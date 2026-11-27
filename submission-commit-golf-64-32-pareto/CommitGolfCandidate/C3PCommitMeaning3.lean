import CommitGolfCandidate.C3PCommitMeaning2

/-! # The paired commit under a fixed oracle: memory of a block and of the leaf phase -/
namespace TwoPermutationPrototype.RV64.C3P
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.RV64.C3Leaves (memoryView_congr addi_mem address_up address_down)
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option autoImplicit false
set_option pp.maxSteps 4000

/-- One pair through passes 1-3: `p1Mem`, the 32-byte draw at `E + 30`, then tags and replies. -/
def pairMem (C : Compression) (P : Sampling.Block → Sampling.Block) (E D : Nat) (a : BitVec 256) (M : Memory) :
    Memory :=
  p3Mem P (writeWindow (p1Mem C M E) (E + 30) (digestWords a)) E D

theorem pair_mem_local (C : Compression) (P : Sampling.Block → Sampling.Block) (E D : Nat) (a : BitVec 256)
    (M M' : Memory) (sep : E + 64 ≤ D) (h : AgreeOn (pairR E D) M M') :
    AgreeOn (pairR E D) (pairMem C P E D a M) (pairMem C P E D a M') := by
  apply p3_mem_local
  intro u hu
  apply write_window_pt
  rcases hu with hm | hd
  · exact p1_mem_local C M M' E (fun v hv => h v (Or.inl hv)) u hm
  · rw [p1_mem_frame _ _ _ _ (by omega), p1_mem_frame _ _ _ _ (by omega)]
    exact h u (Or.inr hd)

theorem pair_mem_frame (C : Compression) (P : Sampling.Block → Sampling.Block) (E D : Nat) (a : BitVec 256)
    (M : Memory) (w : Nat) (h : ¬ pairR E D w) : pairMem C P E D a M w = M w := by
  unfold pairMem
  rw [p3_mem_frame _ _ _ _ _ h]
  unfold pairR msgR at h
  rw [write_window_off _ _ _ _ (by omega), p1_mem_frame _ _ _ _ (by omega)]

theorem prologue_mem (s : MachineState) : (runOpsC s prologueOps).mem = s.mem := by
  simp only [runOpsC, prologueOps, List.foldl, addi_mem]
theorem p2_setup_mem (s : MachineState) : (runOpsC s p2SetupOps).mem = s.mem := by
  simp only [runOpsC, p2SetupOps, List.foldl, addi_mem]
theorem p3_setup_mem (s : MachineState) : (runOpsC s p3SetupOps).mem = s.mem := by
  simp only [runOpsC, p3SetupOps, List.foldl, addi_mem]
theorem epilogue_mem (s : MachineState) : (runOpsC s epilogueOps).mem = s.mem := by
  simp only [runOpsC, epilogueOps, List.foldl, addi_mem]

private theorem bimm256 : signExtend12 (3840 : BitVec 12) = BitVec.ofNat 64 (2 ^ 64 - 8 * 32) := by decide
private theorem bimm272 : signExtend12 (3824 : BitVec 12) = BitVec.ofNat 64 (2 ^ 64 - 8 * 34) := by decide
private theorem bimm256u : signExtend12 (256 : BitVec 12) = BitVec.ofNat 64 (8 * 32) := by decide

theorem block_sep (g : Nat) (hg : g < 8192) : E0 g + 65536 ≤ D0 g := by unfold E0 D0 replyW; omega

/-- **One block under a fixed oracle**: registers as `block_post`, every pair's words are `pairMem` of
the block's starting memory, the rest is unchanged. -/
theorem block_det (oracle : Oracle) (g : Nat) (s : MachineState) (r : BlockRegsP s g) (ws : List (BitVec 256))
    (len : ws.length = 1024) :
    let T := blockDet oracle g s ws
    (T.pc = cpc 45156 ∧ T.getReg .x10 = wordAddress (E0 (g + 1)) ∧ T.getReg .x20 = wordAddress (D0 (g + 1) - 25) ∧
      T.getReg .x5 = 0 ∧ ∀ reg, reg ≠ .x5 → reg ≠ .x10 → reg ≠ .x11 → reg ≠ .x12 → reg ≠ .x13 → reg ≠ .x18 →
        reg ≠ .x20 → T.getReg reg = s.getReg reg) ∧
    (∀ p (hp : p < 1024), ∀ w, pairR (E0 g + 64 * p) (D0 g + 50 * p) w →
      memoryView T w = pairMem oracle.compression (fun x => oracle.permutation x) (E0 g + 64 * p) (D0 g + 50 * p)
        ws[p] (memoryView s) w) ∧
    (∀ w < 2 ^ 33, (∀ p < 1024, ¬ pairR (E0 g + 64 * p) (D0 g + 50 * p) w) → memoryView T w = memoryView s w) := by
  intro T
  have eb := e0_bounds g r.block
  have db := d0_bounds g r.block
  have sep := block_sep g r.block
  obtain ⟨_, inv0, x18, keep0⟩ := block_steps s g r
  have m0 : memoryView (runOpsC s prologueOps) = memoryView s := memoryView_congr (prologue_mem s)
  obtain ⟨inv1, keep1, in1, out1⟩ := pass1_memory oracle.compression (E0 g) _ inv0
  let t1 := pass1Det oracle.compression (E0 g) 1024 0 (runOpsC s prologueOps)
  obtain ⟨q5, q11, q10, qpc, qk⟩ := p2_setup_facts t1
  have t1x18 : t1.getReg .x18 = wordAddress (E0 g) := (keep1 .x18 (by decide) (by decide)).trans x18
  have inv2 : Loop2 (runOpsC t1 p2SetupOps) (E0 g) 0 := by
    refine ⟨?_, ?_, by omega, by omega, q5, q11⟩
    · rw [qpc, inv1.pc, cpc_next, cpc_next, cpc_next]; rfl
    · rw [q10, t1x18, address_down _ 34 3824 bimm272 (by omega) (by norm_num)]; congr 1 <;> omega
  have m2 : memoryView (runOpsC t1 p2SetupOps) = memoryView t1 := memoryView_congr (p2_setup_mem t1)
  obtain ⟨inv2', keep2, in2, out2⟩ := pass2_memory (E0 g) ws len _ inv2
  let t2 := pass2Det (E0 g) ws 0 (runOpsC t1 p2SetupOps)
  obtain ⟨u5, u11, u13, u10, u12, upc, uk⟩ := p3_setup_facts t2
  have t2x18 : t2.getReg .x18 = wordAddress (E0 g) :=
    (keep2 .x18 (by decide)).trans ((qk .x18 (by decide) (by decide) (by decide)).trans t1x18)
  have t2x20 : t2.getReg .x20 = wordAddress (D0 g - 25) :=
    (keep2 .x20 (by decide)).trans ((qk .x20 (by decide) (by decide) (by decide)).trans
      ((keep1 .x20 (by decide) (by decide)).trans ((keep0 .x20 (by decide) (by decide) (by decide) (by decide)
        (by decide)).trans r.reply)))
  have inv3 : Loop3 (runOpsC t2 p3SetupOps) (E0 g) (D0 g) 0 := by
    refine ⟨?_, ?_, ?_, by omega, by omega, by omega, by omega, u5, u11, u13⟩
    · rw [upc, inv2'.pc, cpc_next, cpc_next, cpc_next, cpc_next, cpc_next]; rfl
    · rw [u10, t2x18, address_down _ 32 3840 bimm256 (by omega) (by norm_num)]; congr 1 <;> omega
    · rw [u12, t2x20, show signExtend12 (0 : BitVec 12) = 0#64 by decide, BitVec.add_zero]; congr 1 <;> omega
  have m3 : memoryView (runOpsC t2 p3SetupOps) = memoryView t2 := memoryView_congr (p3_setup_mem t2)
  obtain ⟨inv3', keep3, in3, out3⟩ := pass3_memory (fun x => oracle.permutation x) (E0 g) (D0 g) _ inv3 sep
  let t3 := pass3Det (fun x => oracle.permutation x) (E0 g) (D0 g) 1024 0 (runOpsC t2 p3SetupOps)
  obtain ⟨e20, e10, epc, ek⟩ := epilogue_facts t3
  have mT : memoryView T = memoryView t3 := memoryView_congr (epilogue_mem t3)
  have eT : T = runOpsC t3 epilogueOps := rfl
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [eT, epc, inv3'.pc, cpc_next, cpc_next]; rfl
  · rw [eT, e10, inv3'.source, bimm256u, address_up, eb.2.2]; congr 1 <;> omega
  · rw [eT, e20, inv3'.target, show signExtend12 (0 : BitVec 12) = 0#64 by decide, BitVec.add_zero, db.2.2]
    all_goals (congr 1 <;> omega)
  · rw [eT, ek .x5 (by decide) (by decide)]; exact inv3'.selector
  · intro reg h5 h10 h11 h12 h13 h18 h20
    rw [eT, ek reg h20 h10, keep3 reg h10 h12, uk reg h5 h11 h13 h10 h12, keep2 reg h10, qk reg h5 h11 h10,
      keep1 reg h10 h12, keep0 reg h18 h5 h11 h13 h10]
  · intro p hp w hw
    rw [mT, in3 p hp w hw]
    apply p3_mem_local _ _ _ _ _ _ w hw
    intro u hu
    have ub : u < 2 ^ 33 := by unfold pairR msgR at hu; omega
    rw [m3]
    rcases hu with hm | hd
    · rw [in2 p hp u hm, m2]
      exact write_window_pt _ _ (by rw [in1 p hp u hm, m0])
    · have notmsg : ∀ q < 1024, ¬ msgR (E0 g + 64 * q) u := by intro q hq h; unfold msgR at h; omega
      rw [out2 u ub notmsg, m2, out1 u ub notmsg, m0, write_window_off _ _ _ _ (by omega),
        p1_mem_frame _ _ _ _ (by omega)]
  · intro w wb outside
    have notmsg : ∀ q < 1024, ¬ msgR (E0 g + 64 * q) w := fun q hq h => outside q hq (Or.inl h)
    rw [mT, out3 w wb outside, m3, out2 w wb notmsg, m2, out1 w wb notmsg, m0]

/-! ### A block's memory as one function -/

def blockR (g w : Nat) : Prop := (E0 g ≤ w ∧ w < E0 g + 65536) ∨ (D0 g ≤ w ∧ w < D0 g + 51200)

def blockMem (C : Compression) (P : Sampling.Block → Sampling.Block) (g : Nat) (ws : List (BitVec 256))
    (M : Memory) : Memory := fun w =>
  if E0 g ≤ w ∧ w < E0 g + 65536 then
    pairMem C P (E0 g + 64 * ((w - E0 g) / 64)) (D0 g + 50 * ((w - E0 g) / 64)) (ws[(w - E0 g) / 64]?.getD 0) M w
  else if D0 g ≤ w ∧ w < D0 g + 51200 then
    pairMem C P (E0 g + 64 * ((w - D0 g) / 50)) (D0 g + 50 * ((w - D0 g) / 50)) (ws[(w - D0 g) / 50]?.getD 0) M w
  else M w

theorem block_mem_pair (C : Compression) (P : Sampling.Block → Sampling.Block) (g : Nat) (ws : List (BitVec 256))
    (M : Memory) (p w : Nat) (hg : g < 8192) (hp : p < 1024) (hw : pairR (E0 g + 64 * p) (D0 g + 50 * p) w) :
    blockMem C P g ws M w = pairMem C P (E0 g + 64 * p) (D0 g + 50 * p) (ws[p]?.getD 0) M w := by
  have sep := block_sep g hg
  unfold pairR msgR at hw
  unfold blockMem
  rcases hw with h | h
  · have q : (w - E0 g) / 64 = p := by omega
    rw [if_pos (by omega), q]
  · have q : (w - D0 g) / 50 = p := by omega
    rw [if_neg (by omega), if_pos (by omega), q]

theorem block_pair_of (g w : Nat) (h : blockR g w) :
    ∃ p < 1024, pairR (E0 g + 64 * p) (D0 g + 50 * p) w := by
  unfold blockR at h
  rcases h with h | h
  · exact ⟨(w - E0 g) / 64, by omega, Or.inl ⟨by omega, by omega⟩⟩
  · exact ⟨(w - D0 g) / 50, by omega, Or.inr ⟨by omega, by omega⟩⟩

theorem pair_in_block (g p w : Nat) (hp : p < 1024) (h : pairR (E0 g + 64 * p) (D0 g + 50 * p) w) : blockR g w := by
  unfold pairR msgR at h; unfold blockR; omega

theorem block_mem_local (C : Compression) (P : Sampling.Block → Sampling.Block) (g : Nat) (ws : List (BitVec 256))
    (M M' : Memory) (hg : g < 8192) (h : AgreeOn (blockR g) M M') :
    AgreeOn (blockR g) (blockMem C P g ws M) (blockMem C P g ws M') := by
  intro u hu
  obtain ⟨p, hp, hw⟩ := block_pair_of g u hu
  rw [block_mem_pair C P g ws M p u hg hp hw, block_mem_pair C P g ws M' p u hg hp hw]
  exact pair_mem_local C P _ _ _ M M' (by have := block_sep g hg; omega)
    (fun v hv => h v (pair_in_block g p v hp hv)) u hw

theorem block_mem_frame (C : Compression) (P : Sampling.Block → Sampling.Block) (g : Nat) (ws : List (BitVec 256))
    (M : Memory) (w : Nat) (h : ¬ blockR g w) : blockMem C P g ws M w = M w := by
  unfold blockR at h
  unfold blockMem
  rw [if_neg (by omega), if_neg (by omega)]

theorem block_det_memory (oracle : Oracle) (g : Nat) (s : MachineState) (r : BlockRegsP s g) (ws : List (BitVec 256))
    (len : ws.length = 1024) : ∀ w < 2 ^ 33, memoryView (blockDet oracle g s ws) w =
      blockMem oracle.compression (fun x => oracle.permutation x) g ws (memoryView s) w := by
  intro w wb
  obtain ⟨_, inside, outside⟩ := block_det oracle g s r ws len
  by_cases hw : blockR g w
  · obtain ⟨p, hp, hpw⟩ := block_pair_of g w hw
    rw [block_mem_pair _ _ g ws _ p w r.block hp hpw, inside p hp w hpw, List.getElem?_eq_getElem (by omega),
      Option.getD_some]
  · rw [block_mem_frame _ _ g ws _ w hw]
    exact outside w wb (fun p hp hpw => hw (pair_in_block g p w hp hpw))

/-! ### The leaf phase -/

theorem set_pc_mem_c (t : MachineState) (pc : Word) : (t.setPC pc).mem = t.mem := rfl

theorem fold_b_fold (f : Nat → MachineState → List (BitVec 256) → MachineState) :
    ∀ wss g s, foldB f wss g s = foldG f wss g s := by
  intro wss
  induction wss with
  | nil => intro g s; rfl
  | cons ws wss ih => intro g s; rw [fold_b_cons, ih]; rfl

structure LeafEnd (t : MachineState) (x8 x9 x19 : Word) : Prop where
  pc : t.pc = cpc 45172
  x5 : t.getReg .x5 = 0
  stop : t.getReg .x21 = wordAddress (D0 8192 - 25)
  out : t.getReg .x8 = x8
  heap : t.getReg .x9 = x9
  stride : t.getReg .x19 = x19

def LeafInv (x8 x9 x19 : Word) (g : Nat) (t : MachineState) : Prop :=
  (g < 8192 → LoopRegs t g x8 x9 x19) ∧ (g = 8192 → LeafEnd t x8 x9 x19)

theorem leaf_inv_step (oracle : Oracle) (x8 x9 x19 : Word) (g : Nat) (ws : List (BitVec 256)) (t : MachineState)
    (hg : g < 8192) (len : ws.length = 1024) (inv : LeafInv x8 x9 x19 g t) :
    LeafInv x8 x9 x19 (g + 1) ((blockDet oracle g t ws).setPC (latchPC g)) := by
  have I := inv.1 hg
  obtain ⟨⟨upc, u10, u20, u5, uk⟩, _, _⟩ := block_det oracle g t I.regs ws len
  have k (reg : Reg) (a : reg ≠ .x5) (b : reg ≠ .x10) (c : reg ≠ .x11) (d : reg ≠ .x12) (e : reg ≠ .x13)
      (f : reg ≠ .x18) (h : reg ≠ .x20) : ((blockDet oracle g t ws).setPC (latchPC g)).getReg reg = t.getReg reg := by
    simp only [MachineState.getReg_setPC]; exact uk reg a b c d e f h
  constructor
  · intro next
    have np : latchPC g = cpc blockStart := by unfold latchPC; rw [if_neg (by omega)]
    exact ⟨⟨by rw [np]; rfl, by simpa using u10, by simpa using u20, next⟩,
      (k .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans I.stop,
      (k .x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans I.out,
      (k .x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans I.heap,
      (k .x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans I.stride⟩
  · intro last
    have np : latchPC g = cpc 45172 := by unfold latchPC; rw [if_pos (by omega)]
    exact ⟨by rw [np]; rfl, by simpa using u5,
      (k .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans I.stop,
      (k .x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans I.out,
      (k .x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans I.heap,
      (k .x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans I.stride⟩

/-- **The leaf phase under a fixed oracle**: the end registers, and every block's words are
`blockMem` of the starting memory. -/
theorem leaf_det (oracle : Oracle) (x8 x9 x19 : Word) (wss : List (List (BitVec 256))) (S : MachineState)
    (len : wss.length = 8192) (lens : ∀ ws ∈ wss, ws.length = 1024) (inv : LoopRegs S 0 x8 x9 x19) :
    let L := leafDet oracle wss 0 S
    LeafEnd L x8 x9 x19 ∧
      (∀ g (hg : g < 8192), ∀ w, blockR g w →
        memoryView L w = blockMem oracle.compression (fun x => oracle.permutation x) g wss[g] (memoryView S) w) ∧
      (∀ w < 2 ^ 33, (∀ g < 8192, ¬ blockR g w) → memoryView L w = memoryView S w) := by
  intro L
  have F := fold_memory (fun g s ws => (blockDet oracle g s ws).setPC (latchPC g))
    (fun g ws M => blockMem oracle.compression (fun x => oracle.permutation x) g ws M)
    blockR (LeafInv x8 x9 x19) 8192 (fun ws => ws.length = 1024)
    (fun g ws t hg good i => leaf_inv_step oracle x8 x9 x19 g ws t hg good i)
    (fun g ws t hg good i w wb => by
      rw [show memoryView ((blockDet oracle g t ws).setPC (latchPC g)) = memoryView (blockDet oracle g t ws) from
        memoryView_congr (set_pc_mem_c _ _)]
      exact block_det_memory oracle g t (i.1 hg).regs ws good w wb)
    (fun g ws M M' hg h => block_mem_local _ _ g ws M M' hg h)
    (fun g ws M w _ h => block_mem_frame _ _ g ws M w h)
    (fun g u hg h => by unfold blockR E0 D0 replyW at h; omega)
    (fun g q w hg hq a c => by unfold blockR E0 D0 replyW at a c; omega)
    wss 0 S (by omega) lens ⟨fun _ => inv, fun h => absurd h (by decide)⟩
  simp only [len, Nat.zero_add] at F
  have e : L = foldG (fun g s ws => (blockDet oracle g s ws).setPC (latchPC g)) wss 0 S := fold_b_fold _ wss 0 S
  rw [e]
  exact ⟨F.1.2 rfl, fun g hg w hw => F.2.1 g (by omega) w hw, F.2.2⟩

end TwoPermutationPrototype.RV64.C3P
