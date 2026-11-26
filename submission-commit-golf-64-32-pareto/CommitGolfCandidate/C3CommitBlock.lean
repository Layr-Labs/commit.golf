import CommitGolfCandidate.C3CommitPass3
import CommitGolfCandidate.TwoPermutationProductionLeaf

/-! # The 3c1p commit loop: blocks of 2,048 leaves

Block `g` covers leaves `2048 g .. 2048 g + 2047`. One block costs 32,815 steps and 135,215
cycles plus its latch (2 steps and cycles, 1 for the last block), with 8,192 public calls. The
leaf phase is the jump at word 20 and 8,192 blocks: 268,836,864 steps, 1,107,697,664 cycles,
67,108,864 calls. -/
namespace TwoPermutationPrototype.RV64.C3Leaves
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option autoImplicit false
attribute [local irreducible] execute packedWideCommitImage

def c3HeapBase (g j : Nat) : Nat := leafDest (2048 * g + 128 * ((j + 64) / 128))
def c3SaltBase (g j : Nat) : Nat := leafSalt (2048 * g + 256 * (j / 256))

/-! ### Pass 1 over a block -/

def pass1 (g : Nat) : Nat → Nat → MachineState → OracleComp World MachineState
  | 0, _, s => pure s
  | k + 1, j, s => do
    let mid ← p1Trace s (leafBase (2048 * g + j))
    pass1 g k (j + 1) mid

structure P1Regs (s : MachineState) (g j : Nat) : Prop where
  source : s.getReg .x10 = wordAddress (leafBase (2048 * g + j) - 14)
  size : s.getReg .x11 = 64
  primitive : s.getReg .x13 = 0
  selector : s.getReg .x5 = 0
  pc : s.pc = wordPC (p1Index j)

theorem p1_ready (s : MachineState) (g j : Nat) (bound : g < 8192) (inside : j < 2048) (r : P1Regs s g j) :
    P1Ready s (leafBase (2048 * g + j)) :=
  ⟨r.source, by unfold leafBase; omega, by unfold leafBase; omega, r.selector, r.size, r.primitive⟩

theorem p1_trace_post (s : MachineState) (g j : Nat) (bound : g < 8192) (inside : j < 2048) (r : P1Regs s g j)
    {next : MachineState} (hit : next ∈ support (p1Trace s (leafBase (2048 * g + j)))) :
    P1Regs next g (j + 1) ∧ ∀ reg, reg ≠ .x10 → reg ≠ .x12 → next.getReg reg = s.getReg reg := by
  simp only [p1Trace, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hit
  obtain ⟨t1, _, t2, _, t3, _, rfl⟩ := hit
  have ready := p1_ready s g j bound inside r
  have regs := p1d_regs s _ ready t1 t2 t3
  have keep := p1d_keeps s (leafBase (2048 * g + j)) t1 t2 t3
  refine ⟨⟨?_, (keep .x11 (by decide) (by decide)).trans r.size, (keep .x13 (by decide) (by decide)).trans r.primitive,
    (keep .x5 (by decide) (by decide)).trans r.selector, ?_⟩, keep⟩
  · rw [regs.1]; first | rfl | (congr 1; unfold leafBase; omega)
  · rw [regs.2.2, r.pc, show (32 : Nat) = 4 * 8 by rfl, word_pc_add]; first | rfl | (congr 1; unfold p1Index; omega)

theorem pass1_run (s : MachineState) (g cnt j fuel : Nat) (bound : g < 8192) (inside : j + cnt ≤ 2048)
    (r : P1Regs s g j) :
    execute packedWideCommitImage (8 * cnt + fuel) s true =
      (do let next ← pass1 g cnt j s
          let result ← execute packedWideCommitImage fuel next true
          return result.charge (29 * cnt) (3 * cnt)) := by
  induction cnt generalizing s j with
  | zero => simp [pass1, Execution.charge]
  | succ k ih =>
    rw [show 8 * (k + 1) + fuel = 8 + (8 * k + fuel) by omega,
      execute_p1_leaf s j (by omega) _ (p1_ready s g j bound (by omega) r) r.pc]
    simp only [pass1, bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro mid reached
    rw [ih mid (j + 1) (by omega) (p1_trace_post s g j bound (by omega) r reached).1]
    simp [Execution.charge, Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem pass1_post (s : MachineState) (g cnt j : Nat) (bound : g < 8192) (inside : j + cnt ≤ 2048)
    (r : P1Regs s g j) {next : MachineState} (hit : next ∈ support (pass1 g cnt j s)) :
    P1Regs next g (j + cnt) ∧ ∀ reg, reg ≠ .x10 → reg ≠ .x12 → next.getReg reg = s.getReg reg := by
  induction cnt generalizing s j with
  | zero =>
    simp only [pass1, support_pure, Set.mem_singleton_iff] at hit
    subst hit
    exact ⟨r, fun _ _ _ => rfl⟩
  | succ k ih =>
    simp only [pass1, mem_support_bind_iff] at hit
    obtain ⟨mid, step, reach⟩ := hit
    have first := p1_trace_post s g j bound (by omega) r step
    have rest := ih mid (j + 1) (by omega) first.1 reach
    rw [show j + (k + 1) = j + 1 + k by omega]
    exact ⟨rest.1, fun reg a b => (rest.2 reg a b).trans (first.2 reg a b)⟩

/-! ### Pass 3 over a block, with the window rebases -/

def heapUpdate3 (s : MachineState) := (s.setReg .x20 (s.getReg .x20 + s.getReg .x7)).setPC (s.pc + 4)
def nonceUpdate3 (s : MachineState) := (s.setReg .x22 (s.getReg .x22 + s.getReg .x7)).setPC (s.pc + 4)

def rebased3 (s : MachineState) (j : Nat) : MachineState :=
  let h := if j % 128 = 63 then heapUpdate3 s else s
  if j % 256 = 255 then nonceUpdate3 h else h

def extra3 (j : Nat) : Nat := (if j % 128 = 63 then 1 else 0) + (if j % 256 = 255 then 1 else 0)

def p3Unit (g j : Nat) (s : MachineState) : OracleComp World MachineState := do
  let raw ← p3Trace s j (leafBase (2048 * g + j)) (leafDest (2048 * g + j))
  return rebased3 raw j

def pass3 (g : Nat) : Nat → Nat → MachineState → OracleComp World MachineState
  | 0, _, s => pure s
  | k + 1, j, s => do
    let mid ← p3Unit g j s
    pass3 g k (j + 1) mid

structure P3Regs (s : MachineState) (g j : Nat) : Prop where
  source : s.getReg .x10 = wordAddress (leafBase (2048 * g + j))
  heap : s.getReg .x20 = wordAddress (c3HeapBase g j)
  salts : s.getReg .x22 = wordAddress (c3SaltBase g j + 256)
  stride : s.getReg .x7 = 4096
  selector : s.getReg .x5 = 0
  size : s.getReg .x11 = 200
  primitive : s.getReg .x13 = 1
  pc : s.pc = wordPC (p3Index j)

theorem p3_ready (s : MachineState) (g j : Nat) (bound : g < 8192) (inside : j < 2048) (r : P3Regs s g j) :
    P3Ready s j (leafBase (2048 * g + j)) (leafDest (2048 * g + j)) (c3SaltBase g j) := by
  refine ⟨r.source, ?_, r.salts, ?_, ?_, ?_, ?_, r.selector, r.size, r.primitive⟩
  · rw [r.heap]
    have he : 8 * c3HeapBase g j + 32 * ((j + 64) % 128) =
        8 * leafDest (2048*g+j) + 2048 := by unfold c3HeapBase leafDest; omega
    have hw := congrArg (BitVec.ofNat 64) he
    simp only [BitVec.ofNat_add] at hw
    change BitVec.ofNat 64 (8 * c3HeapBase g j) + (_ - 2048) = _
    rw [show ∀ x y : Word, x + (y - 2048) = (x+y)-2048 by
      intro x y; simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc], hw]
    exact BitVec.add_sub_cancel _ (2048#64)
  all_goals simp only [leafBase, leafDest, c3SaltBase, leafSalt] <;> omega

theorem salt_word_of_block (g j : Nat) : saltWordOf (c3SaltBase g j) j = leafSalt (2048 * g + j) := by
  unfold saltWordOf c3SaltBase leafSalt; omega

theorem heap_at3 (s : MachineState) (j : Nat) (hj : j < 2048) (here : s.pc = wordPC (p3Index j + 8))
    (h : j % 128 = 63) (fuel : Nat) :
    execute packedWideCommitImage (1 + fuel) s true =
      (do let out ← execute packedWideCommitImage fuel (heapUpdate3 s) true
          return out.charge 1 0) := by
  rw [Nat.add_comm 1 fuel, CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _
    (fetch_heap_rebase j hj h s here) (show ordinaryStep s _ = some (heapUpdate3 s) by rfl)]
  rfl

theorem nonce_at3 (s : MachineState) (j : Nat) (hj : j < 2048) (here : s.pc = wordPC (p3Index j + 8))
    (h : j % 256 = 255) (fuel : Nat) :
    execute packedWideCommitImage (1 + fuel) s true =
      (do let out ← execute packedWideCommitImage fuel (nonceUpdate3 s) true
          return out.charge 1 0) := by
  rw [Nat.add_comm 1 fuel, CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _
    (fetch_nonce_rebase j hj h s here) (show ordinaryStep s _ = some (nonceUpdate3 s) by rfl)]
  rfl

theorem rebase3_run (s : MachineState) (j : Nat) (hj : j < 2048) (here : s.pc = wordPC (p3Index j + 8))
    (fuel : Nat) :
    execute packedWideCommitImage (extra3 j + fuel) s true =
      (do let out ← execute packedWideCommitImage fuel (rebased3 s j) true
          return out.charge (extra3 j) 0) := by
  by_cases h : j % 128 = 63
  · have n : j % 256 ≠ 255 := by omega
    simpa [extra3, rebased3, h, n] using heap_at3 s j hj here h fuel
  · by_cases n : j % 256 = 255
    · simpa [extra3, rebased3, h, n] using nonce_at3 s j hj here n fuel
    · simp [extra3, rebased3, h, n, Execution.charge]

theorem p3_unit_post (s : MachineState) (g j : Nat) (bound : g < 8192) (inside : j < 2048) (r : P3Regs s g j)
    {next : MachineState} (hit : next ∈ support (p3Unit g j s)) :
    P3Regs next g (j + 1) ∧ ∀ reg, reg ≠ .x10 → reg ≠ .x12 → reg ≠ .x31 → reg ≠ .x20 → reg ≠ .x22 →
      next.getReg reg = s.getReg reg := by
  simp only [p3Unit, p3Trace, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hit
  obtain ⟨raw, ⟨y, _, rfl⟩, rfl⟩ := hit
  have ready := p3_ready s g j bound inside r
  obtain ⟨f10, f12, fkeep, fpc⟩ := p3_final_regs s j _ _ _ ready y
  let f := p3Final s j (leafDest (2048 * g + j)) y
  have keepR (reg : Reg) (a : reg ≠ .x20) (b : reg ≠ .x22) : (rebased3 f j).getReg reg = f.getReg reg := by
    unfold rebased3 heapUpdate3 nonceUpdate3
    split <;> split <;> simp only [MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm a),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm b)]
  have pcR : (rebased3 f j).pc = wordPC (p3Index (j + 1)) := by
    have base : f.pc = wordPC (p3Index j + 8) := by
      rw [fpc, r.pc, show (32 : Nat) = 4 * 8 by rfl, word_pc_add]
    unfold rebased3 heapUpdate3 nonceUpdate3
    by_cases h : j % 128 = 63 <;> by_cases n : j % 256 = 255
    · omega
    · simp only [h,n,if_true,if_false,MachineState.setPC,MachineState.setReg]
      change f.pc + 4 = _
      rw [base, show (4 : Word) = BitVec.ofNat 64 (4 * 1) by rfl, word_pc_add]
      congr 1; unfold p3Index; omega
    · simp only [h,n,if_true,if_false,MachineState.setPC,MachineState.setReg]
      change f.pc + 4 = _
      rw [base, show (4 : Word) = BitVec.ofNat 64 (4 * 1) by rfl, word_pc_add]
      congr 1; unfold p3Index; omega
    · simp only [h,n,if_false]; rw [base]; congr 1; unfold p3Index; omega
  have heapF : f.getReg .x20 = wordAddress (c3HeapBase g j) := (fkeep .x20 (by decide) (by decide) (by decide)).trans r.heap
  have saltF : f.getReg .x22 = wordAddress (c3SaltBase g j + 256) := (fkeep .x22 (by decide) (by decide) (by decide)).trans r.salts
  have strideF : f.getReg .x7 = 4096 := (fkeep .x7 (by decide) (by decide) (by decide)).trans r.stride
  have heapR : (rebased3 f j).getReg .x20 = wordAddress (c3HeapBase g (j + 1)) := by
    by_cases h : j % 128 = 63
    · have n : j % 256 ≠ 255 := by omega
      simp only [rebased3,h,n,if_true,if_false]
      change f.getReg .x20 + f.getReg .x7 = _
      rw [heapF,strideF]
      change wordAddress _ + wordAddress 512 = _
      rw [← wordAddress_add]; congr 1; unfold c3HeapBase leafDest; omega
    · have kept : (rebased3 f j).getReg .x20 = f.getReg .x20 := by
        by_cases n : j % 256 = 255 <;> simp [rebased3,h,n,nonceUpdate3,MachineState.getReg_setPC,MachineState.getReg_setReg_ne]
      rw [kept, heapF]
      congr 1; unfold c3HeapBase; rw [show (j + 1 + 64) / 128 = (j + 64) / 128 by omega]
  have saltR : (rebased3 f j).getReg .x22 = wordAddress (c3SaltBase g (j + 1) + 256) := by
    by_cases n : j % 256 = 255
    · have h : j % 128 ≠ 63 := by omega
      simp only [rebased3,h,n,if_true,if_false]
      change f.getReg .x22 + f.getReg .x7 = _
      rw [saltF,strideF]
      change wordAddress _ + wordAddress 512 = _
      rw [← wordAddress_add]; congr 1; unfold c3SaltBase leafSalt; omega
    · have kept : (rebased3 f j).getReg .x22 = f.getReg .x22 := by
        by_cases h : j % 128 = 63 <;> simp [rebased3,n,h,heapUpdate3,MachineState.getReg_setPC,MachineState.getReg_setReg_ne]
      rw [kept,saltF]
      congr 1; unfold c3SaltBase; rw [show (j + 1) / 256 = j / 256 by omega]
  refine ⟨⟨?_, heapR, saltR, ?_, ?_, ?_, ?_, pcR⟩, ?_⟩
  · rw [keepR _ (by decide) (by decide), f10]; first | rfl | (congr 1; unfold leafBase; omega)
  · rw [keepR _ (by decide) (by decide), fkeep .x7 (by decide) (by decide) (by decide), r.stride]
  · rw [keepR _ (by decide) (by decide), fkeep .x5 (by decide) (by decide) (by decide), r.selector]
  · rw [keepR _ (by decide) (by decide), fkeep .x11 (by decide) (by decide) (by decide), r.size]
  · rw [keepR _ (by decide) (by decide), fkeep .x13 (by decide) (by decide) (by decide), r.primitive]
  · intro reg a b c d e
    rw [keepR reg d e, fkeep reg a b c]

theorem p3_unit_run (s : MachineState) (g j fuel : Nat) (bound : g < 8192) (inside : j < 2048)
    (r : P3Regs s g j) :
    execute packedWideCommitImage (8 + extra3 j + fuel) s true =
      (do let next ← p3Unit g j s
          let result ← execute packedWideCommitImage fuel next true
          return result.charge (37 + extra3 j) 1) := by
  have ready := p3_ready s g j bound inside r
  rw [show 8 + extra3 j + fuel = 8 + (extra3 j + fuel) by omega, execute_p3_leaf s j inside _ _ _ ready r.pc]
  simp only [p3Unit, bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro raw reached
  have rawPC : raw.pc = wordPC (p3Index j + 8) := by
    simp only [p3Trace, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reached
    obtain ⟨y, _, rfl⟩ := reached
    rw [(p3_final_regs s j _ _ _ ready y).2.2.2, r.pc, show (32 : Nat) = 4 * 8 by rfl, word_pc_add]
  rw [rebase3_run raw j inside rawPC fuel]
  simp [Execution.charge]
  congr 1
  funext a
  congr 1 <;> omega

def progress3 (j : Nat) : Nat := (j + 64) / 128 + j / 256

theorem extra3_count (j : Nat) : progress3 (j + 1) = progress3 j + extra3 j := by
  unfold progress3 extra3
  split <;> split <;> omega

def span3 (j cnt : Nat) : Nat := progress3 (j + cnt) - progress3 j

theorem span3_step (j k : Nat) : span3 j (k + 1) = extra3 j + span3 (j + 1) k := by
  have mono (a b : Nat) (h : a ≤ b) : progress3 a ≤ progress3 b := by
    unfold progress3
    have := Nat.div_le_div_right (c := 128) (show a + 64 ≤ b + 64 by omega)
    have := Nat.div_le_div_right (c := 256) h
    omega
  have stepCount := extra3_count j
  have tailMono := mono (j + 1) (j + 1 + k) (by omega)
  unfold span3
  rw [show j + (k + 1) = j + 1 + k by omega]
  omega

theorem pass3_run (s : MachineState) (g cnt j fuel : Nat) (bound : g < 8192) (inside : j + cnt ≤ 2048)
    (r : P3Regs s g j) :
    execute packedWideCommitImage (8 * cnt + span3 j cnt + fuel) s true =
      (do let next ← pass3 g cnt j s
          let result ← execute packedWideCommitImage fuel next true
          return result.charge (37 * cnt + span3 j cnt) cnt) := by
  induction cnt generalizing s j with
  | zero => simp [pass3, span3, Execution.charge]
  | succ k ih =>
    rw [span3_step, show 8 * (k + 1) + (extra3 j + span3 (j + 1) k) + fuel =
        8 + extra3 j + (8 * k + span3 (j + 1) k + fuel) by omega,
      p3_unit_run s g j _ bound (by omega) r]
    simp only [pass3, bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro mid reached
    rw [ih mid (j + 1) (by omega) (p3_unit_post s g j bound (by omega) r reached).1]
    simp [Execution.charge, Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem pass3_post (s : MachineState) (g cnt j : Nat) (bound : g < 8192) (inside : j + cnt ≤ 2048)
    (r : P3Regs s g j) {next : MachineState} (hit : next ∈ support (pass3 g cnt j s)) :
    P3Regs next g (j + cnt) ∧ ∀ reg, reg ≠ .x10 → reg ≠ .x12 → reg ≠ .x31 → reg ≠ .x20 → reg ≠ .x22 →
      next.getReg reg = s.getReg reg := by
  induction cnt generalizing s j with
  | zero =>
    simp only [pass3, support_pure, Set.mem_singleton_iff] at hit
    subst hit
    exact ⟨r, fun _ _ _ _ _ _ => rfl⟩
  | succ k ih =>
    simp only [pass3, mem_support_bind_iff] at hit
    obtain ⟨mid, step, reach⟩ := hit
    have first := p3_unit_post s g j bound (by omega) r step
    have rest := ih mid (j + 1) (by omega) first.1 reach
    rw [show j + (k + 1) = j + 1 + k by omega]
    exact ⟨rest.1, fun reg a b c d e => (rest.2 reg a b c d e).trans (first.2 reg a b c d e)⟩

end TwoPermutationPrototype.RV64.C3Leaves
