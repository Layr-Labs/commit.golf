import CommitGolfCandidate.C3CommitBlock
import CommitGolfCandidate.TwoPermutationPackedCommit

/-! # The 3c1p commit loop as a `PackedLeafExecution`

A block: entry (`addi s2,a0,0 ; addi a1,zero,64 ; addi a3,zero,0 ; addi a0,a0,-112`), pass 1,
switch (`addi a1,zero,200 ; addi a3,zero,1 ; addi a0,s2,0`), pass 3, latch
(`beq s4,s5,<45172> ; jal zero,<12341>`). The leaf phase is `jal zero,<12341>` and 8,192 blocks. -/
namespace TwoPermutationPrototype.RV64.C3Leaves
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option autoImplicit false
attribute [local irreducible] execute packedWideCommitImage

def entryState (s : MachineState) : MachineState :=
  execInstrBr (execInstrBr (execInstrBr (execInstrBr s (.ADDI .x18 .x10 0)) (.ADDI .x11 .x0 64))
    (.ADDI .x13 .x0 0)) (.ADDI .x10 .x10 3984)

def switchState (s : MachineState) : MachineState :=
  execInstrBr (execInstrBr (execInstrBr s (.ADDI .x11 .x0 200)) (.ADDI .x13 .x0 1)) (.ADDI .x10 .x18 0)

structure BlockRegs (s : MachineState) (g : Nat) : Prop where
  source : s.getReg .x10 = wordAddress (leafBase (2048 * g))
  heap : s.getReg .x20 = wordAddress (c3HeapBase g 0)
  salts : s.getReg .x22 = wordAddress (c3SaltBase g 0 + 256)
  stride : s.getReg .x7 = 4096
  selector : s.getReg .x5 = 0
  pc : s.pc = wordPC blockStart

private theorem imm3984 : signExtend12 (3984 : BitVec 12) = BitVec.ofNat 64 (2 ^ 64 - 8 * 14) := by decide

theorem entry_facts (s : MachineState) (g : Nat) (bound : g < 8192) (r : BlockRegs s g) :
    P1Regs (entryState s) g 0 ∧ (entryState s).getReg .x18 = wordAddress (leafBase (2048 * g)) ∧
      (∀ reg, reg ≠ .x18 → reg ≠ .x11 → reg ≠ .x13 → reg ≠ .x10 → (entryState s).getReg reg = s.getReg reg) ∧
      (entryState s).mem = s.mem := by
  let e1 := execInstrBr s (.ADDI .x18 .x10 0)
  let e2 := execInstrBr e1 (.ADDI .x11 .x0 64)
  let e3 := execInstrBr e2 (.ADDI .x13 .x0 0)
  have h18 : e1.getReg .x18 = wordAddress (leafBase (2048 * g)) := by
    rw [addi_from _ _ _ _ (by decide), r.source, show signExtend12 (0 : BitVec 12) = BitVec.ofNat 64 (8 * 0) by decide,
      address_up]
    rfl
  have keep (reg : Reg) (a : reg ≠ .x18) (b : reg ≠ .x11) (c : reg ≠ .x13) (d : reg ≠ .x10) :
      (entryState s).getReg reg = s.getReg reg := by
    rw [entryState, addi_other _ _ _ _ _ d, addi_other _ _ _ _ _ c, addi_other _ _ _ _ _ b, addi_other _ _ _ _ _ a]
  have x10 : (entryState s).getReg .x10 = wordAddress (leafBase (2048 * g) - 14) := by
    rw [entryState, addi_self _ _ _ (by decide), addi_other _ _ _ _ _ (by decide), addi_other _ _ _ _ _ (by decide),
      addi_other _ _ _ _ _ (by decide), r.source,
      address_down _ 14 3984 imm3984 (by unfold leafBase; omega) (by norm_num)]
  refine ⟨⟨x10, ?_, ?_, (keep .x5 (by decide) (by decide) (by decide) (by decide)).trans r.selector, ?_⟩, ?_, keep, ?_⟩
  · rw [entryState, addi_other _ _ _ _ _ (by decide), addi_other _ _ _ _ _ (by decide), addi_from _ _ _ _ (by decide)]
    rfl
  · rw [entryState, addi_other _ _ _ _ _ (by decide), addi_from _ _ _ _ (by decide)]
    rfl
  · rw [entryState, addi_pc, addi_pc, addi_pc, addi_pc, r.pc]
    simp only [BitVec.add_assoc]
    rw [show (4 : Word) + (4 + (4 + 4)) = BitVec.ofNat 64 (4 * 4) by rfl, word_pc_add]
    rfl
  · rw [entryState, addi_other _ _ _ _ _ (by decide), addi_other _ _ _ _ _ (by decide),
      addi_other _ _ _ _ _ (by decide), h18]
  · rw [entryState, addi_mem, addi_mem, addi_mem, addi_mem]

theorem switch_facts (s : MachineState) (g : Nat) (block : s.getReg .x18 = wordAddress (leafBase (2048 * g)))
    (pc : s.pc = wordPC switchIndex) :
    (switchState s).getReg .x10 = wordAddress (leafBase (2048 * g)) ∧ (switchState s).getReg .x11 = 200 ∧
      (switchState s).getReg .x13 = 1 ∧
      (∀ reg, reg ≠ .x11 → reg ≠ .x13 → reg ≠ .x10 → (switchState s).getReg reg = s.getReg reg) ∧
      (switchState s).pc = wordPC (p3Index 0) ∧ (switchState s).mem = s.mem := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [switchState, addi_from _ _ _ _ (by decide), addi_other _ _ _ _ _ (by decide), addi_other _ _ _ _ _ (by decide),
      block, show signExtend12 (0 : BitVec 12) = BitVec.ofNat 64 (8 * 0) by decide, address_up]
    rfl
  · rw [switchState, addi_other _ _ _ _ _ (by decide), addi_other _ _ _ _ _ (by decide), addi_from _ _ _ _ (by decide)]
    rfl
  · rw [switchState, addi_other _ _ _ _ _ (by decide), addi_from _ _ _ _ (by decide)]
    rfl
  · intro reg a b c
    rw [switchState, addi_other _ _ _ _ _ c, addi_other _ _ _ _ _ b, addi_other _ _ _ _ _ a]
  · rw [switchState, addi_pc, addi_pc, addi_pc, pc]
    simp only [BitVec.add_assoc]
    rw [show (4 : Word) + (4 + 4) = BitVec.ofNat 64 (4 * 3) by rfl, word_pc_add]
    rfl
  · rw [switchState, addi_mem, addi_mem, addi_mem]

theorem entry_run (s : MachineState) (g fuel : Nat) (bound : g < 8192) (r : BlockRegs s g) :
    execute packedWideCommitImage (4 + fuel) s true =
      (do let out ← execute packedWideCommitImage fuel (entryState s) true; return out.charge 4 0) := by
  apply CommitGolfCandidate.execute_unit_steps (states := fun i =>
    if i = 0 then s else if i = 1 then execInstrBr s (.ADDI .x18 .x10 0)
    else if i = 2 then execInstrBr (execInstrBr s (.ADDI .x18 .x10 0)) (.ADDI .x11 .x0 64)
    else if i = 3 then execInstrBr (execInstrBr (execInstrBr s (.ADDI .x18 .x10 0)) (.ADDI .x11 .x0 64))
      (.ADDI .x13 .x0 0)
    else entryState s)
  intro i hi
  have pcs : ∀ k < 4, (if k = 0 then s else if k = 1 then execInstrBr s (.ADDI .x18 .x10 0)
      else if k = 2 then execInstrBr (execInstrBr s (.ADDI .x18 .x10 0)) (.ADDI .x11 .x0 64)
      else if k = 3 then execInstrBr (execInstrBr (execInstrBr s (.ADDI .x18 .x10 0)) (.ADDI .x11 .x0 64))
        (.ADDI .x13 .x0 0)
      else entryState s).pc = wordPC (blockStart + k) := by
    intro k hk
    interval_cases k
    · simpa using r.pc
    · simp only [show (1 : Nat) ≠ 0 by decide, ite_false, ite_true, addi_pc, r.pc]
      rw [show (4 : Word) = BitVec.ofNat 64 (4 * 1) by rfl, word_pc_add]
    · simp only [show (2 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 1 by decide, ite_false, ite_true, addi_pc, r.pc,
        BitVec.add_assoc]
      rw [show (4 : Word) + 4 = BitVec.ofNat 64 (4 * 2) by rfl, word_pc_add]
    · simp only [show (3 : Nat) ≠ 0 by decide, show (3 : Nat) ≠ 1 by decide, show (3 : Nat) ≠ 2 by decide,
        ite_false, ite_true, addi_pc, r.pc, BitVec.add_assoc]
      rw [show (4 : Word) + (4 + 4) = BitVec.ofNat 64 (4 * 3) by rfl, word_pc_add]
  refine ⟨.base (opAt entryOps i), fetch_entry i hi _ (pcs i hi), ?_, ?_⟩
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem switch_run (s : MachineState) (pc : s.pc = wordPC switchIndex) (fuel : Nat) :
    execute packedWideCommitImage (3 + fuel) s true =
      (do let out ← execute packedWideCommitImage fuel (switchState s) true; return out.charge 3 0) := by
  apply CommitGolfCandidate.execute_unit_steps (states := fun i =>
    if i = 0 then s else if i = 1 then execInstrBr s (.ADDI .x11 .x0 200)
    else if i = 2 then execInstrBr (execInstrBr s (.ADDI .x11 .x0 200)) (.ADDI .x13 .x0 1)
    else switchState s)
  intro i hi
  have pcs : ∀ k < 3, (if k = 0 then s else if k = 1 then execInstrBr s (.ADDI .x11 .x0 200)
      else if k = 2 then execInstrBr (execInstrBr s (.ADDI .x11 .x0 200)) (.ADDI .x13 .x0 1)
      else switchState s).pc = wordPC (switchIndex + k) := by
    intro k hk
    interval_cases k
    · simpa using pc
    · simp only [show (1 : Nat) ≠ 0 by decide, ite_false, ite_true, addi_pc, pc]
      rw [show (4 : Word) = BitVec.ofNat 64 (4 * 1) by rfl, word_pc_add]
    · simp only [show (2 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 1 by decide, ite_false, ite_true, addi_pc, pc,
        BitVec.add_assoc]
      rw [show (4 : Word) + 4 = BitVec.ofNat 64 (4 * 2) by rfl, word_pc_add]
  refine ⟨.base (opAt switchOps i), fetch_switch i hi _ (pcs i hi), ?_, ?_⟩
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

/-! ### The latch -/

def c3LatchPC (g : Nat) : Word := if g + 1 = 8192 then 184784 else wordPC blockStart
def c3LatchCost (g : Nat) : Nat := if g + 1 = 8192 then 1 else 2

theorem c3_latch_run (s : MachineState) (g fuel : Nat) (bound : g < 8192)
    (heap : s.getReg .x20 = wordAddress (c3HeapBase g 2048)) (here : s.pc = 184720)
    (stop : s.getReg .x21 = wordAddress (leafDest (2 ^ 24))) :
    execute packedWideCommitImage (c3LatchCost g + fuel) s true =
      (do let y ← execute packedWideCommitImage fuel (s.setPC (c3LatchPC g)) true
          return y.charge (c3LatchCost g) 0) := by
  have eq : s.getReg .x20 = s.getReg .x21 ↔ g + 1 = 8192 := by
    rw [heap, stop]
    constructor
    · intro h
      have j := wordAddress_injective_of_bound (a := c3HeapBase g 2048) (b := leafDest (2 ^ 24))
        (by unfold c3HeapBase leafDest; omega) (by decide) h
      unfold c3HeapBase leafDest at j; omega
    · intro h
      apply congrArg wordAddress
      unfold c3HeapBase leafDest
      omega
  by_cases last : g + 1 = 8192
  · have step : ordinaryStep s (.base (.BEQ .x20 .x21 64)) = some (s.setPC 184784) := by
      simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, here, eq.mpr last, signExtend13]
    rw [c3LatchCost, if_pos last, c3LatchPC, if_pos last, Nat.add_comm 1 fuel,
      CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (packed_wide_fetch_leaf_branch s here) step]
    rfl
  · let middle := s.setPC 184724
    have diff : s.getReg .x20 ≠ s.getReg .x21 := fun h => last (eq.mp h)
    have step : ordinaryStep s (.base (.BEQ .x20 .x21 64)) = some middle := by
      simp [middle, ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, here, diff]
    have jump : ordinaryStep middle (.base (.JAL .x0 1965888)) = some (s.setPC (wordPC blockStart)) := by
      simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, middle, MachineState.setReg,
        MachineState.setPC]
      rfl
    rw [c3LatchCost, if_neg last, c3LatchPC, if_neg last, show 2 + fuel = (fuel + 1) + 1 by omega,
      CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (packed_wide_fetch_leaf_branch s here) step,
      CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (fetch_loop_jump middle rfl) jump]
    simp [instructionCycles, Execution.charge, ← Nat.add_assoc]

/-! ### One block -/

def blockTrace (g : Nat) (s : MachineState) : OracleComp World MachineState := do
  let p1 ← pass1 g 2048 0 (entryState s)
  let p3 ← pass3 g 2048 0 (switchState p1)
  return p3.setPC (c3LatchPC g)

def SavedC3 (reg : Reg) : Prop := reg ∈ [Reg.x5, .x7, .x8, .x9, .x19, .x21]

theorem saved_ne (reg : Reg) (h : SavedC3 reg) :
    reg ≠ .x10 ∧ reg ≠ .x11 ∧ reg ≠ .x12 ∧ reg ≠ .x13 ∧ reg ≠ .x18 ∧ reg ≠ .x20 ∧ reg ≠ .x22 ∧ reg ≠ .x31 := by
  simp only [SavedC3, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem block_inner (s : MachineState) (g : Nat) (bound : g < 8192) (r : BlockRegs s g)
    {p1 : MachineState} (h1 : p1 ∈ support (pass1 g 2048 0 (entryState s))) :
    P3Regs (switchState p1) g 0 ∧
      ∀ reg, SavedC3 reg → (switchState p1).getReg reg = s.getReg reg := by
  obtain ⟨e1, e18, ekeep, _⟩ := entry_facts s g bound r
  obtain ⟨q1, qkeep⟩ := pass1_post _ g 2048 0 bound (by decide) e1 h1
  have q18 : p1.getReg .x18 = wordAddress (leafBase (2048 * g)) := (qkeep .x18 (by decide) (by decide)).trans e18
  have qpc : p1.pc = wordPC switchIndex := by rw [q1.pc]; rfl
  obtain ⟨s10, s11, s13, skeep, spc, _⟩ := switch_facts p1 g q18 qpc
  have through (reg : Reg) (a : reg ≠ .x18) (b : reg ≠ .x11) (c : reg ≠ .x13) (d : reg ≠ .x10) (e : reg ≠ .x12) :
      (switchState p1).getReg reg = s.getReg reg :=
    (skeep reg b c d).trans ((qkeep reg d e).trans (ekeep reg a b c d))
  refine ⟨⟨by simpa using s10, ?_, ?_, ?_, ?_, s11, s13, spc⟩, ?_⟩
  · rw [through .x20 (by decide) (by decide) (by decide) (by decide) (by decide), r.heap]
  · rw [through .x22 (by decide) (by decide) (by decide) (by decide) (by decide), r.salts]
  · rw [through .x7 (by decide) (by decide) (by decide) (by decide) (by decide), r.stride]
  · rw [through .x5 (by decide) (by decide) (by decide) (by decide) (by decide), r.selector]
  · intro reg saved
    obtain ⟨a, b, c, d, e, _, _, _⟩ := saved_ne reg saved
    exact through reg e b d a c

theorem block_run (s : MachineState) (g fuel : Nat) (bound : g < 8192) (r : BlockRegs s g)
    (stop : s.getReg .x21 = wordAddress (leafDest (2 ^ 24))) :
    execute packedWideCommitImage (32815 + c3LatchCost g + fuel) s true =
      (do let next ← blockTrace g s
          let result ← execute packedWideCommitImage fuel next true
          return result.charge (135215 + c3LatchCost g) 8192) := by
  obtain ⟨e1, _, _, _⟩ := entry_facts s g bound r
  have spanAll : span3 0 2048 = 40 := by decide
  rw [show 32815 + c3LatchCost g + fuel = 4 + (8 * 2048 + (3 + (8 * 2048 + span3 0 2048 + (c3LatchCost g + fuel))))
      by rw [spanAll]; omega,
    entry_run s g _ bound r, pass1_run _ g 2048 0 _ bound (by decide) e1]
  simp only [blockTrace, bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro p1 h1
  have inner := block_inner s g bound r h1
  obtain ⟨q1, _⟩ := pass1_post _ g 2048 0 bound (by decide) e1 h1
  rw [switch_run p1 (by rw [q1.pc]; rfl), pass3_run _ g 2048 0 _ bound (by decide) inner.1]
  simp only [bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro p3 h3
  obtain ⟨q3, qkeep3⟩ := pass3_post _ g 2048 0 bound (by decide) inner.1 h3
  have stop3 : p3.getReg .x21 = wordAddress (leafDest (2 ^ 24)) := by
    rw [qkeep3 .x21 (by decide) (by decide) (by decide) (by decide) (by decide),
      inner.2 .x21 (by simp [SavedC3]), stop]
  rw [c3_latch_run p3 g fuel bound q3.heap (by rw [q3.pc]; rfl) stop3]
  simp [Execution.charge, spanAll]
  congr 1
  funext a
  congr 1 <;> omega

theorem block_post (s : MachineState) (g : Nat) (bound : g < 8192) (r : BlockRegs s g)
    {next : MachineState} (hit : next ∈ support (blockTrace g s)) :
    (g + 1 < 8192 → BlockRegs next (g + 1)) ∧ next.pc = c3LatchPC g ∧
      ∀ reg, SavedC3 reg → next.getReg reg = s.getReg reg := by
  simp only [blockTrace, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hit
  obtain ⟨p1, h1, p3, h3, rfl⟩ := hit
  have inner := block_inner s g bound r h1
  obtain ⟨q3, qkeep3⟩ := pass3_post _ g 2048 0 bound (by decide) inner.1 h3
  have keep (reg : Reg) (saved : SavedC3 reg) : (p3.setPC (c3LatchPC g)).getReg reg = s.getReg reg := by
    obtain ⟨a, _, c, _, _, f, h, k⟩ := saved_ne reg saved
    rw [MachineState.getReg_setPC, qkeep3 reg a c k f h, inner.2 reg saved]
  refine ⟨fun more => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, rfl, keep⟩
  · rw [MachineState.getReg_setPC, q3.source]; exact congrArg wordAddress (by unfold leafBase; omega)
  · rw [MachineState.getReg_setPC, q3.heap]; exact congrArg wordAddress (by unfold c3HeapBase leafDest; omega)
  · rw [MachineState.getReg_setPC, q3.salts]; exact congrArg wordAddress (by unfold c3SaltBase leafSalt; omega)
  · exact (keep .x7 (by simp [SavedC3])).trans r.stride
  · exact (keep .x5 (by simp [SavedC3])).trans r.selector
  · change c3LatchPC g = _
    rw [c3LatchPC, if_neg (by omega)]

/-! ### All blocks -/

def blocks : Nat → Nat → MachineState → OracleComp World MachineState
  | 0, _, s => pure s
  | k + 1, g, s => do
    let mid ← blockTrace g s
    blocks k (g + 1) mid

theorem blocks_run (s : MachineState) (cnt g fuel : Nat) (limit : g + cnt = 8192)
    (r : 0 < cnt → BlockRegs s g) (stop : s.getReg .x21 = wordAddress (leafDest (2 ^ 24))) :
    execute packedWideCommitImage ((32817 * cnt - 1) + fuel) s true =
      (do let next ← blocks cnt g s
          let result ← execute packedWideCommitImage fuel next true
          return result.charge (135217 * cnt - 1) (8192 * cnt)) := by
  induction cnt generalizing g s with
  | zero => simp [blocks, Execution.charge]
  | succ k ih =>
    have last : (32817 * (k + 1) - 1) = 32815 + c3LatchCost g + (32817 * k - 1) ∧
        (135217 * (k + 1) - 1) = 135215 + c3LatchCost g + (135217 * k - 1) := by
      unfold c3LatchCost; split <;> constructor <;> omega
    have valid := r (by omega)
    rw [last.1, Nat.add_assoc (32815 + c3LatchCost g), block_run s g _ (by omega) valid stop]
    simp only [blocks, bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro next reached
    obtain ⟨regs, _, keep⟩ := block_post s g (by omega) valid reached
    rw [ih next (g + 1) (by omega) (fun more => regs (by omega)) ((keep .x21 (by simp [SavedC3])).trans stop), last.2]
    simp [Execution.charge, Nat.mul_succ, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem blocks_post (s : MachineState) (cnt g : Nat) (limit : g + cnt = 8192)
    (r : BlockRegs s g) (positive : 0 < cnt) {out : MachineState} (hit : out ∈ support (blocks cnt g s)) :
    out.pc = 184784 ∧ ∀ reg, SavedC3 reg → out.getReg reg = s.getReg reg := by
  induction cnt generalizing g s with
  | zero => omega
  | succ k ih =>
    simp only [blocks, mem_support_bind_iff] at hit
    obtain ⟨mid, step, reach⟩ := hit
    obtain ⟨regs, pc, keep⟩ := block_post s g (by omega) r step
    cases k with
    | zero =>
      simp only [blocks, support_pure, Set.mem_singleton_iff] at reach
      subst out
      exact ⟨by rw [pc, c3LatchPC, if_pos (by omega)], keep⟩
    | succ k =>
      obtain ⟨finish, rest⟩ := ih mid (g + 1) (by omega) (regs (by omega)) (by omega) reach
      exact ⟨finish, fun reg h => (rest reg h).trans (keep reg h)⟩

/-! ### The leaf phase -/

def jumpState (s : MachineState) : MachineState := s.setPC (wordPC blockStart)

def leafPhase (s : MachineState) : OracleComp World MachineState := blocks 8192 0 (jumpState s)

theorem ready_block_regs (s : MachineState) (entry : CommitEntry s) {bits : Nat} (coins : BitVec bits) :
    BlockRegs (jumpState (packed_wideReadyState s coins)) 0 ∧
      (jumpState (packed_wideReadyState s coins)).getReg .x21 = wordAddress (leafDest (2 ^ 24)) := by
  obtain ⟨base, stop, _⟩ := post_random_regs s entry coins
  obtain ⟨_, stride⟩ := packed_wide_ready_state_entry s entry coins
  have save := packed_wide_ready_state_register s coins
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, rfl⟩, ?_⟩
  · rw [jumpState, MachineState.getReg_setPC, packed_wide_ready_source, base.source]; rfl
  · rw [jumpState, MachineState.getReg_setPC, save .x20 (by decide), base.heap]; rfl
  · rw [jumpState, MachineState.getReg_setPC, packed_wide_ready_salts, base.salts]
    exact (wordAddress_add (leafSalt 0) 256).symm
  · rw [jumpState, MachineState.getReg_setPC, stride]
  · rw [jumpState, MachineState.getReg_setPC, save .x5 (by decide), base.selector]
  · rw [jumpState, MachineState.getReg_setPC, save .x21 (by decide), stop]

theorem first_jump_run (s : MachineState) (pc : s.pc = 4176) (fuel : Nat) :
    execute packedWideCommitImage (1 + fuel) s true =
      (do let out ← execute packedWideCommitImage fuel (jumpState s) true; return out.charge 1 0) := by
  have step : ordinaryStep s (.base (.JAL .x0 49284)) = some (jumpState s) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, jumpState, MachineState.setReg,
      MachineState.setPC, pc]
    rfl
  rw [Nat.add_comm 1 fuel, CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (fetch_first_jump s pc) step]
  rfl

def c3Leaves : PackedLeafExecution where
  trace := leafPhase
  executes s entry _ coins fuel := by
    obtain ⟨regs, stop⟩ := ready_block_regs s entry coins
    have pc := (packed_wide_ready_state_entry s entry coins).1
    rw [show 268836864 + fuel = 1 + ((32817 * 8192 - 1) + fuel) by omega, first_jump_run _ pc,
      blocks_run _ 8192 0 fuel (by decide) (fun _ => regs) stop]
    simp only [leafPhase, bind_assoc, pure_bind]
    simp [Execution.charge, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  finished s entry _ coins out hit := by
    obtain ⟨regs, _⟩ := ready_block_regs s entry coins
    obtain ⟨pc, keep⟩ := blocks_post _ 8192 0 (by decide) regs (by decide) hit
    obtain ⟨g, stop, x8, x9, x19⟩ := post_random_regs s entry coins
    have held (reg : Reg) (safe : SavedC3 reg) (diff : reg ∉ [Reg.x7, .x10, .x22]) :
        out.getReg reg = (readyState s coins).getReg reg := by
      rw [keep reg safe, jumpState, MachineState.getReg_setPC, packed_wide_ready_state_register s coins reg diff]
    exact ⟨pc, (held .x5 (by simp [SavedC3]) (by decide)).trans g.selector,
      (held .x9 (by simp [SavedC3]) (by decide)).trans x9, (held .x19 (by simp [SavedC3]) (by decide)).trans x19,
      (held .x21 (by simp [SavedC3]) (by decide)).trans stop, (held .x8 (by simp [SavedC3]) (by decide)).trans x8⟩

end TwoPermutationPrototype.RV64.C3Leaves
