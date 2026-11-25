import CommitGolfCandidate.CommitLeaf

/-! Commitment execution: initialize the heap and salt pointers, sample all private
salts, hash the leaves, and build the parent nodes. These proofs use the submitted
instruction image and the challenge interpreter. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

private def commitLoad (reg : Reg) (high : BitVec 12) : List Instr :=
  [.ADDI reg .x0 0, .SLLI reg reg 11, .ADDI reg reg high,
   .SLLI reg reg 11, .ADDI reg reg 0, .SLLI reg reg 11, .ADDI reg reg 0]

private def commitSetupInstructions : List Instr :=
  [.ADDI .x8 .x10 4064, .ADDI .x26 .x11 0, .ADDI .x9 .x12 0] ++
  commitLoad .x19 4 ++ commitLoad .x6 256 ++ [.ADD .x18 .x9 .x6] ++
  commitLoad .x6 128 ++ [.ADD .x23 .x9 .x6, .ADDI .x5 .x0 2, .ADDI .x10 .x18 0] ++
  commitLoad .x11 128

private def commitSetupPrefix (state : MachineState) (count : Nat) : MachineState :=
  (commitSetupInstructions.take count).foldl execInstrBr state

def commitSetupState (state : MachineState) : MachineState := commitSetupPrefix state 35

set_option maxHeartbeats 1000000 in
/-- The 35-instruction setup computes pointers into the admitted private trapdoor
and the total salt length; it performs no memory access or oracle call. -/
theorem commit_setup (state : MachineState) (pc : state.pc = 4096)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .commit) (35 + fuel) state allowCoins =
      (do let result ← execute (submission.image .commit) fuel (commitSetupState state) allowCoins
          return result.charge 35 0) := by
  apply execute_unit_steps (states := commitSetupPrefix state)
  intro i hi
  refine ⟨.base ((commitSetupInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply commit_fetch _ i _ (by omega)
    · interval_cases i <;>
        simp [commitSetupPrefix, commitSetupInstructions, commitLoad, execInstrBr, pc,
          MachineState.setPC]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

/-- Exact ABI-derived registers at the randomness syscall. -/
theorem commit_setup_registers (state : MachineState) :
    (commitSetupState state).getReg .x5 = 2 ∧
    (commitSetupState state).getReg .x8 = state.getReg .x10 + 18446744073709551584 ∧
    (commitSetupState state).getReg .x9 = state.getReg .x12 ∧
    (commitSetupState state).getReg .x10 = state.getReg .x12 + 1073741824 ∧
    (commitSetupState state).getReg .x11 = 536870912 ∧
    (commitSetupState state).getReg .x18 = state.getReg .x12 + 1073741824 ∧
    (commitSetupState state).getReg .x19 = 16777216 ∧
    (commitSetupState state).getReg .x23 = state.getReg .x12 + 536870912 ∧
    (commitSetupState state).getReg .x26 = state.getReg .x11 := by
  dsimp only [commitSetupState, commitSetupPrefix, commitSetupInstructions, commitLoad,
    List.append, List.take, List.foldl, execInstrBr, signExtend12,
    MachineState.getReg, MachineState.setReg, MachineState.setPC]
  simp [execInstrBr, signExtend12, MachineState.getReg, MachineState.setReg, MachineState.setPC]

theorem commit_setup_pc (state : MachineState) (pc : state.pc = 4096) :
    (commitSetupState state).pc = 4236 := by
  simp [commitSetupState, commitSetupPrefix, commitSetupInstructions, commitLoad,
    execInstrBr, MachineState.setPC, pc]

/-- The real RANDOM syscall samples the salt buffer with private coins. Its cost is
one cycle plus one cycle per eight bytes; it makes no public oracle queries. -/
theorem commit_random (state : MachineState) (pc : state.pc = 4236)
    (selector : state.getReg .x5 = 2) (valid : randomArgumentsValid state = true)
    (fuel : Nat) :
    execute (submission.image .commit) (1 + fuel) state true =
      (do let answer ← liftM ($ᵗ BitVec (8 * (state.getReg .x11).toNat) :
            ProbComp (BitVec (8 * (state.getReg .x11).toNat)))
          let result ← execute (submission.image .commit) fuel
            (writeBits state (state.getReg .x10) answer) true
          return result.charge (1 + ((state.getReg .x11).toNat + 7) / 8) 0) := by
  have fetched : fetch (submission.image .commit) state = some (.base .ECALL) := by
    apply commit_fetch _ 35 _ (by decide) pc; rfl
  rw [Nat.add_comm 1 fuel, execute, fetched]
  simp only [selector, valid]
  rfl

private def commitReadyInstructions : List Instr :=
  [.ADDI .x21 .x0 0, .SLLI .x21 .x21 11, .ADDI .x21 .x21 256, .ADDI .x20 .x0 0,
   .ADDI .x5 .x0 0, .ADDI .x11 .x0 64, .ADDI .x13 .x0 0]

private def commitReadyPrefix (state : MachineState) (count : Nat) : MachineState :=
  (commitReadyInstructions.take count).foldl execInstrBr state

def commitReadyState (state : MachineState) : MachineState := commitReadyPrefix state 7

/-- Initialize the fixed scratch pointer, leaf counter and the constant syscall
arguments of the in-place leaf calls after sampling salts. -/
theorem commit_ready (state : MachineState) (pc : state.pc = 4240) (fuel : Nat) :
    execute (submission.image .commit) (7 + fuel) state true =
      (do let result ← execute (submission.image .commit) fuel (commitReadyState state) true
          return result.charge 7 0) := by
  apply execute_unit_steps (states := commitReadyPrefix state)
  intro i hi
  refine ⟨.base ((commitReadyInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply commit_fetch _ (36 + i) _ (by omega)
    · interval_cases i <;>
        simp [commitReadyPrefix, commitReadyInstructions, execInstrBr, pc, MachineState.setPC]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem commit_ready_pc (state : MachineState) (pc : state.pc = 4240) :
    (commitReadyState state).pc = 4268 := by
  simp [commitReadyState, commitReadyPrefix, commitReadyInstructions, execInstrBr, pc, MachineState.setPC]

theorem commit_ready_counters (state : MachineState) :
    (commitReadyState state).getReg .x21 = 256 ∧ (commitReadyState state).getReg .x20 = 0 ∧
    (commitReadyState state).getReg .x5 = 0 ∧ (commitReadyState state).getReg .x11 = 64 ∧
    (commitReadyState state).getReg .x13 = 0 := by
  simp [commitReadyState, commitReadyPrefix, commitReadyInstructions, execInstrBr,
    signExtend12, MachineState.getReg, MachineState.setReg, MachineState.setPC]

theorem commit_ready_register (state : MachineState) (reg : Reg)
    (notScratch : reg ≠ .x21) (notCounter : reg ≠ .x20) (not5 : reg ≠ .x5)
    (not11 : reg ≠ .x11) (not13 : reg ≠ .x13) :
    (commitReadyState state).getReg reg = state.getReg reg := by
  cases reg <;> simp_all [commitReadyState, commitReadyPrefix, commitReadyInstructions,
    execInstrBr, signExtend12, MachineState.getReg, MachineState.setReg, MachineState.setPC]

private def commitCopySource (start : Nat) : Reg :=
  if start = 43 then .x18 else .x9
private def commitCopyDestination (start : Nat) : Reg :=
  if start = 43 then .x8 else .x26
private def commitCopyOffset (start : Nat) : Nat := if start = 92 then 32 else 0

private def commitCopyInstructions (start : Nat) : List Instr :=
  [.LD .x6 (commitCopySource start) (BitVec.ofNat 12 (commitCopyOffset start)),
   .SD (commitCopyDestination start) .x6 0,
   .LD .x6 (commitCopySource start) (BitVec.ofNat 12 (commitCopyOffset start + 8)),
   .SD (commitCopyDestination start) .x6 8,
   .LD .x6 (commitCopySource start) (BitVec.ofNat 12 (commitCopyOffset start + 16)),
   .SD (commitCopyDestination start) .x6 16,
   .LD .x6 (commitCopySource start) (BitVec.ofNat 12 (commitCopyOffset start + 24)),
   .SD (commitCopyDestination start) .x6 24]

private def commitCopyPrefix (state : MachineState) (start count : Nat) : MachineState :=
  ((commitCopyInstructions start).take count).foldl execInstrBr state

def commitCopyState (state : MachineState) (start : Nat) : MachineState := commitCopyPrefix state start 8

/-- Expose the decoded salt, leaf, and root copy instructions for memory refinement. -/
theorem commit_copy_expansion (state : MachineState) (start : Nat) :
    commitCopyState state start =
      let source := if start = 43 then Reg.x18 else Reg.x9
      let destination := if start = 43 then Reg.x8 else Reg.x26
      let offset := if start = 92 then 32 else 0
      ([.LD .x6 source (BitVec.ofNat 12 offset), .SD destination .x6 0,
        .LD .x6 source (BitVec.ofNat 12 (offset+8)), .SD destination .x6 8,
        .LD .x6 source (BitVec.ofNat 12 (offset+16)), .SD destination .x6 16,
        .LD .x6 source (BitVec.ofNat 12 (offset+24)), .SD destination .x6 24] : List Instr).foldl
          execInstrBr state := rfl

private theorem commit_copy_prefix_register (state : MachineState) (start count : Nat)
    (bounded : count ≤ 8) (reg : Reg) (notTemporary : reg ≠ .x6) :
    (commitCopyPrefix state start count).getReg reg = state.getReg reg := by
  have memRegister (state : MachineState) (address value : Word) (reg : Reg) :
      (state.setMem address value).getReg reg = state.getReg reg := by cases reg <;> rfl
  interval_cases count <;>
    simp only [commitCopyPrefix, commitCopyInstructions, List.take, List.foldl, execInstrBr,
      MachineState.getReg_setPC, memRegister,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm notTemporary)]

theorem commit_copy_register (state : MachineState) (start : Nat) (reg : Reg) (notTemporary : reg ≠ .x6) :
    (commitCopyState state start).getReg reg = state.getReg reg :=
  commit_copy_prefix_register state start 8 (by decide) reg notTemporary

theorem commit_copy_pc (state : MachineState) (start : Nat) :
    (commitCopyState state start).pc = state.pc + 32 := by
  simp [commitCopyState, commitCopyPrefix, commitCopyInstructions, execInstrBr,
    MachineState.setPC, BitVec.add_assoc]

set_option maxHeartbeats 1000000 in
/-- The actual salt store into the leaf's slot and the final root copy each take eight
ordinary instructions. The hypotheses cover every source and destination access. -/
theorem commit_copy (state : MachineState) (start : Nat)
    (location : start = 43 ∨ start = 92)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * start))
    (sourceValid : ∀ word : Fin 4,
      accessValid (state.getReg (commitCopySource start) +
        BitVec.ofNat 64 (commitCopyOffset start + 8 * word.val)) 8 = true)
    (destinationValid : ∀ word : Fin 4,
      accessValid (state.getReg (commitCopyDestination start) +
        BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .commit) (8 + fuel) state allowCoins =
      (do let result ← execute (submission.image .commit) fuel (commitCopyState state start) allowCoins
          return result.charge 8 0) := by
  apply execute_unit_steps (states := commitCopyPrefix state start)
  intro i hi
  refine ⟨.base (((commitCopyInstructions start)[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply commit_fetch _ (start + i) _ (by rcases location with rfl | rfl <;> omega)
    · rcases location with rfl | rfl <;> interval_cases i <;>
        simp [commitCopyPrefix, commitCopyInstructions, execInstrBr, pc, MachineState.setPC]
    · rcases location with rfl | rfl <;> interval_cases i <;> rfl
  · have sourceReg := commit_copy_prefix_register state start i (by omega) (commitCopySource start)
      (by rcases location with rfl | rfl <;> decide)
    have destinationReg := commit_copy_prefix_register state start i (by omega) (commitCopyDestination start)
      (by rcases location with rfl | rfl <;> decide)
    have s0 := sourceValid ⟨0, by decide⟩
    have s1 := sourceValid ⟨1, by decide⟩
    have s2 := sourceValid ⟨2, by decide⟩
    have s3 := sourceValid ⟨3, by decide⟩
    have d0 := destinationValid ⟨0, by decide⟩
    have d1 := destinationValid ⟨1, by decide⟩
    have d2 := destinationValid ⟨2, by decide⟩
    have d3 := destinationValid ⟨3, by decide⟩
    have valid : memoryArgumentsValid (commitCopyPrefix state start i)
        (((commitCopyInstructions start)[i]?).getD .EBREAK) = true := by
      rcases location with rfl | rfl <;> interval_cases i <;>
        simp only [commitCopyInstructions, List.getElem?_cons_zero, List.getElem?_cons_succ,
          Option.getD_some, memoryArgumentsValid, memAccess, sourceReg, destinationReg, signExtend12] <;>
        first | exact s0 | exact s1 | exact s2 | exact s3 |
          exact d0 | exact d1 | exact d2 | exact d3
    interval_cases i <;>
      simp only [commitCopyInstructions, List.getElem?_cons_zero, List.getElem?_cons_succ,
        Option.getD_some] at valid ⊢ <;>
      simp only [ordinaryStep, valid, ↓reduceIte] <;> rfl
  · interval_cases i <;> rfl

/-- Advance the slot, salt and heap pointers; loop while more leaves remain. Both
outcomes of the unsigned branch are represented. -/
def commitPositionNextState (state : MachineState) : MachineState :=
  ((((state.setReg .x8 (state.getReg .x8 + 256)).setReg .x18 (state.getReg .x18 + 32)).setReg
    .x23 (state.getReg .x23 + 32)).setReg .x20 (state.getReg .x20 + 1)).setPC
      (if BitVec.ult (state.getReg .x20 + 1) (state.getReg .x19) then 4268 else 4416)

private def commitNextInstructions : List Instr :=
  [.ADDI .x8 .x8 256, .ADDI .x18 .x18 32, .ADDI .x23 .x23 32, .ADDI .x20 .x20 1]

private def commitNextPrefix (state : MachineState) (count : Nat) : MachineState :=
  (commitNextInstructions.take count).foldl execInstrBr state

theorem commit_leaf_next_position (state : MachineState) (pc : state.pc = 4396) (fuel : Nat) :
    execute (submission.image .commit) (5 + fuel) state true =
      (do let result ← execute (submission.image .commit) fuel (commitPositionNextState state) true
          return result.charge 5 0) := by
  have setup (remaining : Nat) :
      execute (submission.image .commit) (4 + remaining) state true =
        (do let result ← execute (submission.image .commit) remaining (commitNextPrefix state 4) true
            return result.charge 4 0) := by
    apply execute_unit_steps (states := commitNextPrefix state)
    intro i hi
    refine ⟨.base ((commitNextInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
    · apply commit_fetch _ (75 + i) _ (by omega)
      · interval_cases i <;> simp [commitNextPrefix, commitNextInstructions, execInstrBr, pc, MachineState.setPC]
      · interval_cases i <;> rfl
    · interval_cases i <;> rfl
    · interval_cases i <;> rfl
  have fetched : fetch (submission.image .commit) (commitNextPrefix state 4) =
      some (.base (.BLTU .x20 .x19 8048)) := by
    apply commit_fetch _ 79 _ (by decide)
    · simp [commitNextPrefix, commitNextInstructions, execInstrBr, pc, MachineState.setPC]
    · rfl
  have stepped : ordinaryStep (commitNextPrefix state 4) (.base (.BLTU .x20 .x19 8048)) =
      some (commitPositionNextState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend13, signExtend12,
      commitNextPrefix, commitNextInstructions, commitPositionNextState, MachineState.getReg,
      MachineState.setReg, MachineState.setPC, pc]
    split <;> simp_all
  rw [show 5 + fuel = 4 + (fuel + 1) by omega, setup,
    execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  simp [instructionCycles, Execution.charge, ← Nat.add_assoc]

/-- Query of in-place call `j` on the current state. -/
abbrev chainQuery (state : MachineState) (j : Nat) : PublicSpec.Domain :=
  .inl (readBuffer state (state.getReg .x8 + BitVec.ofNat 64 (32*j)).toNat 64)

/-- The exact state distribution after one salt/leaf iteration: copy the salt into the
slot, then eight in-place calls, the last writing the heap slot, then advance. -/
def commitPositionRun (state : MachineState) : OracleComp World MachineState := do
  let s0 := commitCopyState state 43
  let a0 ← World.query (.inr (chainQuery s0 0))
  let s1 := chainCallState s0 0 a0
  let a1 ← World.query (.inr (chainQuery s1 1))
  let s2 := chainCallState s1 1 a1
  let a2 ← World.query (.inr (chainQuery s2 2))
  let s3 := chainCallState s2 2 a2
  let a3 ← World.query (.inr (chainQuery s3 3))
  let s4 := chainCallState s3 3 a3
  let a4 ← World.query (.inr (chainQuery s4 4))
  let s5 := chainCallState s4 4 a4
  let a5 ← World.query (.inr (chainQuery s5 5))
  let s6 := chainCallState s5 5 a5
  let a6 ← World.query (.inr (chainQuery s6 6))
  let s7 := chainCallState s6 6 a6
  let a7 ← World.query (.inr (chainQuery s7 7))
  return commitPositionNextState (chainCallState s7 7 a7)

/-- Register facts preserved through one call. -/
private theorem chain_step_facts (s : MachineState) (j : Nat) (hj : j < 8) (answer : BitVec 256)
    (slot heap : Nat) (slotPointer : s.getReg .x8 = BitVec.ofNat 64 slot)
    (heapPointer : s.getReg .x23 = BitVec.ofNat 64 heap)
    (r5 : s.getReg .x5 = 0) (r11 : s.getReg .x11 = 64) (r13 : s.getReg .x13 = 0) :
    (chainCallState s j answer).getReg .x8 = BitVec.ofNat 64 slot ∧
    (chainCallState s j answer).getReg .x23 = BitVec.ofNat 64 heap ∧
    (chainCallState s j answer).getReg .x5 = 0 ∧
    (chainCallState s j answer).getReg .x11 = 64 ∧
    (chainCallState s j answer).getReg .x13 = 0 ∧
    (chainCallState s j answer).pc = s.pc + 12 :=
  ⟨(chain_call_register s j hj answer .x8 (by decide) (by decide)).trans slotPointer,
   (chain_call_register s j hj answer .x23 (by decide) (by decide)).trans heapPointer,
   (chain_call_register s j hj answer .x5 (by decide) (by decide)).trans r5,
   (chain_call_register s j hj answer .x11 (by decide) (by decide)).trans r11,
   (chain_call_register s j hj answer .x13 (by decide) (by decide)).trans r13,
   chain_call_pc s j hj answer⟩

set_option maxHeartbeats 800000 in
/-- One complete commitment leaf iteration: store its salt in front of the leaf's
message, hash 2048 bits in place with four direct calls, the last writing the heap
slot, then advance. 37 instructions, 93 cycles and exactly eight public queries. -/
theorem commit_position (state : MachineState) (pc : state.pc = 4268)
    (r5 : state.getReg .x5 = 0) (r11 : state.getReg .x11 = 64) (r13 : state.getReg .x13 = 0)
    (slot : Nat) (slotPointer : state.getReg .x8 = BitVec.ofNat 64 slot)
    (slotAligned : slot % 8 = 0) (slotBound : slot + 288 ≤ MEMORY_BYTES)
    (saltValid : ∀ word : Fin 4,
      accessValid (state.getReg .x18 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (heap : Nat) (heapPointer : state.getReg .x23 = BitVec.ofNat 64 heap)
    (heapAligned : heap % 8 = 0) (heapBound : heap + 32 ≤ MEMORY_BYTES)
    (fuel : Nat) :
    execute (submission.image .commit) (37 + fuel) state true =
      (do let finished ← commitPositionRun state
          let result ← execute (submission.image .commit) fuel finished true
          return result.charge 93 8) := by
  have slotValid : ∀ word : Fin 4,
      accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word.val)) 8 = true := by
    intro word
    have bound : slot + 8 * word.val + 8 ≤ MEMORY_BYTES := by have := word.isLt; omega
    simp only [accessValid, rangeValid, slotPointer, pointer_offset_nat slot (8 * word.val) (by omega),
      Bool.and_eq_true, decide_eq_true_eq]
    constructor <;> omega
  let s0 := commitCopyState state 43
  have s0reg (reg : Reg) (h : reg ≠ .x6) : s0.getReg reg = state.getReg reg :=
    commit_copy_register state 43 reg h
  have s0pc : s0.pc = BitVec.ofNat 64 (4096 + 4 * (51 + 3*0)) := by
    rw [commit_copy_pc, pc]; rfl
  have p0 : s0.getReg .x8 = BitVec.ofNat 64 slot := (s0reg .x8 (by decide)).trans slotPointer
  have h0 : s0.getReg .x23 = BitVec.ofNat 64 heap := (s0reg .x23 (by decide)).trans heapPointer
  have q0 := chain_call_valid s0 0 (by decide) slot heap p0 slotAligned slotBound h0 heapAligned heapBound
  rw [show 37 + fuel = 8 + (3 + (3 + (3 + (3 + (3 + (3 + (3 + (3 + (5 + fuel))))))))) by omega,
    commit_copy state 43 (Or.inl rfl) pc
      (by simpa [commitCopySource, commitCopyOffset] using saltValid)
      (by simpa [commitCopyDestination] using slotValid),
    commit_chain_call s0 0 (by decide) s0pc ((s0reg .x5 (by decide)).trans r5)
      ((s0reg .x11 (by decide)).trans r11) ((s0reg .x13 (by decide)).trans r13)
      q0.1 q0.2.1 q0.2.2.1 q0.2.2.2]
  simp only [commitPositionRun, bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro a0 _
  let s1 := chainCallState s0 0 a0
  have f1 := chain_step_facts s0 0 (by decide) a0 slot heap p0 h0 ((s0reg .x5 (by decide)).trans r5) ((s0reg .x11 (by decide)).trans r11) ((s0reg .x13 (by decide)).trans r13)
  have s1pc : s1.pc = BitVec.ofNat 64 (4096 + 4 * (51 + 3*1)) := by
    rw [f1.2.2.2.2.2, s0pc]; rfl
  have q1 := chain_call_valid s1 1 (by decide) slot heap f1.1 slotAligned slotBound f1.2.1 heapAligned heapBound
  rw [commit_chain_call s1 1 (by decide) s1pc f1.2.2.1 f1.2.2.2.1 f1.2.2.2.2.1
    q1.1 q1.2.1 q1.2.2.1 q1.2.2.2]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro a1 _
  let s2 := chainCallState s1 1 a1
  have f2 := chain_step_facts s1 1 (by decide) a1 slot heap f1.1 f1.2.1 f1.2.2.1 f1.2.2.2.1 f1.2.2.2.2.1
  have s2pc : s2.pc = BitVec.ofNat 64 (4096 + 4 * (51 + 3*2)) := by
    rw [f2.2.2.2.2.2, s1pc]; rfl
  have q2 := chain_call_valid s2 2 (by decide) slot heap f2.1 slotAligned slotBound f2.2.1 heapAligned heapBound
  rw [commit_chain_call s2 2 (by decide) s2pc f2.2.2.1 f2.2.2.2.1 f2.2.2.2.2.1
    q2.1 q2.2.1 q2.2.2.1 q2.2.2.2]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro a2 _
  let s3 := chainCallState s2 2 a2
  have f3 := chain_step_facts s2 2 (by decide) a2 slot heap f2.1 f2.2.1 f2.2.2.1 f2.2.2.2.1 f2.2.2.2.2.1
  have s3pc : s3.pc = BitVec.ofNat 64 (4096 + 4 * (51 + 3*3)) := by
    rw [f3.2.2.2.2.2, s2pc]; rfl
  have q3 := chain_call_valid s3 3 (by decide) slot heap f3.1 slotAligned slotBound f3.2.1 heapAligned heapBound
  rw [commit_chain_call s3 3 (by decide) s3pc f3.2.2.1 f3.2.2.2.1 f3.2.2.2.2.1
    q3.1 q3.2.1 q3.2.2.1 q3.2.2.2]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro a3 _
  let s4 := chainCallState s3 3 a3
  have f4 := chain_step_facts s3 3 (by decide) a3 slot heap f3.1 f3.2.1 f3.2.2.1 f3.2.2.2.1 f3.2.2.2.2.1
  have s4pc : s4.pc = BitVec.ofNat 64 (4096 + 4 * (51 + 3*4)) := by
    rw [f4.2.2.2.2.2, s3pc]; rfl
  have q4 := chain_call_valid s4 4 (by decide) slot heap f4.1 slotAligned slotBound f4.2.1 heapAligned heapBound
  rw [commit_chain_call s4 4 (by decide) s4pc f4.2.2.1 f4.2.2.2.1 f4.2.2.2.2.1
    q4.1 q4.2.1 q4.2.2.1 q4.2.2.2]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro a4 _
  let s5 := chainCallState s4 4 a4
  have f5 := chain_step_facts s4 4 (by decide) a4 slot heap f4.1 f4.2.1 f4.2.2.1 f4.2.2.2.1 f4.2.2.2.2.1
  have s5pc : s5.pc = BitVec.ofNat 64 (4096 + 4 * (51 + 3*5)) := by
    rw [f5.2.2.2.2.2, s4pc]; rfl
  have q5 := chain_call_valid s5 5 (by decide) slot heap f5.1 slotAligned slotBound f5.2.1 heapAligned heapBound
  rw [commit_chain_call s5 5 (by decide) s5pc f5.2.2.1 f5.2.2.2.1 f5.2.2.2.2.1
    q5.1 q5.2.1 q5.2.2.1 q5.2.2.2]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro a5 _
  let s6 := chainCallState s5 5 a5
  have f6 := chain_step_facts s5 5 (by decide) a5 slot heap f5.1 f5.2.1 f5.2.2.1 f5.2.2.2.1 f5.2.2.2.2.1
  have s6pc : s6.pc = BitVec.ofNat 64 (4096 + 4 * (51 + 3*6)) := by
    rw [f6.2.2.2.2.2, s5pc]; rfl
  have q6 := chain_call_valid s6 6 (by decide) slot heap f6.1 slotAligned slotBound f6.2.1 heapAligned heapBound
  rw [commit_chain_call s6 6 (by decide) s6pc f6.2.2.1 f6.2.2.2.1 f6.2.2.2.2.1
    q6.1 q6.2.1 q6.2.2.1 q6.2.2.2]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro a6 _
  let s7 := chainCallState s6 6 a6
  have f7 := chain_step_facts s6 6 (by decide) a6 slot heap f6.1 f6.2.1 f6.2.2.1 f6.2.2.2.1 f6.2.2.2.2.1
  have s7pc : s7.pc = BitVec.ofNat 64 (4096 + 4 * (51 + 3*7)) := by
    rw [f7.2.2.2.2.2, s6pc]; rfl
  have q7 := chain_call_valid s7 7 (by decide) slot heap f7.1 slotAligned slotBound f7.2.1 heapAligned heapBound
  rw [commit_chain_call s7 7 (by decide) s7pc f7.2.2.1 f7.2.2.2.1 f7.2.2.2.2.1
    q7.1 q7.2.1 q7.2.2.1 q7.2.2.2]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro a7 _
  have f8 := chain_step_facts s7 7 (by decide) a7 slot heap f7.1 f7.2.1 f7.2.2.1 f7.2.2.2.1 f7.2.2.2.2.1
  have s8pc : (chainCallState s7 7 a7).pc = 4396 := by
    rw [f8.2.2.2.2.2, s7pc]; rfl
  rw [commit_leaf_next_position _ s8pc]
  simp [Execution.charge, ← Nat.add_assoc]
  rfl

end CommitGolfCandidate
