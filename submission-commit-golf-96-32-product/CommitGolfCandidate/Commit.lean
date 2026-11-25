import CommitGolfCandidate.CommitLeaf

/-! Commitment execution: initialize the heap and salt pointers, sample all private
salts, hash 32 leaves per iteration (four 8-leaf chunks), and prepare for parents.
These proofs use the submitted instruction image and the challenge interpreter. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

private def commitSetupPrefix (state : MachineState) (count : Nat) : MachineState :=
  (commitSetupInstructions.take count).foldl execInstrBr state

def commitSetupState (state : MachineState) : MachineState := commitSetupPrefix state 28

set_option maxHeartbeats 1000000 in
/-- The 28-instruction setup computes pointers into the admitted private trapdoor
and the total salt length; it performs no memory access or oracle call. -/
theorem commit_setup (state : MachineState) (pc : state.pc = 4096)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .commit) (28 + fuel) state allowCoins =
      (do let result ← execute (submission.image .commit) fuel (commitSetupState state) allowCoins
          return result.charge 28 0) := by
  apply execute_unit_steps (states := commitSetupPrefix state)
  intro i hi
  refine ⟨.base ((commitSetupInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply commit_fetch _ i _ (by omega)
    · interval_cases i <;>
        simp [commitSetupPrefix, commitSetupInstructions, execInstrBr, pc, MachineState.setPC]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

/-- Exact ABI-derived registers at the randomness syscall. -/
theorem commit_setup_registers (state : MachineState) :
    (commitSetupState state).getReg .x5 = 2 ∧
    (commitSetupState state).getReg .x8 = state.getReg .x10 + 18446744073709551584 ∧
    (commitSetupState state).getReg .x9 = state.getReg .x12 ∧
    (commitSetupState state).getReg .x10 = state.getReg .x12 + 1610612736 ∧
    (commitSetupState state).getReg .x11 = 536870912 ∧
    (commitSetupState state).getReg .x18 = state.getReg .x12 + 1610612736 ∧
    (commitSetupState state).getReg .x23 = state.getReg .x12 + 805306368 ∧
    (commitSetupState state).getReg .x26 = state.getReg .x11 := by
  dsimp only [commitSetupState, commitSetupPrefix, commitSetupInstructions,
    List.take, List.foldl, execInstrBr, signExtend12,
    MachineState.getReg, MachineState.setReg, MachineState.setPC]
  simp [execInstrBr, signExtend12, MachineState.getReg, MachineState.setReg, MachineState.setPC]

theorem commit_setup_pc (state : MachineState) (pc : state.pc = 4096) :
    (commitSetupState state).pc = 4208 := by
  simp [commitSetupState, commitSetupPrefix, commitSetupInstructions,
    execInstrBr, MachineState.setPC, pc]

/-- The real RANDOM syscall samples the salt buffer with private coins. Its cost is
one cycle plus one cycle per eight bytes; it makes no public oracle queries. -/
theorem commit_random (state : MachineState) (pc : state.pc = 4208)
    (selector : state.getReg .x5 = 2) (valid : randomArgumentsValid state = true)
    (fuel : Nat) :
    execute (submission.image .commit) (1 + fuel) state true =
      (do let answer ← liftM ($ᵗ BitVec (8 * (state.getReg .x11).toNat) :
            ProbComp (BitVec (8 * (state.getReg .x11).toNat)))
          let result ← execute (submission.image .commit) fuel
            (writeBits state (state.getReg .x10) answer) true
          return result.charge (1 + ((state.getReg .x11).toNat + 7) / 8) 0) := by
  have fetched : fetch (submission.image .commit) state = some (.base .ECALL) := by
    apply commit_fetch _ 28 _ (by decide) pc; rfl
  rw [Nat.add_comm 1 fuel, execute, fetched]
  simp only [selector, valid]
  rfl

private def commitReadyPrefix (state : MachineState) (count : Nat) : MachineState :=
  (commitReadyInstructions.take count).foldl execInstrBr state

def commitReadyState (state : MachineState) : MachineState := commitReadyPrefix state 10

/-- Initialize the 32-leaf iteration counter (`n/32`), chunk stride (`x29 = 2048`),
and constant syscall arguments after sampling salts. -/
theorem commit_ready (state : MachineState) (pc : state.pc = 4212) (fuel : Nat) :
    execute (submission.image .commit) (10 + fuel) state true =
      (do let result ← execute (submission.image .commit) fuel (commitReadyState state) true
          return result.charge 10 0) := by
  apply execute_unit_steps (states := commitReadyPrefix state)
  intro i hi
  refine ⟨.base ((commitReadyInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply commit_fetch _ (29 + i) _ (by omega)
    · interval_cases i <;>
        simp [commitReadyPrefix, commitReadyInstructions, execInstrBr, pc, MachineState.setPC]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem commit_ready_pc (state : MachineState) (pc : state.pc = 4212) :
    (commitReadyState state).pc = 4252 := by
  simp [commitReadyState, commitReadyPrefix, commitReadyInstructions, execInstrBr, pc,
    MachineState.setPC]

theorem commit_ready_counters (state : MachineState) :
    (commitReadyState state).getReg .x20 = 524288 ∧
    (commitReadyState state).getReg .x29 = 2048 ∧
    (commitReadyState state).getReg .x5 = 0 ∧
    (commitReadyState state).getReg .x11 = 96 ∧
    (commitReadyState state).getReg .x13 = 0 := by
  simp [commitReadyState, commitReadyPrefix, commitReadyInstructions, execInstrBr,
    signExtend12, MachineState.getReg, MachineState.setReg, MachineState.setPC]

theorem commit_ready_register (state : MachineState) (reg : Reg)
    (notCounter : reg ≠ .x20) (not29 : reg ≠ .x29) (not5 : reg ≠ .x5)
    (not11 : reg ≠ .x11) (not13 : reg ≠ .x13) :
    (commitReadyState state).getReg reg = state.getReg reg := by
  cases reg <;> simp_all [commitReadyState, commitReadyPrefix, commitReadyInstructions,
    execInstrBr, signExtend12, MachineState.getReg, MachineState.setReg, MachineState.setPC]

private def commitCopyPrefix (state : MachineState) (src dst : Reg)
    (srcOff dstOff count : Nat) : MachineState :=
  ((commitCopyInstructions src dst srcOff dstOff).take count).foldl execInstrBr state

def commitCopyState (state : MachineState) (src dst : Reg) (srcOff dstOff : Nat) : MachineState :=
  commitCopyPrefix state src dst srcOff dstOff 8

/-- Expose the decoded salt and root copy instructions for memory refinement. -/
theorem commit_copy_expansion (state : MachineState) (src dst : Reg) (srcOff dstOff : Nat) :
    commitCopyState state src dst srcOff dstOff =
      ([.LD .x6 src (BitVec.ofNat 12 srcOff), .SD dst .x6 (BitVec.ofNat 12 dstOff),
        .LD .x6 src (BitVec.ofNat 12 (srcOff + 8)), .SD dst .x6 (BitVec.ofNat 12 (dstOff + 8)),
        .LD .x6 src (BitVec.ofNat 12 (srcOff + 16)), .SD dst .x6 (BitVec.ofNat 12 (dstOff + 16)),
        .LD .x6 src (BitVec.ofNat 12 (srcOff + 24)), .SD dst .x6 (BitVec.ofNat 12 (dstOff + 24))] :
        List Instr).foldl execInstrBr state := rfl

private theorem commit_copy_prefix_register (state : MachineState) (src dst : Reg)
    (srcOff dstOff count : Nat) (bounded : count ≤ 8) (reg : Reg) (notTemporary : reg ≠ .x6) :
    (commitCopyPrefix state src dst srcOff dstOff count).getReg reg = state.getReg reg := by
  have memRegister (s : MachineState) (address value : Word) (r : Reg) :
      (s.setMem address value).getReg r = s.getReg r := by cases r <;> rfl
  interval_cases count <;>
    simp only [commitCopyPrefix, commitCopyInstructions, List.take, List.foldl, execInstrBr,
      MachineState.getReg_setPC, memRegister,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm notTemporary)]

theorem commit_copy_register (state : MachineState) (src dst : Reg) (srcOff dstOff : Nat)
    (reg : Reg) (notTemporary : reg ≠ .x6) :
    (commitCopyState state src dst srcOff dstOff).getReg reg = state.getReg reg :=
  commit_copy_prefix_register state src dst srcOff dstOff 8 (by decide) reg notTemporary

theorem commit_copy_pc (state : MachineState) (src dst : Reg) (srcOff dstOff : Nat) :
    (commitCopyState state src dst srcOff dstOff).pc = state.pc + 32 := by
  simp only [commitCopyState, commitCopyPrefix, commitCopyInstructions, List.take, List.foldl,
    execInstrBr, MachineState.pc_setReg, MachineState.pc_setMem, MachineState.setPC,
    BitVec.add_assoc]
  rfl

set_option maxHeartbeats 2400000 in
/-- Any 8-instruction digest copy in the commitment image (salt loads and root output). -/
theorem commit_copy (state : MachineState) (start : Nat) (src dst : Reg) (srcOff dstOff : Nat)
    (startBound : start + 8 ≤ 811)
    (codeAt : ∀ i < 8, commitInstrAt (start + i) = (commitCopyInstructions src dst srcOff dstOff)[i]?)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * start))
    (hsrc6 : src ≠ .x6) (hdst6 : dst ≠ .x6)
    (hsrcBound : srcOff + 24 < 2048) (hsrcAligned : srcOff % 8 = 0)
    (hdstBound : dstOff + 24 < 2048) (hdstAligned : dstOff % 8 = 0)
    (sourceValid : ∀ word : Fin 4,
      accessValid (state.getReg src + BitVec.ofNat 64 (srcOff + 8 * word.val)) 8 = true)
    (destinationValid : ∀ word : Fin 4,
      accessValid (state.getReg dst + BitVec.ofNat 64 (dstOff + 8 * word.val)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .commit) (8 + fuel) state allowCoins =
      (do let result ← execute (submission.image .commit) fuel
            (commitCopyState state src dst srcOff dstOff) allowCoins
          return result.charge 8 0) := by
  have hs0 : signExtend12 (BitVec.ofNat 12 srcOff) = BitVec.ofNat 64 srcOff :=
    signExtend12_ofNat_mul8 srcOff (by omega) hsrcAligned
  have hs1 : signExtend12 (BitVec.ofNat 12 (srcOff + 8)) = BitVec.ofNat 64 (srcOff + 8) :=
    signExtend12_ofNat_mul8 (srcOff + 8) (by omega) (by omega)
  have hs2 : signExtend12 (BitVec.ofNat 12 (srcOff + 16)) = BitVec.ofNat 64 (srcOff + 16) :=
    signExtend12_ofNat_mul8 (srcOff + 16) (by omega) (by omega)
  have hs3 : signExtend12 (BitVec.ofNat 12 (srcOff + 24)) = BitVec.ofNat 64 (srcOff + 24) :=
    signExtend12_ofNat_mul8 (srcOff + 24) (by omega) (by omega)
  have hd0 : signExtend12 (BitVec.ofNat 12 dstOff) = BitVec.ofNat 64 dstOff :=
    signExtend12_ofNat_mul8 dstOff (by omega) hdstAligned
  have hd1 : signExtend12 (BitVec.ofNat 12 (dstOff + 8)) = BitVec.ofNat 64 (dstOff + 8) :=
    signExtend12_ofNat_mul8 (dstOff + 8) (by omega) (by omega)
  have hd2 : signExtend12 (BitVec.ofNat 12 (dstOff + 16)) = BitVec.ofNat 64 (dstOff + 16) :=
    signExtend12_ofNat_mul8 (dstOff + 16) (by omega) (by omega)
  have hd3 : signExtend12 (BitVec.ofNat 12 (dstOff + 24)) = BitVec.ofNat 64 (dstOff + 24) :=
    signExtend12_ofNat_mul8 (dstOff + 24) (by omega) (by omega)
  have s0 : accessValid (state.getReg src + BitVec.ofNat 64 srcOff) 8 = true := by
    simpa using sourceValid ⟨0, by decide⟩
  have s1 : accessValid (state.getReg src + BitVec.ofNat 64 (srcOff + 8)) 8 = true := by
    simpa using sourceValid ⟨1, by decide⟩
  have s2 : accessValid (state.getReg src + BitVec.ofNat 64 (srcOff + 16)) 8 = true := by
    simpa using sourceValid ⟨2, by decide⟩
  have s3 : accessValid (state.getReg src + BitVec.ofNat 64 (srcOff + 24)) 8 = true := by
    simpa using sourceValid ⟨3, by decide⟩
  have d0 : accessValid (state.getReg dst + BitVec.ofNat 64 dstOff) 8 = true := by
    simpa using destinationValid ⟨0, by decide⟩
  have d1 : accessValid (state.getReg dst + BitVec.ofNat 64 (dstOff + 8)) 8 = true := by
    simpa using destinationValid ⟨1, by decide⟩
  have d2 : accessValid (state.getReg dst + BitVec.ofNat 64 (dstOff + 16)) 8 = true := by
    simpa using destinationValid ⟨2, by decide⟩
  have d3 : accessValid (state.getReg dst + BitVec.ofNat 64 (dstOff + 24)) 8 = true := by
    simpa using destinationValid ⟨3, by decide⟩
  apply execute_unit_steps (states := commitCopyPrefix state src dst srcOff dstOff)
  intro i hi
  refine ⟨.base (((commitCopyInstructions src dst srcOff dstOff)[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply commit_fetch _ (start + i) _ (by omega)
    · interval_cases i
      · simpa [commitCopyPrefix] using pc
      · simp only [commitCopyPrefix, commitCopyInstructions, List.take, List.foldl, execInstrBr,
          MachineState.pc_setReg, MachineState.pc_setMem, MachineState.setPC, pc, BitVec.add_assoc]
        exact pc_add_steps start 1 (start + 1) (by omega)
      · simp only [commitCopyPrefix, commitCopyInstructions, List.take, List.foldl, execInstrBr,
          MachineState.pc_setReg, MachineState.pc_setMem, MachineState.setPC, pc, BitVec.add_assoc]
        exact pc_add_steps start 2 (start + 2) (by omega)
      · simp only [commitCopyPrefix, commitCopyInstructions, List.take, List.foldl, execInstrBr,
          MachineState.pc_setReg, MachineState.pc_setMem, MachineState.setPC, pc, BitVec.add_assoc]
        exact pc_add_steps start 3 (start + 3) (by omega)
      · simp only [commitCopyPrefix, commitCopyInstructions, List.take, List.foldl, execInstrBr,
          MachineState.pc_setReg, MachineState.pc_setMem, MachineState.setPC, pc, BitVec.add_assoc]
        exact pc_add_steps start 4 (start + 4) (by omega)
      · simp only [commitCopyPrefix, commitCopyInstructions, List.take, List.foldl, execInstrBr,
          MachineState.pc_setReg, MachineState.pc_setMem, MachineState.setPC, pc, BitVec.add_assoc]
        exact pc_add_steps start 5 (start + 5) (by omega)
      · simp only [commitCopyPrefix, commitCopyInstructions, List.take, List.foldl, execInstrBr,
          MachineState.pc_setReg, MachineState.pc_setMem, MachineState.setPC, pc, BitVec.add_assoc]
        exact pc_add_steps start 6 (start + 6) (by omega)
      · simp only [commitCopyPrefix, commitCopyInstructions, List.take, List.foldl, execInstrBr,
          MachineState.pc_setReg, MachineState.pc_setMem, MachineState.setPC, pc, BitVec.add_assoc]
        exact pc_add_steps start 7 (start + 7) (by omega)
    · have hc := codeAt i hi
      interval_cases i <;> simpa [commitCopyInstructions] using hc
  · have sourceReg := commit_copy_prefix_register state src dst srcOff dstOff i (by omega) src hsrc6
    have destReg := commit_copy_prefix_register state src dst srcOff dstOff i (by omega) dst hdst6
    have valid : memoryArgumentsValid (commitCopyPrefix state src dst srcOff dstOff i)
        (((commitCopyInstructions src dst srcOff dstOff)[i]?).getD .EBREAK) = true := by
      interval_cases i <;>
        simp only [commitCopyInstructions, List.getElem?_cons_zero, List.getElem?_cons_succ,
          Option.getD_some, memoryArgumentsValid, memAccess, sourceReg, destReg,
          hs0, hs1, hs2, hs3, hd0, hd1, hd2, hd3] <;>
        first | exact s0 | exact s1 | exact s2 | exact s3 |
          exact d0 | exact d1 | exact d2 | exact d3
    interval_cases i <;>
      simp only [commitCopyInstructions, List.getElem?_cons_zero, List.getElem?_cons_succ,
        Option.getD_some] at valid ⊢ <;>
      simp only [ordinaryStep, valid, ↓reduceIte] <;> rfl
  · interval_cases i <;> rfl

/-- End-of-chunk advance: `ADD x8, x8, x29` (1 instruction, 1 cycle). -/
def chunkAdvanceState (state : MachineState) : MachineState :=
  (state.setReg .x8 (state.getReg .x8 + state.getReg .x29)).setPC (state.pc + 4)

theorem commit_chunk_advance (state : MachineState) (c : Nat) (hc : c < 4)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * (199 + 161 * c))) (fuel : Nat) :
    execute (submission.image .commit) (1 + fuel) state true =
      (do let result ← execute (submission.image .commit) fuel (chunkAdvanceState state) true
          return result.charge 1 0) := by
  have fetched : fetch (submission.image .commit) state = some (.base (.ADD .x8 .x8 .x29)) := by
    apply commit_fetch _ (199 + 161 * c) _ (by omega) pc
    exact commit_instr_chunk_advance c hc
  have stepped : ordinaryStep state (.base (.ADD .x8 .x8 .x29)) = some (chunkAdvanceState state) := rfl
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  rfl

/-- Advance the salt and heap pointers by 32 leaves and loop while iterations remain. -/
def commitPositionNextState (state : MachineState) : MachineState :=
  (((state.setReg .x18 (state.getReg .x18 + 1024)).setReg .x23 (state.getReg .x23 + 1536)).setReg
    .x20 (state.getReg .x20 - 1)).setPC
      (if state.getReg .x20 - 1 = 0 then 6844 else 4252)

private def commitNextPrefix (state : MachineState) (count : Nat) : MachineState :=
  (commitNextInstructions.take count).foldl execInstrBr state

theorem commit_leaf_next_position (state : MachineState) (pc : state.pc = 6828) (fuel : Nat) :
    execute (submission.image .commit) (4 + fuel) state true =
      (do let result ← execute (submission.image .commit) fuel (commitPositionNextState state) true
          return result.charge 4 0) := by
  have setup (remaining : Nat) :
      execute (submission.image .commit) (3 + remaining) state true =
        (do let result ← execute (submission.image .commit) remaining (commitNextPrefix state 3) true
            return result.charge 3 0) := by
    apply execute_unit_steps (states := commitNextPrefix state)
    intro i hi
    refine ⟨.base ((commitNextInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
    · apply commit_fetch _ (683 + i) _ (by omega)
      · interval_cases i <;>
          simp [commitNextPrefix, commitNextInstructions, execInstrBr, pc, MachineState.setPC]
      · interval_cases i <;> rfl
    · interval_cases i <;> rfl
    · interval_cases i <;> rfl
  have fetched : fetch (submission.image .commit) (commitNextPrefix state 3) =
      some (.base (.BNE .x20 .x0 5604)) := by
    apply commit_fetch _ 686 _ (by decide)
    · simp [commitNextPrefix, commitNextInstructions, execInstrBr, pc, MachineState.setPC]
    · rfl
  have stepped : ordinaryStep (commitNextPrefix state 3) (.base (.BNE .x20 .x0 5604)) =
      some (commitPositionNextState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend13, signExtend12,
      commitNextPrefix, commitNextInstructions, commitPositionNextState, MachineState.getReg,
      MachineState.setReg, MachineState.setPC, pc, BitVec.sub_eq_add_neg]
    split <;> simp_all
  rw [show 4 + fuel = 3 + (fuel + 1) by omega, setup,
    execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  simp [instructionCycles, Execution.charge, ← Nat.add_assoc]

/-- Query of in-place call `j` of lane `k` on the current state. -/
abbrev chainQuery (state : MachineState) (k j : Nat) : PublicSpec.Domain :=
  .inl (readBuffer state (chainSource state k j).toNat 96)

/-- The four in-place calls of lane `k` in chunk `c`. -/
def laneRun (state : MachineState) (c k : Nat) : OracleComp World MachineState := do
  let a0 ← World.query (.inr (chainQuery state k 0))
  let s1 := chainCallState state c k 0 a0
  let a1 ← World.query (.inr (chainQuery s1 k 1))
  let s2 := chainCallState s1 c k 1 a1
  let a2 ← World.query (.inr (chainQuery s2 k 2))
  let s3 := chainCallState s2 c k 2 a2
  let a3 ← World.query (.inr (chainQuery s3 k 3))
  return chainCallState s3 c k 3 a3

/-- Salt copy followed by four in-place calls for leaf `k` in chunk `c`. -/
def leafRun (state : MachineState) (c k : Nat) : OracleComp World MachineState :=
  laneRun (commitCopyState state .x18 .x8 (256 * c + 32 * k) (256 * k)) c k

/-- `count` consecutive leaves starting at lane `start` inside chunk `c`. -/
def chunkLeavesFrom (state : MachineState) (c start : Nat) : Nat → OracleComp World MachineState
  | 0 => pure state
  | remaining + 1 => do
      let next ← leafRun state c start
      chunkLeavesFrom next c (start + 1) remaining

/-- One 8-leaf chunk `c`: hash 8 leaves then advance `x8` by `x29` (`2048`). -/
def chunkRun (state : MachineState) (c : Nat) : OracleComp World MachineState := do
  let hashed ← chunkLeavesFrom state c 0 8
  return chunkAdvanceState hashed

/-- `count` consecutive 8-leaf chunks starting at chunk `start`. -/
def iterChunksFrom (state : MachineState) (start : Nat) : Nat → OracleComp World MachineState
  | 0 => pure state
  | remaining + 1 => do
      let next ← chunkRun state start
      iterChunksFrom next (start + 1) remaining

/-- Exact state distribution after one 32-leaf iteration: four 8-leaf chunks then latch. -/
def commitPositionRun (state : MachineState) : OracleComp World MachineState := do
  let chunks ← iterChunksFrom state 0 4
  return commitPositionNextState chunks

/-- Register facts preserved through one call. -/
private theorem chain_step_facts (s : MachineState) (c k j : Nat)
    (hc : c < 4) (hk : k < 8) (hj : j < 4) (answer : BitVec 256)
    (slot heap : Nat) (slotPointer : s.getReg .x8 = BitVec.ofNat 64 slot)
    (heapPointer : s.getReg .x23 = BitVec.ofNat 64 heap)
    (r5 : s.getReg .x5 = 0) (r11 : s.getReg .x11 = 96) (r13 : s.getReg .x13 = 0) :
    (chainCallState s c k j answer).getReg .x8 = BitVec.ofNat 64 slot ∧
    (chainCallState s c k j answer).getReg .x23 = BitVec.ofNat 64 heap ∧
    (chainCallState s c k j answer).getReg .x5 = 0 ∧
    (chainCallState s c k j answer).getReg .x11 = 96 ∧
    (chainCallState s c k j answer).getReg .x13 = 0 ∧
    (chainCallState s c k j answer).pc = s.pc + 12 :=
  ⟨(chain_call_register s c k j hc hk hj answer .x8 (by decide) (by decide)).trans slotPointer,
   (chain_call_register s c k j hc hk hj answer .x23 (by decide) (by decide)).trans heapPointer,
   (chain_call_register s c k j hc hk hj answer .x5 (by decide) (by decide)).trans r5,
   (chain_call_register s c k j hc hk hj answer .x11 (by decide) (by decide)).trans r11,
   (chain_call_register s c k j hc hk hj answer .x13 (by decide) (by decide)).trans r13,
   chain_call_pc s c k j hc hk hj answer⟩

theorem pc_add_twelve (n m : Nat) (h : m = n + 3) :
    BitVec.ofNat 64 (4096 + 4 * n) + 12 = BitVec.ofNat 64 (4096 + 4 * m) :=
  pc_add_steps n 3 m h

attribute [local irreducible] execute

set_option maxHeartbeats 1600000 in
/-- The four in-place calls of lane `k` in chunk `c`: 12 instructions, 40 cycles, 4 queries. -/
theorem commit_lane (state : MachineState) (c k : Nat) (hc : c < 4) (hk : k < 8)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * (47 + 161 * c + 20 * k)))
    (r5 : state.getReg .x5 = 0) (r11 : state.getReg .x11 = 96) (r13 : state.getReg .x13 = 0)
    (slot : Nat) (slotPointer : state.getReg .x8 = BitVec.ofNat 64 slot)
    (slotAligned : slot % 8 = 0) (slotBound : slot + 2080 ≤ MEMORY_BYTES)
    (heap : Nat) (heapPointer : state.getReg .x23 = BitVec.ofNat 64 heap)
    (heapAligned : heap % 8 = 0) (heapBound : heap + 1536 ≤ MEMORY_BYTES)
    (fuel : Nat) :
    execute (submission.image .commit) (12 + fuel) state true =
      (do let finished ← laneRun state c k
          let result ← execute (submission.image .commit) fuel finished true
          return result.charge 40 4) := by
  have pc0 : state.pc = BitVec.ofNat 64 (4096 + 4 * (47 + 161 * c + 20 * k + 3 * 0)) := by
    rw [pc, show 47 + 161 * c + 20 * k + 3 * 0 = 47 + 161 * c + 20 * k by omega]
  have q0 := chain_call_valid state c k 0 hc hk (by decide) slot heap slotPointer slotAligned
    slotBound heapPointer heapAligned heapBound
  rw [show 12 + fuel = 3 + (3 + (3 + (3 + fuel))) by omega,
    commit_chain_call state c k 0 hc hk (by decide) pc0 r5 r11 r13 q0.1 q0.2.1 q0.2.2.1 q0.2.2.2]
  simp only [laneRun, bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro a0 _
  let s1 := chainCallState state c k 0 a0
  have f1 := chain_step_facts state c k 0 hc hk (by decide) a0 slot heap slotPointer heapPointer
    r5 r11 r13
  have s1pc : s1.pc = BitVec.ofNat 64 (4096 + 4 * (47 + 161 * c + 20 * k + 3 * 1)) := by
    rw [f1.2.2.2.2.2, pc0]
    exact pc_add_twelve (47 + 161 * c + 20 * k + 3 * 0) (47 + 161 * c + 20 * k + 3 * 1) (by omega)
  have q1 := chain_call_valid s1 c k 1 hc hk (by decide) slot heap f1.1 slotAligned slotBound
    f1.2.1 heapAligned heapBound
  rw [commit_chain_call s1 c k 1 hc hk (by decide) s1pc f1.2.2.1 f1.2.2.2.1 f1.2.2.2.2.1
    q1.1 q1.2.1 q1.2.2.1 q1.2.2.2]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro a1 _
  let s2 := chainCallState s1 c k 1 a1
  have f2 := chain_step_facts s1 c k 1 hc hk (by decide) a1 slot heap f1.1 f1.2.1 f1.2.2.1
    f1.2.2.2.1 f1.2.2.2.2.1
  have s2pc : s2.pc = BitVec.ofNat 64 (4096 + 4 * (47 + 161 * c + 20 * k + 3 * 2)) := by
    rw [f2.2.2.2.2.2, s1pc]
    exact pc_add_twelve (47 + 161 * c + 20 * k + 3 * 1) (47 + 161 * c + 20 * k + 3 * 2) (by omega)
  have q2 := chain_call_valid s2 c k 2 hc hk (by decide) slot heap f2.1 slotAligned slotBound
    f2.2.1 heapAligned heapBound
  rw [commit_chain_call s2 c k 2 hc hk (by decide) s2pc f2.2.2.1 f2.2.2.2.1 f2.2.2.2.2.1
    q2.1 q2.2.1 q2.2.2.1 q2.2.2.2]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro a2 _
  let s3 := chainCallState s2 c k 2 a2
  have f3 := chain_step_facts s2 c k 2 hc hk (by decide) a2 slot heap f2.1 f2.2.1 f2.2.2.1
    f2.2.2.2.1 f2.2.2.2.2.1
  have s3pc : s3.pc = BitVec.ofNat 64 (4096 + 4 * (47 + 161 * c + 20 * k + 3 * 3)) := by
    rw [f3.2.2.2.2.2, s2pc]
    exact pc_add_twelve (47 + 161 * c + 20 * k + 3 * 2) (47 + 161 * c + 20 * k + 3 * 3) (by omega)
  have q3 := chain_call_valid s3 c k 3 hc hk (by decide) slot heap f3.1 slotAligned slotBound
    f3.2.1 heapAligned heapBound
  rw [commit_chain_call s3 c k 3 hc hk (by decide) s3pc f3.2.2.1 f3.2.2.2.1 f3.2.2.2.2.1
    q3.1 q3.2.1 q3.2.2.1 q3.2.2.2]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro a3 _
  simp [Execution.charge, ← Nat.add_assoc]
  rfl

theorem lane_run_support (state finished : MachineState) (c k : Nat)
    (reachable : finished ∈ support (laneRun state c k)) :
    ∃ a0 a1 a2 a3, finished = chainCallState (chainCallState (chainCallState (chainCallState
      state c k 0 a0) c k 1 a1) c k 2 a2) c k 3 a3 := by
  simp only [laneRun, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reachable
  obtain ⟨a0, _, a1, _, a2, _, a3, _, rfl⟩ := reachable
  exact ⟨a0, a1, a2, a3, rfl⟩

theorem lane_run_register (state finished : MachineState) (c k : Nat)
    (hc : c < 4) (hk : k < 8)
    (reachable : finished ∈ support (laneRun state c k))
    (reg : Reg) (n10 : reg ≠ .x10) (n12 : reg ≠ .x12) :
    finished.getReg reg = state.getReg reg := by
  obtain ⟨a0, a1, a2, a3, rfl⟩ := lane_run_support state finished c k reachable
  rw [chain_call_register _ c k 3 hc hk (by decide) _ reg n10 n12,
    chain_call_register _ c k 2 hc hk (by decide) _ reg n10 n12,
    chain_call_register _ c k 1 hc hk (by decide) _ reg n10 n12,
    chain_call_register _ c k 0 hc hk (by decide) _ reg n10 n12]

theorem lane_run_pc (state finished : MachineState) (c k : Nat)
    (hc : c < 4) (hk : k < 8)
    (reachable : finished ∈ support (laneRun state c k)) :
    finished.pc = state.pc + 48 := by
  obtain ⟨a0, a1, a2, a3, rfl⟩ := lane_run_support state finished c k reachable
  rw [chain_call_pc _ c k 3 hc hk (by decide), chain_call_pc _ c k 2 hc hk (by decide),
    chain_call_pc _ c k 1 hc hk (by decide), chain_call_pc _ c k 0 hc hk (by decide)]
  simp only [BitVec.add_assoc]
  rfl

theorem leaf_run_register (state finished : MachineState) (c k : Nat)
    (hc : c < 4) (hk : k < 8)
    (reachable : finished ∈ support (leafRun state c k))
    (reg : Reg) (n6 : reg ≠ .x6) (n10 : reg ≠ .x10) (n12 : reg ≠ .x12) :
    finished.getReg reg = state.getReg reg :=
  (lane_run_register _ finished c k hc hk reachable reg n10 n12).trans
    (commit_copy_register state .x18 .x8 _ _ reg n6)

theorem leaf_run_pc (state finished : MachineState) (c k : Nat)
    (hc : c < 4) (hk : k < 8)
    (reachable : finished ∈ support (leafRun state c k)) :
    finished.pc = state.pc + 80 := by
  rw [lane_run_pc _ finished c k hc hk reachable, commit_copy_pc, BitVec.add_assoc]
  rfl

/-- One leaf (salt copy + 4 in-place calls): 20 instructions, 48 cycles, 4 queries. -/
theorem commit_leaf (state : MachineState) (c k : Nat) (hc : c < 4) (hk : k < 8)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * (39 + 161 * c + 20 * k)))
    (r5 : state.getReg .x5 = 0) (r11 : state.getReg .x11 = 96) (r13 : state.getReg .x13 = 0)
    (slot : Nat) (slotPointer : state.getReg .x8 = BitVec.ofNat 64 slot)
    (slotAligned : slot % 8 = 0) (slotBound : slot + 2080 ≤ MEMORY_BYTES)
    (saltValid : ∀ word : Fin 128,
      accessValid (state.getReg .x18 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (heap : Nat) (heapPointer : state.getReg .x23 = BitVec.ofNat 64 heap)
    (heapAligned : heap % 8 = 0) (heapBound : heap + 1536 ≤ MEMORY_BYTES)
    (fuel : Nat) :
    execute (submission.image .commit) (20 + fuel) state true =
      (do let finished ← leafRun state c k
          let result ← execute (submission.image .commit) fuel finished true
          return result.charge 48 4) := by
  have mem : MEMORY_BYTES = 2 ^ 36 := rfl
  let s0 := commitCopyState state .x18 .x8 (256 * c + 32 * k) (256 * k)
  have s0reg (reg : Reg) (h : reg ≠ .x6) : s0.getReg reg = state.getReg reg :=
    commit_copy_register state .x18 .x8 _ _ reg h
  have s0pc : s0.pc = BitVec.ofNat 64 (4096 + 4 * (47 + 161 * c + 20 * k)) := by
    rw [commit_copy_pc, pc]
    exact pc_add_steps _ 8 _ (by omega)
  have srcValid : ∀ word : Fin 4,
      accessValid (state.getReg .x18 + BitVec.ofNat 64 (256 * c + 32 * k + 8 * word.val)) 8 = true := by
    intro word
    have hw := word.isLt
    have := saltValid ⟨32 * c + 4 * k + word.val, by omega⟩
    simpa [show 8 * (32 * c + 4 * k + word.val) = 256 * c + 32 * k + 8 * word.val by omega] using this
  have dstValid : ∀ word : Fin 4,
      accessValid (state.getReg .x8 + BitVec.ofNat 64 (256 * k + 8 * word.val)) 8 = true := by
    intro word
    have hw := word.isLt
    simp only [accessValid, rangeValid, slotPointer,
      pointer_offset_nat slot (256 * k + 8 * word.val) (by omega),
      Bool.and_eq_true, decide_eq_true_eq]
    constructor <;> omega
  rw [show 20 + fuel = 8 + (12 + fuel) by omega,
    commit_copy state (39 + 161 * c + 20 * k) .x18 .x8 (256 * c + 32 * k) (256 * k) (by omega)
      (fun i hi => commit_instr_leaf_copy c k i hc hk hi) pc (by decide) (by decide)
      (by omega) (by omega) (by omega) (by omega) srcValid dstValid,
    commit_lane s0 c k hc hk s0pc ((s0reg .x5 (by decide)).trans r5)
      ((s0reg .x11 (by decide)).trans r11) ((s0reg .x13 (by decide)).trans r13)
      slot ((s0reg .x8 (by decide)).trans slotPointer) slotAligned slotBound
      heap ((s0reg .x23 (by decide)).trans heapPointer) heapAligned heapBound]
  simp only [leafRun, bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro finished _
  simp [Execution.charge, ← Nat.add_assoc]

theorem chunk_leaves_from_register (state finished : MachineState) (c start remaining : Nat)
    (hc : c < 4) (hbound : start + remaining ≤ 8)
    (reachable : finished ∈ support (chunkLeavesFrom state c start remaining))
    (reg : Reg) (n6 : reg ≠ .x6) (n10 : reg ≠ .x10) (n12 : reg ≠ .x12) :
    finished.getReg reg = state.getReg reg := by
  induction remaining generalizing state start with
  | zero =>
    simp only [chunkLeavesFrom, support_pure, Set.mem_singleton_iff] at reachable
    subst finished
    rfl
  | succ remaining ih =>
    simp only [chunkLeavesFrom, mem_support_bind_iff] at reachable
    obtain ⟨next, reached, rest⟩ := reachable
    exact (ih next (start + 1) (by omega) rest).trans
      (leaf_run_register state next c start hc (by omega) reached reg n6 n10 n12)

theorem chunk_leaves_from_pc (state finished : MachineState) (c start remaining : Nat)
    (hc : c < 4) (hbound : start + remaining ≤ 8)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * (39 + 161 * c + 20 * start)))
    (reachable : finished ∈ support (chunkLeavesFrom state c start remaining)) :
    finished.pc = BitVec.ofNat 64 (4096 + 4 * (39 + 161 * c + 20 * (start + remaining))) := by
  induction remaining generalizing state start with
  | zero =>
    simp only [chunkLeavesFrom, support_pure, Set.mem_singleton_iff] at reachable
    subst finished
    simpa using pc
  | succ remaining ih =>
    simp only [chunkLeavesFrom, mem_support_bind_iff] at reachable
    obtain ⟨next, reached, rest⟩ := reachable
    have nextPC : next.pc = BitVec.ofNat 64 (4096 + 4 * (39 + 161 * c + 20 * (start + 1))) := by
      rw [leaf_run_pc state next c start hc (by omega) reached, pc]
      exact pc_add_steps _ 20 _ (by omega)
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      ih next (start + 1) (by omega) nextPC rest

theorem commit_chunk_leaves_from (state : MachineState) (c start remaining : Nat)
    (hc : c < 4) (hbound : start + remaining ≤ 8)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * (39 + 161 * c + 20 * start)))
    (r5 : state.getReg .x5 = 0) (r11 : state.getReg .x11 = 96) (r13 : state.getReg .x13 = 0)
    (slot : Nat) (slotPointer : state.getReg .x8 = BitVec.ofNat 64 slot)
    (slotAligned : slot % 8 = 0) (slotBound : slot + 2080 ≤ MEMORY_BYTES)
    (saltValid : ∀ word : Fin 128,
      accessValid (state.getReg .x18 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (heap : Nat) (heapPointer : state.getReg .x23 = BitVec.ofNat 64 heap)
    (heapAligned : heap % 8 = 0) (heapBound : heap + 1536 ≤ MEMORY_BYTES)
    (fuel : Nat) :
    execute (submission.image .commit) (20 * remaining + fuel) state true =
      (do let finished ← chunkLeavesFrom state c start remaining
          let result ← execute (submission.image .commit) fuel finished true
          return result.charge (48 * remaining) (4 * remaining)) := by
  induction remaining generalizing state start with
  | zero => simp [chunkLeavesFrom, Execution.charge]
  | succ remaining ih =>
    rw [show 20 * (remaining + 1) + fuel = 20 + (20 * remaining + fuel) by omega,
      commit_leaf state c start hc (by omega) pc r5 r11 r13 slot slotPointer slotAligned slotBound
        saltValid heap heapPointer heapAligned heapBound]
    simp only [chunkLeavesFrom, bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro next reached
    have keep (reg : Reg) (n6 : reg ≠ .x6) (n10 : reg ≠ .x10) (n12 : reg ≠ .x12) :
        next.getReg reg = state.getReg reg :=
      leaf_run_register state next c start hc (by omega) reached reg n6 n10 n12
    have nextPC : next.pc = BitVec.ofNat 64 (4096 + 4 * (39 + 161 * c + 20 * (start + 1))) := by
      rw [leaf_run_pc state next c start hc (by omega) reached, pc]
      exact pc_add_steps _ 20 _ (by omega)
    rw [ih next (start + 1) (by omega) nextPC
      ((keep .x5 (by decide) (by decide) (by decide)).trans r5)
      ((keep .x11 (by decide) (by decide) (by decide)).trans r11)
      ((keep .x13 (by decide) (by decide) (by decide)).trans r13)
      ((keep .x8 (by decide) (by decide) (by decide)).trans slotPointer)
      (by intro word; rw [keep .x18 (by decide) (by decide) (by decide)]; exact saltValid word)
      ((keep .x23 (by decide) (by decide) (by decide)).trans heapPointer)]
    simp [Execution.charge, Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

theorem chunk_run_registers (state finished : MachineState) (c : Nat) (hc : c < 4)
    (reachable : finished ∈ support (chunkRun state c)) :
    finished.getReg .x8 = state.getReg .x8 + state.getReg .x29 ∧
    ∀ reg, reg ≠ .x6 → reg ≠ .x8 → reg ≠ .x10 → reg ≠ .x12 →
      finished.getReg reg = state.getReg reg := by
  simp only [chunkRun, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reachable
  obtain ⟨hashed, reached, rfl⟩ := reachable
  have keep (reg : Reg) (n6 : reg ≠ .x6) (n10 : reg ≠ .x10) (n12 : reg ≠ .x12) :=
    chunk_leaves_from_register state hashed c 0 8 hc (by decide) reached reg n6 n10 n12
  refine ⟨?_, ?_⟩
  · simp only [chunkAdvanceState, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x8 ≠ .x0)]
    rw [keep .x8 (by decide) (by decide) (by decide), keep .x29 (by decide) (by decide) (by decide)]
  · intro reg n6 n8 n10 n12
    simp only [chunkAdvanceState, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm n8)]
    exact keep reg n6 n10 n12

theorem chunk_run_pc (state finished : MachineState) (c : Nat) (hc : c < 4)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * (39 + 161 * c)))
    (reachable : finished ∈ support (chunkRun state c)) :
    finished.pc = BitVec.ofNat 64 (4096 + 4 * (39 + 161 * (c + 1))) := by
  simp only [chunkRun, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reachable
  obtain ⟨hashed, reached, rfl⟩ := reachable
  have hpc := chunk_leaves_from_pc state hashed c 0 8 hc (by decide) (by simpa using pc) reached
  simp only [chunkAdvanceState, MachineState.setPC]
  rw [hpc]
  exact pc_add_steps _ 1 _ (by omega)

/-- One 8-leaf chunk plus `ADD x8, x8, x29`: 161 instructions, 385 cycles, 32 queries. -/
theorem commit_chunk (state : MachineState) (c : Nat) (hc : c < 4)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * (39 + 161 * c)))
    (r5 : state.getReg .x5 = 0) (r11 : state.getReg .x11 = 96) (r13 : state.getReg .x13 = 0)
    (slot : Nat) (slotPointer : state.getReg .x8 = BitVec.ofNat 64 slot)
    (slotAligned : slot % 8 = 0) (slotBound : slot + 2080 ≤ MEMORY_BYTES)
    (saltValid : ∀ word : Fin 128,
      accessValid (state.getReg .x18 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (heap : Nat) (heapPointer : state.getReg .x23 = BitVec.ofNat 64 heap)
    (heapAligned : heap % 8 = 0) (heapBound : heap + 1536 ≤ MEMORY_BYTES)
    (fuel : Nat) :
    execute (submission.image .commit) (161 + fuel) state true =
      (do let finished ← chunkRun state c
          let result ← execute (submission.image .commit) fuel finished true
          return result.charge 385 32) := by
  rw [show 161 + fuel = 20 * 8 + (1 + fuel) by omega,
    commit_chunk_leaves_from state c 0 8 hc (by decide) (by simpa using pc)
      r5 r11 r13 slot slotPointer slotAligned slotBound saltValid heap heapPointer heapAligned
      heapBound]
  simp only [chunkRun, bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro hashed reached
  have hpc : hashed.pc = BitVec.ofNat 64 (4096 + 4 * (199 + 161 * c)) := by
    have h := chunk_leaves_from_pc state hashed c 0 8 hc (by decide) (by simpa using pc) reached
    simpa [show 39 + 161 * c + 20 * (0 + 8) = 199 + 161 * c by omega] using h
  rw [commit_chunk_advance hashed c hc hpc]
  simp [Execution.charge, ← Nat.add_assoc]

theorem iter_chunks_from_registers (state finished : MachineState) (start remaining : Nat)
    (hbound : start + remaining ≤ 4) (r29 : state.getReg .x29 = 2048)
    (reachable : finished ∈ support (iterChunksFrom state start remaining)) :
    finished.getReg .x8 = state.getReg .x8 + BitVec.ofNat 64 (2048 * remaining) ∧
    ∀ reg, reg ≠ .x6 → reg ≠ .x8 → reg ≠ .x10 → reg ≠ .x12 →
      finished.getReg reg = state.getReg reg := by
  induction remaining generalizing state start with
  | zero =>
    simp only [iterChunksFrom, support_pure, Set.mem_singleton_iff] at reachable
    subst finished
    exact ⟨by simp, fun _ _ _ _ _ => rfl⟩
  | succ remaining ih =>
    simp only [iterChunksFrom, mem_support_bind_iff] at reachable
    obtain ⟨next, reached, rest⟩ := reachable
    have regs := chunk_run_registers state next start (by omega) reached
    have next29 : next.getReg .x29 = 2048 :=
      (regs.2 .x29 (by decide) (by decide) (by decide) (by decide)).trans r29
    have done := ih next (start + 1) (by omega) next29 rest
    refine ⟨?_, fun reg n6 n8 n10 n12 =>
      (done.2 reg n6 n8 n10 n12).trans (regs.2 reg n6 n8 n10 n12)⟩
    have h2048 : 2048 + 2048 * remaining = 2048 * (remaining + 1) := by
      rw [Nat.mul_succ, Nat.add_comm]
    rw [done.1, regs.1, r29, BitVec.add_assoc,
      show (2048 : Word) = BitVec.ofNat 64 2048 from rfl, ← BitVec.ofNat_add, h2048]

theorem iter_chunks_from_pc (state finished : MachineState) (start remaining : Nat)
    (hbound : start + remaining ≤ 4)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * (39 + 161 * start)))
    (reachable : finished ∈ support (iterChunksFrom state start remaining)) :
    finished.pc = BitVec.ofNat 64 (4096 + 4 * (39 + 161 * (start + remaining))) := by
  induction remaining generalizing state start with
  | zero =>
    simp only [iterChunksFrom, support_pure, Set.mem_singleton_iff] at reachable
    subst finished
    simpa using pc
  | succ remaining ih =>
    simp only [iterChunksFrom, mem_support_bind_iff] at reachable
    obtain ⟨next, reached, rest⟩ := reachable
    have nextPC := chunk_run_pc state next start (by omega) pc reached
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      ih next (start + 1) (by omega) nextPC rest

private theorem chunk_slot_bound_now (s r M : Nat) (h : s + 32 + 2048 * (r + 1) ≤ M) :
    s + 2080 ≤ M := by
  have h1 : 2048 ≤ 2048 * (r + 1) := Nat.le_mul_of_pos_right 2048 (Nat.succ_pos r)
  have h2 : s + 2080 = s + 32 + 2048 := by omega
  rw [h2]
  exact Nat.le_trans (Nat.add_le_add_left h1 (s + 32)) h

private theorem chunk_slot_bound_next (s r M : Nat) (h : s + 32 + 2048 * (r + 1) ≤ M) :
    s + 2048 + 32 + 2048 * r ≤ M := by
  have heq : s + 2048 + 32 + 2048 * r = s + 32 + 2048 * (r + 1) := by
    rw [Nat.mul_succ]; generalize 2048 * r = k; omega
  rwa [heq]

private theorem iter_slot_bound_start (s M : Nat) (h : s + 8224 ≤ M) :
    s + 32 + 2048 * 4 ≤ M := by
  have h1 : 32 + 2048 * 4 = 8224 := by decide
  rw [Nat.add_assoc, h1]
  exact h

theorem commit_iter_chunks_from (state : MachineState) (start remaining : Nat)
    (hbound : start + remaining ≤ 4)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * (39 + 161 * start)))
    (r29 : state.getReg .x29 = 2048)
    (r5 : state.getReg .x5 = 0) (r11 : state.getReg .x11 = 96) (r13 : state.getReg .x13 = 0)
    (slot : Nat) (slotPointer : state.getReg .x8 = BitVec.ofNat 64 slot)
    (slotAligned : slot % 8 = 0) (slotBound : slot + 32 + 2048 * remaining ≤ MEMORY_BYTES)
    (saltValid : ∀ word : Fin 128,
      accessValid (state.getReg .x18 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (heap : Nat) (heapPointer : state.getReg .x23 = BitVec.ofNat 64 heap)
    (heapAligned : heap % 8 = 0) (heapBound : heap + 1536 ≤ MEMORY_BYTES)
    (fuel : Nat) :
    execute (submission.image .commit) (161 * remaining + fuel) state true =
      (do let finished ← iterChunksFrom state start remaining
          let result ← execute (submission.image .commit) fuel finished true
          return result.charge (385 * remaining) (32 * remaining)) := by
  induction remaining generalizing state start slot with
  | zero => simp [iterChunksFrom, Execution.charge]
  | succ remaining ih =>
    have hstep : 161 * (remaining + 1) + fuel = 161 + (161 * remaining + fuel) := by
      rw [Nat.mul_succ, Nat.add_comm (161 * remaining) 161, Nat.add_assoc]
    rw [hstep,
      commit_chunk state start (by omega) pc r5 r11 r13 slot slotPointer slotAligned
        (chunk_slot_bound_now slot remaining MEMORY_BYTES slotBound)
        saltValid heap heapPointer heapAligned heapBound]
    simp only [iterChunksFrom, bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro next reached
    have regs := chunk_run_registers state next start (by omega) reached
    have nextSlot : next.getReg .x8 = BitVec.ofNat 64 (slot + 2048) := by
      rw [regs.1, slotPointer, r29]
      show BitVec.ofNat 64 slot + BitVec.ofNat 64 2048 = _
      rw [← BitVec.ofNat_add]
    have nextAligned : (slot + 2048) % 8 = 0 := by rw [Nat.add_mod, slotAligned]
    have nextPC := chunk_run_pc state next start (by omega) pc reached
    rw [ih next (start + 1) (by omega) nextPC
      ((regs.2 .x29 (by decide) (by decide) (by decide) (by decide)).trans r29)
      ((regs.2 .x5 (by decide) (by decide) (by decide) (by decide)).trans r5)
      ((regs.2 .x11 (by decide) (by decide) (by decide) (by decide)).trans r11)
      ((regs.2 .x13 (by decide) (by decide) (by decide) (by decide)).trans r13)
      (slot + 2048) nextSlot nextAligned
      (chunk_slot_bound_next slot remaining MEMORY_BYTES slotBound)
      (by intro word; rw [regs.2 .x18 (by decide) (by decide) (by decide) (by decide)]; exact saltValid word)
      ((regs.2 .x23 (by decide) (by decide) (by decide) (by decide)).trans heapPointer)]
    simp only [bind_assoc, pure_bind]
    apply bind_congr_of_forall_mem_support
    intro finished _
    apply bind_congr_of_forall_mem_support
    intro result _
    simp only [Execution.charge, Nat.mul_succ, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

set_option maxHeartbeats 1600000 in
/-- One complete 32-leaf iteration (four 8-leaf chunks + latch):
648 instructions, 1544 cycles, and 128 public queries. -/
theorem commit_position (state : MachineState) (pc : state.pc = 4252)
    (r29 : state.getReg .x29 = 2048)
    (r5 : state.getReg .x5 = 0) (r11 : state.getReg .x11 = 96) (r13 : state.getReg .x13 = 0)
    (slot : Nat) (slotPointer : state.getReg .x8 = BitVec.ofNat 64 slot)
    (slotAligned : slot % 8 = 0) (slotBound : slot + 8224 ≤ MEMORY_BYTES)
    (saltValid : ∀ word : Fin 128,
      accessValid (state.getReg .x18 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (heap : Nat) (heapPointer : state.getReg .x23 = BitVec.ofNat 64 heap)
    (heapAligned : heap % 8 = 0) (heapBound : heap + 1536 ≤ MEMORY_BYTES)
    (fuel : Nat) :
    execute (submission.image .commit) (648 + fuel) state true =
      (do let finished ← commitPositionRun state
          let result ← execute (submission.image .commit) fuel finished true
          return result.charge 1544 128) := by
  have hstep : 648 + fuel = 161 * 4 + (4 + fuel) := by omega
  rw [hstep,
    commit_iter_chunks_from state 0 4 (by decide) (by rw [pc]; rfl) r29 r5 r11 r13
      slot slotPointer slotAligned (iter_slot_bound_start slot MEMORY_BYTES slotBound)
      saltValid heap heapPointer heapAligned heapBound]
  simp only [commitPositionRun, bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro chunks reached
  have chunksPC : chunks.pc = 6828 :=
    (iter_chunks_from_pc state chunks 0 4 (by decide) (by rw [pc]; rfl) reached).trans rfl
  rw [commit_leaf_next_position chunks chunksPC]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro result _
  simp only [Execution.charge, ← Nat.add_assoc]

end CommitGolfCandidate
