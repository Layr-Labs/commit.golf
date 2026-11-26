import CommitGolfCandidate.CommitLeaf

/-! Commitment execution: initialize the heap and salt pointers, sample all private
salts, hash the leaves, and build the parent nodes. These proofs use the submitted
instruction image and the challenge interpreter. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

private def commitLoad (reg : Reg) (high : BitVec 12) : List Instr :=
  [.ADDI reg .x0 0, .SLLI reg reg 11, .ADDI reg reg high,
   .SLLI reg reg 11, .ADDI reg reg 0, .SLLI reg reg 11, .ADDI reg reg 0]

private def commitSetupInstructions : List Instr :=
  [.ADDI .x8 .x10 4064, .ADDI .x26 .x11 0, .ADDI .x9 .x12 0] ++
  commitLoad .x6 384 ++ [.ADD .x18 .x9 .x6] ++
  commitLoad .x6 192 ++ [.ADD .x23 .x9 .x6, .ADDI .x5 .x0 2, .ADDI .x10 .x18 0] ++
  commitLoad .x11 96

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
    (commitSetupState state).getReg .x10 = state.getReg .x12 + 1610612736 ∧
    (commitSetupState state).getReg .x11 = 402653184 ∧
    (commitSetupState state).getReg .x18 = state.getReg .x12 + 1610612736 ∧
    (commitSetupState state).getReg .x23 = state.getReg .x12 + 805306368 ∧
    (commitSetupState state).getReg .x26 = state.getReg .x11 := by
  dsimp only [commitSetupState, commitSetupPrefix, commitSetupInstructions, commitLoad,
    List.append, List.take, List.foldl, execInstrBr, signExtend12,
    MachineState.getReg, MachineState.setReg, MachineState.setPC]
  simp [execInstrBr, signExtend12, MachineState.getReg, MachineState.setReg, MachineState.setPC]

theorem commit_setup_pc (state : MachineState) (pc : state.pc = 4096) :
    (commitSetupState state).pc = 4208 := by
  simp [commitSetupState, commitSetupPrefix, commitSetupInstructions, commitLoad,
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

private def commitReadyInstructions : List Instr :=
  [.ADDI .x20 .x0 0, .SLLI .x20 .x20 11, .ADDI .x20 .x20 2, .SLLI .x20 .x20 11,
   .ADDI .x20 .x20 0, .SLLI .x20 .x20 11, .ADDI .x20 .x20 0,
   .ADDI .x5 .x0 0, .ADDI .x11 .x0 96, .ADDI .x13 .x0 0]

private def commitReadyPrefix (state : MachineState) (count : Nat) : MachineState :=
  (commitReadyInstructions.take count).foldl execInstrBr state

def commitReadyState (state : MachineState) : MachineState := commitReadyPrefix state 10

/-- Initialize the pair counter (n/2) and the constant syscall arguments of the
in-place leaf calls after sampling salts. -/
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
  simp [commitReadyState, commitReadyPrefix, commitReadyInstructions, execInstrBr, pc, MachineState.setPC]

theorem commit_ready_counters (state : MachineState) :
    (commitReadyState state).getReg .x20 = 8388608 ∧
    (commitReadyState state).getReg .x5 = 0 ∧ (commitReadyState state).getReg .x11 = 96 ∧
    (commitReadyState state).getReg .x13 = 0 := by
  simp [commitReadyState, commitReadyPrefix, commitReadyInstructions, execInstrBr,
    signExtend12, MachineState.getReg, MachineState.setReg, MachineState.setPC]

theorem commit_ready_register (state : MachineState) (reg : Reg)
    (notCounter : reg ≠ .x20) (not5 : reg ≠ .x5)
    (not11 : reg ≠ .x11) (not13 : reg ≠ .x13) :
    (commitReadyState state).getReg reg = state.getReg reg := by
  cases reg <;> simp_all [commitReadyState, commitReadyPrefix, commitReadyInstructions,
    execInstrBr, signExtend12, MachineState.getReg, MachineState.setReg, MachineState.setPC]

/-- The commitment root copy (instructions 124..131): four words from x21 to x26. -/
private def commitCopyInstructions (_start : Nat) : List Instr :=
  [.LD .x6 .x21 0, .SD .x26 .x6 0, .LD .x6 .x21 8, .SD .x26 .x6 8,
   .LD .x6 .x21 16, .SD .x26 .x6 16, .LD .x6 .x21 24, .SD .x26 .x6 24]

private def commitCopyPrefix (state : MachineState) (start count : Nat) : MachineState :=
  ((commitCopyInstructions start).take count).foldl execInstrBr state

def commitCopyState (state : MachineState) (start : Nat) : MachineState := commitCopyPrefix state start 8

/-- Expose the decoded root copy instructions for memory refinement. -/
theorem commit_copy_expansion (state : MachineState) (start : Nat) :
    commitCopyState state start =
      ([.LD .x6 .x21 0, .SD .x26 .x6 0, .LD .x6 .x21 8, .SD .x26 .x6 8,
        .LD .x6 .x21 16, .SD .x26 .x6 16, .LD .x6 .x21 24, .SD .x26 .x6 24] :
        List Instr).foldl execInstrBr state := rfl

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

set_option maxHeartbeats 4000000 in
/-- The final root copy takes eight ordinary instructions. The hypotheses cover every
source and destination access. -/
theorem commit_copy (state : MachineState) (start : Nat)
    (location : start = 124)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * start))
    (sourceValid : ∀ word : Fin 4,
      accessValid (state.getReg .x21 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (destinationValid : ∀ word : Fin 4,
      accessValid (state.getReg .x26 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .commit) (8 + fuel) state allowCoins =
      (do let result ← execute (submission.image .commit) fuel (commitCopyState state start) allowCoins
          return result.charge 8 0) := by
  subst location
  apply execute_unit_steps (states := commitCopyPrefix state 124)
  intro i hi
  refine ⟨.base (((commitCopyInstructions 124)[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply commit_fetch _ (124 + i) _ (by omega)
    · interval_cases i <;>
        simp [commitCopyPrefix, commitCopyInstructions, execInstrBr, pc, MachineState.setPC]
    · interval_cases i <;> rfl
  · have sourceReg := commit_copy_prefix_register state 124 i (by omega) .x21 (by decide)
    have destinationReg := commit_copy_prefix_register state 124 i (by omega) .x26 (by decide)
    have s0 := sourceValid ⟨0, by decide⟩
    have s1 := sourceValid ⟨1, by decide⟩
    have s2 := sourceValid ⟨2, by decide⟩
    have s3 := sourceValid ⟨3, by decide⟩
    have d0 := destinationValid ⟨0, by decide⟩
    have d1 := destinationValid ⟨1, by decide⟩
    have d2 := destinationValid ⟨2, by decide⟩
    have d3 := destinationValid ⟨3, by decide⟩
    have valid : memoryArgumentsValid (commitCopyPrefix state 124 i)
        (((commitCopyInstructions 124)[i]?).getD .EBREAK) = true := by
      interval_cases i <;>
        simp (config := { decide := true }) only [commitCopyInstructions,
          List.getElem?_cons_zero, List.getElem?_cons_succ,
          Option.getD_some, memoryArgumentsValid, memAccess, signExtend12] <;>
        (try simp only [sourceReg, destinationReg]) <;>
        first | exact s0 | exact s1 | exact s2 | exact s3 |
          exact d0 | exact d1 | exact d2 | exact d3
    interval_cases i <;>
      simp only [commitCopyInstructions, List.getElem?_cons_zero, List.getElem?_cons_succ,
        Option.getD_some] at valid ⊢ <;>
      simp only [ordinaryStep, valid, ↓reduceIte] <;> rfl
  · interval_cases i <;> rfl

/-- Salt copy of lane `k` (instructions 39+19k .. 45+19k): three words of the packed
24-byte salt at x18+24k into the lane's state slot x8+256k, then a zero fourth word, so
the slot holds the 32-byte leaf state `salt | 0^64`. -/
def commitSaltInstructions (k : Nat) : List Instr :=
  [.LD .x6 .x18 (BitVec.ofNat 12 (24*k)), .SD .x8 .x6 (BitVec.ofNat 12 (256*k)),
   .LD .x6 .x18 (BitVec.ofNat 12 (24*k+8)), .SD .x8 .x6 (BitVec.ofNat 12 (256*k+8)),
   .LD .x6 .x18 (BitVec.ofNat 12 (24*k+16)), .SD .x8 .x6 (BitVec.ofNat 12 (256*k+16)),
   .SD .x8 .x0 (BitVec.ofNat 12 (256*k+24))]

private def commitSaltPrefix (state : MachineState) (k count : Nat) : MachineState :=
  ((commitSaltInstructions k).take count).foldl execInstrBr state

def commitSaltState (state : MachineState) (k : Nat) : MachineState := commitSaltPrefix state k 7

theorem commit_salt_expansion (state : MachineState) (k : Nat) :
    commitSaltState state k = (commitSaltInstructions k).foldl execInstrBr state := rfl

private theorem commit_salt_prefix_register (state : MachineState) (k count : Nat)
    (bounded : count ≤ 7) (reg : Reg) (notTemporary : reg ≠ .x6) :
    (commitSaltPrefix state k count).getReg reg = state.getReg reg := by
  have memRegister (state : MachineState) (address value : Word) (reg : Reg) :
      (state.setMem address value).getReg reg = state.getReg reg := by cases reg <;> rfl
  interval_cases count <;>
    simp only [commitSaltPrefix, commitSaltInstructions, List.take, List.foldl, execInstrBr,
      MachineState.getReg_setPC, memRegister,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm notTemporary)]

theorem commit_salt_register (state : MachineState) (k : Nat) (reg : Reg) (notTemporary : reg ≠ .x6) :
    (commitSaltState state k).getReg reg = state.getReg reg :=
  commit_salt_prefix_register state k 7 (by decide) reg notTemporary

theorem commit_salt_pc (state : MachineState) (k : Nat) :
    (commitSaltState state k).pc = state.pc + 28 := by
  simp [commitSaltState, commitSaltPrefix, commitSaltInstructions, execInstrBr,
    MachineState.setPC, BitVec.add_assoc]

set_option hygiene false in
local macro "commit_salt_tac " n:num : tactic => `(tactic| (
  apply execute_unit_steps (states := commitSaltPrefix state $n)
  intro i hi
  refine ⟨.base (((commitSaltInstructions $n)[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply commit_fetch _ (39 + 19 * $n + i) _ (by omega)
    · interval_cases i <;>
        simp [commitSaltPrefix, commitSaltInstructions, execInstrBr, pc, MachineState.setPC]
    · interval_cases i <;> rfl
  · have sourceReg := commit_salt_prefix_register state $n i (by omega) .x18 (by decide)
    have destinationReg := commit_salt_prefix_register state $n i (by omega) .x8 (by decide)
    have s0 := sourceValid ⟨0, by decide⟩
    have s1 := sourceValid ⟨1, by decide⟩
    have s2 := sourceValid ⟨2, by decide⟩
    have d0 := destinationValid ⟨0, by decide⟩
    have d1 := destinationValid ⟨1, by decide⟩
    have d2 := destinationValid ⟨2, by decide⟩
    have d3 := destinationValid ⟨3, by decide⟩
    have valid : memoryArgumentsValid (commitSaltPrefix state $n i)
        (((commitSaltInstructions $n)[i]?).getD .EBREAK) = true := by
      interval_cases i <;>
        simp (config := { decide := true }) only [commitSaltInstructions,
          List.getElem?_cons_zero, List.getElem?_cons_succ,
          Option.getD_some, memoryArgumentsValid, memAccess, signExtend12] <;>
        (try simp only [sourceReg, destinationReg]) <;>
        first | exact s0 | exact s1 | exact s2 |
          exact d0 | exact d1 | exact d2 | exact d3
    interval_cases i <;>
      simp only [commitSaltInstructions, List.getElem?_cons_zero, List.getElem?_cons_succ,
        Option.getD_some] at valid ⊢ <;>
      simp only [ordinaryStep, valid, ↓reduceIte] <;> rfl
  · interval_cases i <;> rfl))

set_option maxHeartbeats 4000000 in
/-- The salt copy of lane `k` takes seven ordinary instructions. The hypotheses cover
every source and destination access. -/
theorem commit_salt_copy (state : MachineState) (k : Nat) (hk : k < 2)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * (39 + 19 * k)))
    (sourceValid : ∀ word : Fin 3,
      accessValid (state.getReg .x18 + BitVec.ofNat 64 (24 * k + 8 * word.val)) 8 = true)
    (destinationValid : ∀ word : Fin 4,
      accessValid (state.getReg .x8 + BitVec.ofNat 64 (256 * k + 8 * word.val)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .commit) (7 + fuel) state allowCoins =
      (do let result ← execute (submission.image .commit) fuel (commitSaltState state k) allowCoins
          return result.charge 7 0) := by
  interval_cases k
  · commit_salt_tac 0
  · commit_salt_tac 1

private theorem salt_getReg_setMem (state : MachineState) (address value : Word) (reg : Reg) :
    (state.setMem address value).getReg reg = state.getReg reg := by
  cases reg <;> rfl

private theorem salt_getMem_setMem (state : MachineState) (address value query : Word) :
    (state.setMem address value).getMem query =
      if query = address then value else state.getMem query := by
  simp [MachineState.getMem, MachineState.setMem]

/-- Outside the four destination words, the salt copy leaves memory unchanged. -/
theorem commit_salt_memory_outside (state : MachineState) (k : Nat) (hk : k < 2) (address : Word)
    (outside : ∀ word : Fin 4,
      address ≠ state.getReg .x8 + BitVec.ofNat 64 (256 * k + 8 * word.val)) :
    (commitSaltState state k).getMem address = state.getMem address := by
  have h0 := outside ⟨0, by decide⟩
  have h1 := outside ⟨1, by decide⟩
  have h2 := outside ⟨2, by decide⟩
  have h3 := outside ⟨3, by decide⟩
  interval_cases k <;>
  simp [commitSaltState, commitSaltPrefix, commitSaltInstructions,
    execInstrBr, MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq,
    salt_getReg_setMem, salt_getMem_setMem, signExtend12] at h0 h1 h2 h3 ⊢ <;>
  simp [h0, h1, h2, h3]

/-- With disjoint source and destination words, the salt copy writes the three source
words to the first three destination words. -/
theorem commit_salt_memory (state : MachineState) (k : Nat) (hk : k < 2)
    (separated : ∀ (source : Fin 3) (destination : Fin 4),
      state.getReg .x18 + BitVec.ofNat 64 (24 * k + 8 * source.val) ≠
        state.getReg .x8 + BitVec.ofNat 64 (256 * k + 8 * destination.val)) (word : Fin 3) :
    (commitSaltState state k).getMem (state.getReg .x8 + BitVec.ofNat 64 (256 * k + 8 * word.val)) =
      state.getMem (state.getReg .x18 + BitVec.ofNat 64 (24 * k + 8 * word.val)) := by
  have h10 := separated ⟨1, by decide⟩ ⟨0, by decide⟩
  have h20 := separated ⟨2, by decide⟩ ⟨0, by decide⟩
  have h21 := separated ⟨2, by decide⟩ ⟨1, by decide⟩
  interval_cases k <;>
  simp [signExtend12] at h10 h20 h21 <;>
  fin_cases word <;>
    simp [commitSaltState, commitSaltPrefix, commitSaltInstructions,
      execInstrBr, MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq,
      salt_getReg_setMem, salt_getMem_setMem, signExtend12, h10, h20, h21]

/-- The salt copy clears the fourth word of the lane's state slot. -/
theorem commit_salt_memory_zero (state : MachineState) (k : Nat) (hk : k < 2) :
    (commitSaltState state k).getMem (state.getReg .x8 + BitVec.ofNat 64 (256 * k + 8 * 3)) = 0 := by
  interval_cases k <;>
    simp [commitSaltState, commitSaltPrefix, commitSaltInstructions,
      execInstrBr, MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq,
      salt_getReg_setMem, salt_getMem_setMem, signExtend12] <;> rfl

/-- Outside the four destination words, the root copy leaves memory unchanged. -/
theorem commit_copy_memory_outside (state : MachineState) (start : Nat) (address : Word)
    (outside : ∀ word : Fin 4,
      address ≠ state.getReg .x26 + BitVec.ofNat 64 (8 * word.val)) :
    (commitCopyState state start).getMem address = state.getMem address := by
  have h0 := outside ⟨0, by decide⟩
  have h1 := outside ⟨1, by decide⟩
  have h2 := outside ⟨2, by decide⟩
  have h3 := outside ⟨3, by decide⟩
  have a0 : address ≠ state.getReg .x26 := by simpa using h0
  have a1 : address ≠ state.getReg .x26 + 8#64 := h1
  have a2 : address ≠ state.getReg .x26 + 16#64 := h2
  have a3 : address ≠ state.getReg .x26 + 24#64 := h3
  simp [commitCopyState, commitCopyPrefix, commitCopyInstructions,
    execInstrBr, MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq,
    salt_getReg_setMem, salt_getMem_setMem, signExtend12, a0, a1, a2, a3]

/-- With disjoint source and destination words, the root copy writes all four original
source words to their corresponding destination addresses. -/
theorem commit_copy_memory (state : MachineState) (start : Nat)
    (separated : ∀ source destination : Fin 4,
      state.getReg .x21 + BitVec.ofNat 64 (8 * source.val) ≠
        state.getReg .x26 + BitVec.ofNat 64 (8 * destination.val)) (word : Fin 4) :
    (commitCopyState state start).getMem (state.getReg .x26 + BitVec.ofNat 64 (8 * word.val)) =
      state.getMem (state.getReg .x21 + BitVec.ofNat 64 (8 * word.val)) := by
  have h10 : state.getReg .x21 + 8#64 ≠ state.getReg .x26 := by
    simpa using separated ⟨1, by decide⟩ ⟨0, by decide⟩
  have h20 : state.getReg .x21 + 16#64 ≠ state.getReg .x26 := by
    simpa using separated ⟨2, by decide⟩ ⟨0, by decide⟩
  have h21 : state.getReg .x21 + 16#64 ≠ state.getReg .x26 + 8#64 :=
    separated ⟨2, by decide⟩ ⟨1, by decide⟩
  have h30 : state.getReg .x21 + 24#64 ≠ state.getReg .x26 := by
    simpa using separated ⟨3, by decide⟩ ⟨0, by decide⟩
  have h31 : state.getReg .x21 + 24#64 ≠ state.getReg .x26 + 8#64 :=
    separated ⟨3, by decide⟩ ⟨1, by decide⟩
  have h32 : state.getReg .x21 + 24#64 ≠ state.getReg .x26 + 16#64 :=
    separated ⟨3, by decide⟩ ⟨2, by decide⟩
  fin_cases word <;>
    simp [commitCopyState, commitCopyPrefix, commitCopyInstructions,
      execInstrBr, MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq,
      salt_getReg_setMem, signExtend12,
      h10, h20, h21, h30, h31, h32]

/-- Advance the slot, salt and heap pointers by one pair; loop while pairs remain. Both
outcomes of the branch are represented. -/
def commitPositionNextState (state : MachineState) : MachineState :=
  ((((state.setReg .x8 (state.getReg .x8 + 512)).setReg .x18 (state.getReg .x18 + 48)).setReg
    .x23 (state.getReg .x23 + 96)).setReg .x20 (state.getReg .x20 - 1)).setPC
      (if state.getReg .x20 - 1 = 0 then 4424 else 4252)

private def commitNextInstructions : List Instr :=
  [.ADDI .x8 .x8 512, .ADDI .x18 .x18 48, .ADDI .x23 .x23 96, .ADDI .x20 .x20 4095]

private def commitNextPrefix (state : MachineState) (count : Nat) : MachineState :=
  (commitNextInstructions.take count).foldl execInstrBr state

theorem commit_leaf_next_position (state : MachineState) (pc : state.pc = 4404) (fuel : Nat) :
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
    · apply commit_fetch _ (77 + i) _ (by omega)
      · interval_cases i <;> simp [commitNextPrefix, commitNextInstructions, execInstrBr, pc, MachineState.setPC]
      · interval_cases i <;> rfl
    · interval_cases i <;> rfl
    · interval_cases i <;> rfl
  have fetched : fetch (submission.image .commit) (commitNextPrefix state 4) =
      some (.base (.BNE .x20 .x0 8024)) := by
    apply commit_fetch _ 81 _ (by decide)
    · simp [commitNextPrefix, commitNextInstructions, execInstrBr, pc, MachineState.setPC]
    · rfl
  have stepped : ordinaryStep (commitNextPrefix state 4) (.base (.BNE .x20 .x0 8024)) =
      some (commitPositionNextState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend13, signExtend12,
      commitNextPrefix, commitNextInstructions, commitPositionNextState, MachineState.getReg,
      MachineState.setReg, MachineState.setPC, pc, BitVec.sub_eq_add_neg]
    split <;> simp_all
  rw [show 5 + fuel = 4 + (fuel + 1) by omega, setup,
    execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  simp [instructionCycles, Execution.charge, ← Nat.add_assoc]

/-- Query of in-place call `j` of lane `k` on the current state. -/
abbrev chainQuery (state : MachineState) (k j : Nat) : PublicSpec.Domain :=
  .inl (readBuffer state (chainSource state k j).toNat 96)

/-- The four in-place calls of lane `k`. -/
def laneRun (state : MachineState) (k : Nat) : OracleComp World MachineState := do
  let a0 ← World.query (.inr (chainQuery state k 0))
  let s1 := chainCallState state k 0 a0
  let a1 ← World.query (.inr (chainQuery s1 k 1))
  let s2 := chainCallState s1 k 1 a1
  let a2 ← World.query (.inr (chainQuery s2 k 2))
  let s3 := chainCallState s2 k 2 a2
  let a3 ← World.query (.inr (chainQuery s3 k 3))
  return chainCallState s3 k 3 a3

/-- The exact state distribution after one pair iteration: salt copy and four calls for
lane 0, salt copy and four calls for lane 1, then advance. -/
def commitPositionRun (state : MachineState) : OracleComp World MachineState := do
  let first ← laneRun (commitSaltState state 0) 0
  let second ← laneRun (commitSaltState first 1) 1
  return commitPositionNextState second

/-- Register facts preserved through one call. -/
private theorem chain_step_facts (s : MachineState) (k j : Nat) (hk : k < 2) (hj : j < 4)
    (answer : BitVec 256)
    (slot heap : Nat) (slotPointer : s.getReg .x8 = BitVec.ofNat 64 slot)
    (heapPointer : s.getReg .x23 = BitVec.ofNat 64 heap)
    (r5 : s.getReg .x5 = 0) (r11 : s.getReg .x11 = 96) (r13 : s.getReg .x13 = 0) :
    (chainCallState s k j answer).getReg .x8 = BitVec.ofNat 64 slot ∧
    (chainCallState s k j answer).getReg .x23 = BitVec.ofNat 64 heap ∧
    (chainCallState s k j answer).getReg .x5 = 0 ∧
    (chainCallState s k j answer).getReg .x11 = 96 ∧
    (chainCallState s k j answer).getReg .x13 = 0 ∧
    (chainCallState s k j answer).pc = s.pc + 12 :=
  ⟨(chain_call_register s k j hk hj answer .x8 (by decide) (by decide)).trans slotPointer,
   (chain_call_register s k j hk hj answer .x23 (by decide) (by decide)).trans heapPointer,
   (chain_call_register s k j hk hj answer .x5 (by decide) (by decide)).trans r5,
   (chain_call_register s k j hk hj answer .x11 (by decide) (by decide)).trans r11,
   (chain_call_register s k j hk hj answer .x13 (by decide) (by decide)).trans r13,
   chain_call_pc s k j hk hj answer⟩

theorem pc_add_twelve (n m : Nat) (h : m = n + 3) :
    BitVec.ofNat 64 (4096 + 4*n) + 12 = BitVec.ofNat 64 (4096 + 4*m) := by
  rw [h]
  conv_rhs => rw [show 4096 + 4*(n+3) = (4096+4*n) + 12 by omega, BitVec.ofNat_add]
  rfl

set_option maxHeartbeats 1600000 in
/-- The four in-place calls of lane `k`: twelve instructions, forty cycles, four queries. -/
theorem commit_lane (state : MachineState) (k : Nat) (hk : k < 2)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * (46 + 19*k)))
    (r5 : state.getReg .x5 = 0) (r11 : state.getReg .x11 = 96) (r13 : state.getReg .x13 = 0)
    (slot : Nat) (slotPointer : state.getReg .x8 = BitVec.ofNat 64 slot)
    (slotAligned : slot % 8 = 0) (slotBound : slot + 544 ≤ MEMORY_BYTES)
    (heap : Nat) (heapPointer : state.getReg .x23 = BitVec.ofNat 64 heap)
    (heapAligned : heap % 8 = 0) (heapBound : heap + 64 ≤ MEMORY_BYTES)
    (fuel : Nat) :
    execute (submission.image .commit) (12 + fuel) state true =
      (do let finished ← laneRun state k
          let result ← execute (submission.image .commit) fuel finished true
          return result.charge 40 4) := by
  have pc0 : state.pc = BitVec.ofNat 64 (4096 + 4 * (46 + 19*k + 3*0)) := by
    rw [pc, show 46 + 19*k + 3*0 = 46 + 19*k by omega]
  have q0 := chain_call_valid state k 0 hk (by decide) slot heap slotPointer slotAligned slotBound
    heapPointer heapAligned heapBound
  rw [show 12 + fuel = 3 + (3 + (3 + (3 + fuel))) by omega,
    commit_chain_call state k 0 hk (by decide) pc0 r5 r11 r13 q0.1 q0.2.1 q0.2.2.1 q0.2.2.2]
  simp only [laneRun, bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro a0 _
  let s1 := chainCallState state k 0 a0
  have f1 := chain_step_facts state k 0 hk (by decide) a0 slot heap slotPointer heapPointer r5 r11 r13
  have s1pc : s1.pc = BitVec.ofNat 64 (4096 + 4 * (46 + 19*k + 3*1)) := by
    rw [f1.2.2.2.2.2, pc0, pc_add_twelve (46 + 19*k + 3*0) (46 + 19*k + 3*1) (by omega)]
  have q1 := chain_call_valid s1 k 1 hk (by decide) slot heap f1.1 slotAligned slotBound f1.2.1
    heapAligned heapBound
  rw [commit_chain_call s1 k 1 hk (by decide) s1pc f1.2.2.1 f1.2.2.2.1 f1.2.2.2.2.1
    q1.1 q1.2.1 q1.2.2.1 q1.2.2.2]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro a1 _
  let s2 := chainCallState s1 k 1 a1
  have f2 := chain_step_facts s1 k 1 hk (by decide) a1 slot heap f1.1 f1.2.1 f1.2.2.1 f1.2.2.2.1
    f1.2.2.2.2.1
  have s2pc : s2.pc = BitVec.ofNat 64 (4096 + 4 * (46 + 19*k + 3*2)) := by
    rw [f2.2.2.2.2.2, s1pc, pc_add_twelve (46 + 19*k + 3*1) (46 + 19*k + 3*2) (by omega)]
  have q2 := chain_call_valid s2 k 2 hk (by decide) slot heap f2.1 slotAligned slotBound f2.2.1
    heapAligned heapBound
  rw [commit_chain_call s2 k 2 hk (by decide) s2pc f2.2.2.1 f2.2.2.2.1 f2.2.2.2.2.1
    q2.1 q2.2.1 q2.2.2.1 q2.2.2.2]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro a2 _
  let s3 := chainCallState s2 k 2 a2
  have f3 := chain_step_facts s2 k 2 hk (by decide) a2 slot heap f2.1 f2.2.1 f2.2.2.1 f2.2.2.2.1
    f2.2.2.2.2.1
  have s3pc : s3.pc = BitVec.ofNat 64 (4096 + 4 * (46 + 19*k + 3*3)) := by
    rw [f3.2.2.2.2.2, s2pc, pc_add_twelve (46 + 19*k + 3*2) (46 + 19*k + 3*3) (by omega)]
  have q3 := chain_call_valid s3 k 3 hk (by decide) slot heap f3.1 slotAligned slotBound f3.2.1
    heapAligned heapBound
  rw [commit_chain_call s3 k 3 hk (by decide) s3pc f3.2.2.1 f3.2.2.2.1 f3.2.2.2.2.1
    q3.1 q3.2.1 q3.2.2.1 q3.2.2.2]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro a3 _
  simp [Execution.charge, ← Nat.add_assoc]
  rfl

theorem lane_run_support (state finished : MachineState) (k : Nat)
    (reachable : finished ∈ support (laneRun state k)) :
    ∃ a0 a1 a2 a3, finished = chainCallState (chainCallState (chainCallState (chainCallState
      state k 0 a0) k 1 a1) k 2 a2) k 3 a3 := by
  simp only [laneRun, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reachable
  obtain ⟨a0, _, a1, _, a2, _, a3, _, rfl⟩ := reachable
  exact ⟨a0, a1, a2, a3, rfl⟩

theorem lane_run_register (state finished : MachineState) (k : Nat) (hk : k < 2)
    (reachable : finished ∈ support (laneRun state k))
    (reg : Reg) (n10 : reg ≠ .x10) (n12 : reg ≠ .x12) :
    finished.getReg reg = state.getReg reg := by
  obtain ⟨a0, a1, a2, a3, rfl⟩ := lane_run_support state finished k reachable
  rw [chain_call_register _ k 3 hk (by decide) _ reg n10 n12, chain_call_register _ k 2 hk (by decide) _ reg n10 n12,
    chain_call_register _ k 1 hk (by decide) _ reg n10 n12, chain_call_register _ k 0 hk (by decide) _ reg n10 n12]

theorem lane_run_pc (state finished : MachineState) (k : Nat) (hk : k < 2)
    (reachable : finished ∈ support (laneRun state k)) :
    finished.pc = state.pc + 48 := by
  obtain ⟨a0, a1, a2, a3, rfl⟩ := lane_run_support state finished k reachable
  rw [chain_call_pc _ k 3 hk (by decide), chain_call_pc _ k 2 hk (by decide),
    chain_call_pc _ k 1 hk (by decide), chain_call_pc _ k 0 hk (by decide)]
  simp only [BitVec.add_assoc]
  rfl

set_option maxHeartbeats 1600000 in
/-- One complete commitment pair iteration: for each lane store its salt state in front
of the leaf's message, hash 2048 bits in place with four direct calls, the last writing
the lane's heap slot; then advance. 43 instructions, 99 cycles and eight public queries. -/
theorem commit_position (state : MachineState) (pc : state.pc = 4252)
    (r5 : state.getReg .x5 = 0) (r11 : state.getReg .x11 = 96) (r13 : state.getReg .x13 = 0)
    (slot : Nat) (slotPointer : state.getReg .x8 = BitVec.ofNat 64 slot)
    (slotAligned : slot % 8 = 0) (slotBound : slot + 544 ≤ MEMORY_BYTES)
    (saltValid : ∀ word : Fin 6,
      accessValid (state.getReg .x18 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (heap : Nat) (heapPointer : state.getReg .x23 = BitVec.ofNat 64 heap)
    (heapAligned : heap % 8 = 0) (heapBound : heap + 64 ≤ MEMORY_BYTES)
    (fuel : Nat) :
    execute (submission.image .commit) (43 + fuel) state true =
      (do let finished ← commitPositionRun state
          let result ← execute (submission.image .commit) fuel finished true
          return result.charge 99 8) := by
  have mem : MEMORY_BYTES = 2^36 := rfl
  have slotValid (offset : Nat) (inside : offset + 32 ≤ 544) (offsetAligned : offset % 8 = 0) :
      ∀ word : Fin 4,
      accessValid (state.getReg .x8 + BitVec.ofNat 64 (offset + 8 * word.val)) 8 = true := by
    intro word
    have bound : slot + (offset + 8 * word.val) + 8 ≤ MEMORY_BYTES := by have := word.isLt; omega
    simp only [accessValid, rangeValid, slotPointer, pointer_offset_nat slot (offset + 8 * word.val) (by omega),
      Bool.and_eq_true, decide_eq_true_eq]
    constructor <;> omega
  let s0 := commitSaltState state 0
  have s0reg (reg : Reg) (h : reg ≠ .x6) : s0.getReg reg = state.getReg reg :=
    commit_salt_register state 0 reg h
  have s0pc : s0.pc = BitVec.ofNat 64 (4096 + 4 * (46 + 19*0)) := by
    rw [commit_salt_pc, pc]; rfl
  rw [show 43 + fuel = 7 + (12 + (7 + (12 + (5 + fuel)))) by omega,
    commit_salt_copy state 0 (by decide) (by rw [pc]; rfl)
      (by intro word; simpa using saltValid ⟨word.val, by omega⟩)
      (by simpa using slotValid 0 (by decide) (by decide)),
    commit_lane s0 0 (by decide) s0pc ((s0reg .x5 (by decide)).trans r5)
      ((s0reg .x11 (by decide)).trans r11) ((s0reg .x13 (by decide)).trans r13)
      slot ((s0reg .x8 (by decide)).trans slotPointer) slotAligned slotBound
      heap ((s0reg .x23 (by decide)).trans heapPointer) heapAligned heapBound]
  simp only [commitPositionRun, bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro first reachedFirst
  have firstReg (reg : Reg) (n10 : reg ≠ .x10) (n12 : reg ≠ .x12) (n6 : reg ≠ .x6) :
      first.getReg reg = state.getReg reg :=
    (lane_run_register s0 first 0 (by decide) reachedFirst reg n10 n12).trans (s0reg reg n6)
  have firstPC : first.pc = BitVec.ofNat 64 (4096 + 4 * (39 + 19 * 1)) := by
    rw [lane_run_pc s0 first 0 (by decide) reachedFirst, s0pc]; rfl
  let t0 := commitSaltState first 1
  have t0reg (reg : Reg) (h : reg ≠ .x6) : t0.getReg reg = first.getReg reg :=
    commit_salt_register first 1 reg h
  have t0pc : t0.pc = BitVec.ofNat 64 (4096 + 4 * (46 + 19*1)) := by
    rw [commit_salt_pc, firstPC]; rfl
  rw [commit_salt_copy first 1 (by decide) firstPC
      (by
        intro word
        show accessValid (first.getReg .x18 + BitVec.ofNat 64 (24 * 1 + 8 * word.val)) 8 = true
        rw [firstReg .x18 (by decide) (by decide) (by decide)]
        simpa [show 24 * 1 + 8 * word.val = 8 * (word.val + 3) by omega] using
          saltValid ⟨word.val + 3, by omega⟩)
      (by
        intro word
        show accessValid (first.getReg .x8 + BitVec.ofNat 64 (256 * 1 + 8 * word.val)) 8 = true
        rw [firstReg .x8 (by decide) (by decide) (by decide)]
        exact slotValid 256 (by decide) (by decide) word),
    commit_lane t0 1 (by decide) t0pc
      ((t0reg .x5 (by decide)).trans (firstReg .x5 (by decide) (by decide) (by decide) |>.trans r5))
      ((t0reg .x11 (by decide)).trans (firstReg .x11 (by decide) (by decide) (by decide) |>.trans r11))
      ((t0reg .x13 (by decide)).trans (firstReg .x13 (by decide) (by decide) (by decide) |>.trans r13))
      slot ((t0reg .x8 (by decide)).trans (firstReg .x8 (by decide) (by decide) (by decide) |>.trans slotPointer))
      slotAligned slotBound
      heap ((t0reg .x23 (by decide)).trans (firstReg .x23 (by decide) (by decide) (by decide) |>.trans heapPointer))
      heapAligned heapBound]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro second reachedSecond
  have secondPC : second.pc = 4404 := by
    rw [lane_run_pc t0 second 1 (by decide) reachedSecond, t0pc]; rfl
  rw [commit_leaf_next_position _ secondPC]
  simp [Execution.charge, ← Nat.add_assoc]

end CommitGolfCandidate
