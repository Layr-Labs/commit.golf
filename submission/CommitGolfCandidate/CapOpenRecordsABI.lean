import CommitGolfCandidate.CapOpenRecordsFrame
import CommitGolfCandidate.CapOpenIndexBytes
import CommitGolfCandidate.CapOpenInitialFacts

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

def capOpenAbiRecordContext : CapOpenRecordContext where
  roots := capProgram.layout.trapdoor
  salts := capProgram.layout.trapdoor+64*LENGTH
  indices := capProgram.layout.indices
  output := capProgram.layout.proof
  limit := capProgram.layout.proof+capProgram.sizes.proof
  rootAligned := by decide
  rootBound := by decide
  saltAligned := by decide
  saltBound := by decide
  indexHigh := by decide
  indexAligned := by decide
  outputAligned := by decide
  limitBound := by decide

def capOpenRequestedIndices (positions : Positions) : List Index :=
  positions.sort (· ≤ ·)

theorem cap_open_abi_record_windows (positions : Positions) :
    (capOpenRequestedIndices positions).length < 2^64 ∧
    capOpenAbiRecordContext.indices+8*(capOpenRequestedIndices positions).length+32 ≤
      capOpenAbiRecordContext.output ∧
    capOpenAbiRecordContext.output+544*(capOpenRequestedIndices positions).length ≤
      capOpenAbiRecordContext.limit := by
  have cardinal : positions.card ≤ LENGTH := by
    simpa [Index] using Finset.card_le_univ positions
  simp only [capOpenRequestedIndices, Finset.length_sort]
  norm_num [capOpenAbiRecordContext, capProgram, capExperimental, candidate, layout,
    sizes, trapdoorBytes, openingBytes, LENGTH, LOG_LENGTH, LEAF_SIZE, DIGEST_BYTES]
    at cardinal ⊢
  omega

theorem cap_open_abi_record_inputs
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions) :
    CapOpenRecordInputs capOpenAbiRecordContext (capOpenRequestedIndices positions)
      (capProgram.initialState .opening (trapdoor, positions)) := by
  intro ordinal inside
  simp only [capOpenRequestedIndices, Finset.length_sort] at inside
  exact cap_open_input_index trapdoor positions ordinal inside

theorem cap_open_abi_record_ready
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions)
    (positive : 0 < positions.card) :
    CapOpenRecordsReady capOpenAbiRecordContext (capOpenRequestedIndices positions)
      (capProgram.initialState .opening (trapdoor, positions)) positions.card
      (capOpenInitializedState (capProgram.initialState .opening (trapdoor, positions))) := by
  let initial := capProgram.initialState .opening (trapdoor, positions)
  have windows := cap_open_abi_record_windows positions
  have small : positions.card < 2^64 := by
    simpa only [capOpenRequestedIndices, Finset.length_sort] using windows.1
  have nonzero : BitVec.ofNat 64 positions.card ≠ (0 : Word) := by
    intro equal
    have value := congrArg BitVec.toNat equal
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small] at value
    change positions.card = 0 at value
    omega
  have count : initial.getReg .x16 = BitVec.ofNat 64 positions.card := rfl
  have currentPC : (capOpenInitializedState initial).pc = 4212 := by
    simp only [capOpenInitializedState, count, nonzero, ite_false, MachineState.setPC]
  have registers := cap_open_setup_registers initial
  refine ⟨?_, cap_open_initial_count trapdoor positions, ?_,
    cap_open_initial_root_base trapdoor positions,
    cap_open_initial_salt_base trapdoor positions,
    registers.2.2.2.2.1, registers.2.2.2.2.2.2.1,
    registers.2.2.2.2.2.2.2.2.1, ?_, ?_, ?_, ?_⟩
  · simp only [capOpenRequestedIndices, Finset.length_sort]
    exact Nat.le_refl _
  · simpa only [ne_of_gt positive, ite_false] using currentPC
  · simpa only [capOpenRequestedIndices, capOpenAbiRecordContext, Finset.length_sort, Nat.sub_self,
      Nat.mul_zero, Nat.add_zero] using cap_open_initial_index_pointer trapdoor positions
  · simpa only [capOpenRequestedIndices, capOpenAbiRecordContext, Finset.length_sort, Nat.sub_self,
      Nat.mul_zero, Nat.add_zero] using cap_open_initial_proof_pointer trapdoor positions
  · intro address high below
    exact cap_open_initial_byte_frame trapdoor positions _ address below
  · exact cap_open_setup_nonce_stride initial

end CommitGolfCandidate
