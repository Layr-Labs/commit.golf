import CommitGolfCandidate.CapCheckInitialFacts
import CommitGolfCandidate.CapCheckRetainedIndex

/-! ABI admission of the current checker record. The initial minimum-length
gate reserves all 544-byte lower records, including their salts. Source values
and indices use their distinct fixed ABI ranges. Bounds are natural numbers
before their addresses are converted to words. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

theorem cap_check_record_bounds (input : CheckInput) (ordinal : Nat)
    (present : ordinal < input.positions.card)
    (admitted : input.proof.length ≤ capProgram.sizes.proof)
    (enough : 544 * input.positions.card ≤ input.proof.length) :
    capProgram.layout.indices + 8*ordinal + 8 ≤ MEMORY_BYTES ∧
    capProgram.layout.values + 256*ordinal + 256 ≤ MEMORY_BYTES ∧
    capProgram.layout.proof + 544*ordinal + 544 ≤
      capProgram.layout.proof + input.proof.length ∧
    capProgram.layout.proof + input.proof.length ≤ MEMORY_BYTES := by
  have cardinal : input.positions.card ≤ LENGTH := by
    simpa [Index] using Finset.card_le_univ input.positions
  have proofBound := (cap_check_loader_bounds input admitted).1
  refine ⟨?_, ?_, by omega, proofBound⟩
  all_goals
    norm_num [capProgram, capExperimental, candidate, layout, trapdoorBytes,
      LENGTH, LOG_LENGTH, LEAF_SIZE, DIGEST_BYTES, MEMORY_BYTES] at cardinal ⊢
    omega

private theorem word_access (address : Nat) (aligned : address % 8 = 0)
    (bounded : address+8 ≤ MEMORY_BYTES) :
    accessValid (BitVec.ofNat 64 address) 8 = true := by
  have small : address < 2^64 := by
    simp only [MEMORY_BYTES] at bounded
    omega
  simp only [accessValid, rangeValid, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt small, bounded, aligned, decide_true, Bool.true_and]

theorem cap_check_record_access (input : CheckInput) (ordinal : Nat)
    (present : ordinal < input.positions.card)
    (admitted : input.proof.length ≤ capProgram.sizes.proof)
    (enough : 544 * input.positions.card ≤ input.proof.length)
    (state : MachineState)
    (indices : state.getReg .x24 =
      BitVec.ofNat 64 (capProgram.layout.indices + 8*ordinal))
    (values : state.getReg .x8 =
      BitVec.ofNat 64 (capProgram.layout.values + 256*ordinal))
    (proof : state.getReg .x25 =
      BitVec.ofNat 64 (capProgram.layout.proof + 544*ordinal)) :
    accessValid (state.getReg .x24) 8 = true ∧
    (∀ word : Fin 4,
      accessValid (state.getReg .x25 + BitVec.ofNat 64 (8*word.val)) 8 = true) ∧
    (∀ word < 32,
      accessValid (state.getReg .x8 + BitVec.ofNat 64 (8*word)) 8 = true) := by
  have bounds := cap_check_record_bounds input ordinal present admitted enough
  have indexAlign : (capProgram.layout.indices + 8*ordinal) % 8 = 0 := by
    norm_num [capProgram, capExperimental, candidate, layout, trapdoorBytes,
      LENGTH, LOG_LENGTH, LEAF_SIZE, DIGEST_BYTES]
  have valueAlign : (capProgram.layout.values + 256*ordinal) % 8 = 0 := by
    norm_num [capProgram, capExperimental, candidate, layout, trapdoorBytes,
      LENGTH, LOG_LENGTH, LEAF_SIZE, DIGEST_BYTES]
    omega
  have proofAlign : (capProgram.layout.proof + 544*ordinal) % 8 = 0 := by
    norm_num [capProgram, capExperimental, candidate, layout, trapdoorBytes,
      LENGTH, LOG_LENGTH, LEAF_SIZE, DIGEST_BYTES]
    omega
  refine ⟨?_, ?_, ?_⟩
  · rw [indices]
    exact word_access _ indexAlign bounds.1
  · intro word
    rw [proof, ← BitVec.ofNat_add]
    apply word_access
    · omega
    · have inside := word.isLt
      omega
  · intro word inside
    rw [values, ← BitVec.ofNat_add]
    apply word_access
    · omega
    · omega

end CommitGolfCandidate
