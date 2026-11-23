import CommitGolfCandidate.TwoPermutationPackedHonestInput
import CommitGolfCandidate.TwoPermutationPackedInputFrame

/-! One-byte search: inputs that agree with an honest input on its records.

The record phase reads only the commitment, positions, values and the record bytes `[0, 534 k)` of the proof. Its
honest facts therefore hold for every input that agrees with the honest input there (`NearHonest`), whatever its
cap bytes are. The one-byte checker needs this for the truncated honest proof, whose decoded cap differs from the
honest one in 8 bits of the last frontier digest. The 8 bytes of slack after `534 k` cover the aligned word that
holds the last record byte. -/
namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open TwoPermutationPrototype.RV64
open TwoPermutationPrototype.Checker (RecordInputFrame checker_positions_bound)

/-- `input` is `honest` with another proof of the same length that has the same bytes before `534 k + 8`. -/
def NearHonest (input honest : CheckInput) : Prop :=
  ∃ P : Proof, input = { honest with proof := P } ∧ P.length = honest.proof.length ∧
    ∀ q, q < 534*honest.positions.card+8 → P[q]? = honest.proof[q]?

theorem NearHonest.refl (honest : CheckInput) : NearHonest honest honest :=
  ⟨honest.proof, rfl, rfl, fun _ _ => rfl⟩

theorem NearHonest.of_eq {input honest : CheckInput} (same : input = honest) : NearHonest input honest :=
  same ▸ NearHonest.refl honest

theorem NearHonest.positions {input honest : CheckInput} (near : NearHonest input honest) :
    input.positions = honest.positions := by
  obtain ⟨P, rfl, _, _⟩ := near
  rfl

theorem NearHonest.commitment {input honest : CheckInput} (near : NearHonest input honest) :
    input.commitment = honest.commitment := by
  obtain ⟨P, rfl, _, _⟩ := near
  rfl

theorem NearHonest.length {input honest : CheckInput} (near : NearHonest input honest) :
    input.proof.length = honest.proof.length := by
  obtain ⟨P, rfl, len, _⟩ := near
  exact len

theorem read_buffer_bytes_congr (first second : MachineState) (address count : Nat)
    (same : ∀ j < count, first.getByte (BitVec.ofNat 64 (address+j)) = second.getByte (BitVec.ofNat 64 (address+j))) :
    readBuffer first address count = readBuffer second address count := by
  unfold readBuffer
  congr 1
  apply Finset.sum_congr rfl
  intro j inside
  rw [same j (Finset.mem_range.mp inside)]

/-- A near-honest input loads the honest input's bytes below `534 k + 8` of its proof. -/
theorem near_proof_byte {input honest : CheckInput} (near : NearHonest input honest)
    (admitted : honest.proof.length ≤ PackedChecker.submission.sizes.proof) (offset : Nat)
    (inside : offset < 534*honest.positions.card+8) (present : offset < honest.proof.length) :
    (QAssembly.submission.initialState .check input).getByte (BitVec.ofNat 64 (13824430176+offset)) =
      (QAssembly.submission.initialState .check honest).getByte (BitVec.ofNat 64 (13824430176+offset)) := by
  obtain ⟨P, rfl, len, agree⟩ := near
  have first := PackedChecker.check_input_proof_byte { honest with proof := P }
    (by change P.length ≤ _; rw [len]; exact admitted) offset (by change offset < P.length; omega)
  have second := PackedChecker.check_input_proof_byte honest admitted offset present
  rw [PackedChecker.initial_state] at first second
  change (QAssembly.submission.initialState .check _).getByte (BitVec.ofNat 64 (13824430176+offset)) = _ at first second
  rw [first, second]
  have same := agree offset inside
  rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem present] at same
  exact Option.some_inj.mp same

/-- A frame on a near-honest input reads the honest input's record bytes. -/
theorem near_proof_frame {input honest : CheckInput} (near : NearHonest input honest)
    (admitted : honest.proof.length ≤ PackedChecker.submission.sizes.proof)
    (records : 534*honest.positions.card ≤ honest.proof.length)
    (ordinal offset count : Nat) (state : MachineState)
    (frame : RecordInputFrame input ordinal state) (before : ordinal ≤ honest.positions.card)
    (inside : 534*ordinal+offset+count ≤ 534*honest.positions.card) :
    readBuffer state (checkProofByte ordinal+offset) count =
      readBuffer (QAssembly.submission.initialState .check honest) (checkProofByte ordinal+offset) count := by
  have card := checker_positions_bound honest
  have bounded : checkProofByte ordinal+offset+count ≤ 2^35 := by
    unfold checkProofByte
    omega
  rw [record_proof_frame input ordinal offset count state frame (by rw [near.positions]; exact before) bounded]
  apply read_buffer_bytes_congr
  intro j small
  have address : checkProofByte ordinal+offset+j = 13824430176+(534*ordinal+offset+j) := by
    unfold checkProofByte
    omega
  rw [address]
  exact near_proof_byte near admitted _ (by omega) (by omega)

end TwoPermutationPrototype.Packed.Checker
