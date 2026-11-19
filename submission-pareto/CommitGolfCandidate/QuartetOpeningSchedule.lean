import CommitGolfCandidate.TwoPermutationPackedOpeningSchedule
import CommitGolfCandidate.TwoPermutationPackedOpeningImage
import CommitGolf.Statements
import CommitGolfCandidate.QuartetManifest

namespace TwoPermutationPrototype.QuartetOpening
open CommitGolf CommitGolf.Riscv TwoPermutationPrototype.Sampling

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem manifest_admitted : QuartetArtifact.submission.Admission := by
  intro program
  cases program <;>
    simp only [QuartetArtifact.submission, Image.Valid, Image.byteSize, LayoutValid,
      dataBase, ArtifactEncoding.length_decode] <;> decide

def actualOpening : Image := QuartetArtifact.submission.image .opening

theorem opening_words : actualOpening.code.length = 713 := by
  simp only [actualOpening, QuartetArtifact.submission, ArtifactEncoding.length_decode]

/-- The 64 words covering both cap loops, the size return, and HALT are
identical in the two delivered images after shifting 46 instructions. -/
theorem cap_words :
    ∀ j : Fin 64, actualOpening.code.getD (649 + j.val) 0 =
      PackedOpening.openingImage.code.getD (603 + j.val) 0 := by
  intro j
  simp only [actualOpening, QuartetArtifact.submission]
  rw [ArtifactEncoding.getD_decode 32 _ _ (by omega)]
  revert j
  decide

/-- Proof bytes of an opening: 534-byte records and the cap frontier in 238-byte groups of eight
(K3-DESIGN §9.2: `30 f - 2 floor(f/8)` frontier bytes). -/
def proofLength (positions : Positions) : Nat :=
  534*positions.card + 30*(Opening.openingNodes positions).length - 2*((Opening.openingNodes positions).length/8)

def scheduledCycles (positions : Positions) : Nat :=
  if positions.card = 0 then 7 else
    15 + (673*positions.card-1) + 2554 +
      (PackedOpening.capSubtreeCycles (Opening.groupsBefore positions positions.card) 1 8 +
        4*(Opening.openingNodes positions).length + 34*((Opening.openingNodes positions).length/8) + 3) + 4

theorem group_index (i : Index) :
    (4194304 + i.val / 4) / 16384 = capGroup i := by
  change (4194304 + i.val / 4) / 16384 = (16777216+i.val)/65536
  omega

/-- The input and output layout has room for the largest honest opening even
when every position is disclosed. -/
theorem capacity_all (positions : Positions) : proofLength positions ≤ 8959041024 := by
  have cardinal : positions.card ≤ 16777216 := by
    have top : positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ positions
    exact top
  have nodes := Opening.opening_nodes_bound positions
  unfold proofLength
  omega

theorem fuel_all (positions : Positions) :
    scheduledCycles positions ≤ QuartetArtifact.submission.steps .opening := by
  have cardinal : positions.card ≤ 16777216 := by
    have top : positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ positions
    exact top
  have count := Opening.opening_nodes_bound positions
  change scheduledCycles positions ≤ 17179934720
  unfold scheduledCycles
  split
  · decide
  · rw [PackedOpening.cap_cycle_delta]
    have budget := Opening.opening_cap_cycles_bound (Opening.groupsBefore positions positions.card)
    have nodes := Opening.opening_nodes_bound positions
    simp only [Opening.openingNodes, ite_eq_right (by assumption)] at nodes
    omega

theorem scheduled_cycles_le (p : Positions) (nz : p.card ≠ 0) : scheduledCycles p ≤ 15 + 673*p.card + 100000 := by
  unfold scheduledCycles
  rw [ite_eq_right nz, PackedOpening.cap_cycle_delta]
  have budget := Opening.opening_cap_cycles_bound (Opening.groupsBefore p p.card)
  have count := Opening.opening_nodes_bound p
  have nodes := Opening.opening_nodes_bound p
  simp only [Opening.openingNodes, ite_eq_right nz] at nodes
  omega

theorem delta (positions : Positions) (nonempty : positions.card ≠ 0) :
    scheduledCycles positions = PackedOpening.scheduledCycles positions + 5 + 83*positions.card +
      4*(Opening.openingNodes positions).length + 34*((Opening.openingNodes positions).length/8) ∧
    proofLength positions + 2*((Opening.openingNodes positions).length/8) =
      PackedOpening.proofLength positions + 36*positions.card := by
  unfold scheduledCycles PackedOpening.scheduledCycles proofLength PackedOpening.proofLength PackedOpening.recordBytes
  rw [ite_eq_right nonempty, ite_eq_right nonempty]
  omega

theorem scored_limits (positions : Positions) (count : positions.card = BATCH) :
    scheduledCycles positions ≤ 99996 ∧ proofLength positions ≤ 72160 := by
  have realCount : positions.card = 128 := count
  have previous := PackedOpening.scheduled_scored_limits positions count
  have change := delta positions (by omega)
  have nodes := Opening.opening_nodes_bound positions
  constructor
  · omega
  · unfold proofLength
    omega

theorem scored_attainment :
    ∃ positions : Positions, positions.card = BATCH ∧ scheduledCycles positions = 99996 ∧
      proofLength positions = 72160 := by
  obtain ⟨positions, count, cycles, bytes⟩ := PackedOpening.scheduled_scored_attainment
  have realCount : positions.card = 128 := count
  have change := delta positions (by omega)
  have full : (Opening.openingNodes positions).length = 128 := by
    unfold PackedOpening.proofLength PackedOpening.recordBytes at bytes
    omega
  refine ⟨positions, count, ?_, ?_⟩
  · have total := change.1
    omega
  · unfold proofLength
    omega

end TwoPermutationPrototype.QuartetOpening
