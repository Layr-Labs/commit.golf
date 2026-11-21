import CommitGolfCandidate.GroupOpenABI
import CommitGolfCandidate.GroupOpenModel
import CommitGolfCandidate.GroupOpenRecordBytes

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp Sampling
open Opening (trapdoorHeap sortedIndex openingNodes groupsBefore)
open QuartetOpening (proofLength)
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000

/-- `bytesAt` over consecutive equal-width chunks is the concatenation of the chunks. -/
private theorem bytes_at_chunks {α : Type} (state : MachineState) (address width : Nat) (items : List α)
    (itemBytes : α → List Byte)
    (reads : ∀ j (inside : j < items.length),
      bytesAt state (address+width*j) width = itemBytes items[j]) :
    bytesAt state address (width*items.length) = items.flatMap itemBytes := by
  induction items generalizing address with
  | nil => simp [bytesAt]
  | cons first rest ih =>
    have head := reads 0 (by simp)
    have tail : ∀ j (inside : j < rest.length),
        bytesAt state (address + width + width*j) width = itemBytes rest[j] := by
      intro j inside
      have same := reads (j+1) (by simpa)
      simpa only [List.getElem_cons_succ, Nat.mul_succ, Nat.add_left_comm, Nat.add_comm, Nat.add_assoc] using same
    rw [List.length_cons, Nat.mul_succ, Nat.add_comm (width*rest.length) width, bytes_at_append,
      List.flatMap_cons, ih (address+width) tail]
    simpa using head

/-- The decoded ABI output is the exact lower records and canonical cap footer. -/
theorem read_opening_proof (s : Submission) (abi : OpeningABI s)
    (trapdoor : BitVec (8 * s.sizes.trapdoor)) (positions : Positions) (result : Execution)
    (physical : OpenPhysical s trapdoor positions result) :
    s.readProof result = proofFromTrapdoor (s := s) trapdoor positions := by
  have fit : (result.state.getReg .x11).toNat ≤ s.sizes.proof := by
    rw [physical.length]
    exact (QuartetOpening.capacity_all positions).trans abi.capacity
  have success : s.openingSucceeded result = true := by
    simp [Submission.openingSucceeded, physical.success, fit]
  simp only [Submission.readProof, success, ite_true, physical.length, abi.toOpeningLayout.proof]
  change bytesAt result.state proofBase (proofLength positions) = _
  have split : proofLength positions = 534*positions.card + capOffset (openingNodes positions).length := by
    unfold proofLength capOffset
    omega
  rw [split, bytes_at_append, proofFromTrapdoor]
  congr 1
  · have length : (positions.sort (· ≤ ·)).length = positions.card := Finset.length_sort _
    rw [← length]
    apply bytes_at_chunks
    intro j inside
    have present : j < positions.card := by simpa using inside
    have lower : CompletedRecords s trapdoor positions result.state (j+1) := by
      intro prior live earlier
      exact physical.lower prior live (by omega)
    exact record_bytes s abi.toOpeningLayout trapdoor positions result.state j present lower
  · have footer := physical.footer
    rw [show proofBase+534*positions.card = recordBase positions.card from rfl]
    exact footer

end TwoPermutationPrototype.GroupedOpening
