import CommitGolfCandidate.CapOldProofSelect
import CommitGolfCandidate.CapOldLowerSelect
import CommitGolfCandidate.CapTreeMarksNonempty
import CommitGolfCandidate.CapOpenLoadedBytes

/-! Pure postprocessing of the old full-path transcript. All slot choices use
only positions, and on honest full-path inputs every returned byte is copied
from the supplied proof. Short arbitrary inputs use the total zero fallback.
Empty requests return no bytes. The image-level loaded-byte equality below
does not require an honest heap or any hash equation. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
attribute [local irreducible] readBuffer capOpenLowerDigests capOpenBoundaryDigests heapDigest

noncomputable def capPostprocess (positions : Positions) (proof : Proof) : Proof :=
  if positions.card=0 then []
  else capOldLowerBytes positions proof ++ capOldBoundaryBytes positions proof 8 1

theorem cap_postprocess_empty (positions : Positions) (proof : Proof)
    (empty : positions.card=0) : capPostprocess positions proof=[] := by
  rw [capPostprocess,if_pos empty]

theorem cap_postprocess_loaded (message : Message) (committed : MachineState)
    (positions : Positions) (positive : 0 < positions.card) :
    capPostprocess positions
      (referenceOpening (heapDigest committed 4294971424)
        (fun index => readNonce committed (5368713248+24*index.val)) positions) =
      capOpenLoadedBytes
        (readBuffer committed capProgram.layout.trapdoor capProgram.sizes.trapdoor)
        positions := by
  rw [capPostprocess,if_neg (by omega),cap_old_lower_loaded message,
    cap_old_boundary_bytes _ _ positions 8 1 (by decide) (by decide) (by decide)
      (Or.inl (cap_open_requested_marks_nonempty positions positive)),
    capOpenLoadedBytes]
  apply congrArg (fun suffix : Proof =>
    capDigestEncoding (capOpenLowerDigests
      (readBuffer committed capProgram.layout.trapdoor capProgram.sizes.trapdoor)
      positions) ++ suffix)
  apply congrArg capDigestEncoding
  rw [← cap_root_boundary_order,capOpenBoundaryDigests]
  apply List.map_congr_left
  intro node member
  have bounds := cap_control_boundaries_nodes (capOpenRequestedMarks positions)
    1022 (.visit 1) (by constructor <;> decide) node member
  exact (cap_open_committed_root_slot committed positions node bounds.2).symm

end CommitGolfCandidate
