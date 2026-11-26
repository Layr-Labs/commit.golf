import CommitGolfCandidate.ReconstructedHonestForward
import CommitGolfCandidate.ReconstructedHonestCapSpan

namespace CommitGolfCandidate.Reconstruction.HonestScanForward
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp HonestRanges HonestProtected HonestCapState HonestCapStages
open HonestRecordMemory (constant)
open HonestCapTables (scratch w)
open HonestCapRam (activeBase)
open CommitBlocks (addr)

set_option maxRecDepth 32768
set_option maxHeartbeats 50000000
attribute [local irreducible] ArtifactEncoding.decode

def input (p : Nat) : Shape := ⟨[(.x16,HonestCapSpan.flags),(.x23,HonestCapSpan.flags),
  (.x24,HonestCapSpan.flags),(.x9,constant scratch),(.x20,constant p)],[]⟩

private theorem table (p : Fin 257) : HonestForward.check Artifact.openingCode stops 17 (addr 1470)
    ((input p.val).model HonestCapSpan.emptyContext)=true := by
  exact (by decide +kernel : ∀ i : Fin 257, HonestForward.check Artifact.openingCode stops 17 (addr 1470)
    ((input i.val).model HonestCapSpan.emptyContext)=true) p

/-- Every actual pair scan returns to its guard in at most 17 instructions,
without faulting or querying the oracle, independently of both loaded bytes. -/
theorem run (s : MachineState) (coins : Bool) (pc0 : s.pc=addr 1470) (p : Fin 257)
    (left : Contains HonestCapSpan.flags (s.getReg .x23)) (right : Contains HonestCapSpan.flags (s.getReg .x16))
    (parent : Contains HonestCapSpan.flags (s.getReg .x24)) (ptr : s.getReg .x9=w scratch)
    (counter : s.getReg .x20=w p.val) : HonestForward.Forward image coins stops 17 s := by
  have model : Holds HonestCapSpan.emptyContext (input p.val) s := by
    refine ⟨?_,(by intro _ _ h; cases h),(by intro _ h; cases h)⟩
    intro r v h
    simp only [input,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with h|h|h|h|h <;> cases h
    · exact right
    · exact left
    · exact parent
    · rw [ptr]; exact precise _
    · rw [counter]; exact precise _
  exact HonestForward.sound Artifact.openingCode image (Eq.refl (ArtifactEncoding.decode 32 _)) (by decide) stops
    17 _ _ (table p) s coins pc0 (models_shape model)

end CommitGolfCandidate.Reconstruction.HonestScanForward
