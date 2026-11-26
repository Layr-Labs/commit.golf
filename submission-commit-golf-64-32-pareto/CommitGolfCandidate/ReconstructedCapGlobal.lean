import CommitGolfCandidate.ReconstructedCapControlMemory
import CommitGolfCandidate.ReconstructedCapFrame
import CommitGolfCandidate.ReconstructedHonestCapMetadata

namespace CommitGolfCandidate.Reconstruction.CapGlobal
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 HonestCapStages HonestCapPlan
open HonestCapTables (w sp scratch)
open CommitBlocks (addr)
set_option maxRecDepth 20000
set_option maxHeartbeats 8500000
attribute [local irreducible] ArtifactEncoding.decode

def fixed : Facts := [(.x5,w CapLoad.heap),(.x9,w scratch),(.x13,w HonestCapRam.activeBase),(.x17,w HonestRecordMemory.proofBase),
  (.x18,w (CapLoad.heap+24)),(.x19,34),(.x28,65),(.x31,211)]
def keep : List Reg := [.x5,.x9,.x13,.x17,.x18,.x19,.x28,.x31,.x2,.x8]

theorem init_table : checked 1429 [(.x0,0),(.x8,sp)]
    [.x0,.x5,.x8,.x9,.x10,.x11,.x13,.x14,.x17,.x18,.x19,.x26,.x28,.x31]
    [(1451,fixed)] 19=true := by decide +kernel

theorem mapped (p : Phase) (notStart : p≠.enter) (live : p≠.returned) :
    HonestFrame.check Artifact.openingCode stops keep (fee p) (addr (pc p))=true := by
  cases p <;> first | contradiction | (simp only [fee,pc];decide +kernel)

theorem reg (p : Phase) (s t : MachineState) (coin : Bool) (notStart : p≠.enter) (live : p≠.returned)
    (start : s.pc=addr (pc p)) (path : HonestCapState.Path coin s t) :
    ∀ r∈keep, t.getReg r=s.getReg r :=
  HonestFrame.sound Artifact.openingCode HonestCapState.image (Eq.refl (ArtifactEncoding.decode 32 _)) (by decide)
    stops keep (fee p) _ (mapped p notStart live) coin s t start path

structure Common (s : MachineState) (trap : CommitStorage.Trapdoor) (ps : Positions) : Prop where
  source : CapEntry.Source s trap ps
  regs : holds s fixed

theorem transferred (p : Phase) (s t : MachineState) (trap : CommitStorage.Trapdoor) (ps : Positions)
    (before : Common s trap ps) (notStart : p≠.enter) (live : p≠.returned) (start : s.pc=addr (pc p))
    (path : HonestCapState.Path true s t) (mem : CapFrame.same s t) : Common t trap ps := by
  have same := reg p s t true notStart live start path
  refine ⟨CapFrame.transfer s t trap ps before.source (same _ (by decide)) (same _ (by decide)) mem,?_⟩
  intro r v h
  have subset : r∈keep := by
    simp only [fixed,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with h|h|h|h|h|h|h|h <;> cases h <;> decide
  exact (same _ subset).trans (before.regs _ _ h)

end CommitGolfCandidate.Reconstruction.CapGlobal
