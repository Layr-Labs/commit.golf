import CommitGolfCandidate.ReconstructedHonestScanForward
import CommitGolfCandidate.ReconstructedCommitExact

namespace CommitGolfCandidate.Reconstruction.CapControlForward
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp HonestRanges HonestProtected HonestCapStages
open CommitBlocks (addr)
open HonestCapState (image)
open HonestCapTables (w sp)
open HonestCapSpan (emptyContext)
set_option maxRecDepth 24000
set_option maxHeartbeats 30000000
attribute [local irreducible] ArtifactEncoding.decode

def shape (xs : Facts) : Shape := ⟨xs.map (fun x => (x.1,point x.2)),[]⟩
def ready (i n : Nat) (xs : Facts) := HonestForward.check Artifact.openingCode stops n (addr i) ((shape xs).model emptyContext)

theorem forward (o : Oracle) (s : MachineState) (i n : Nat) (xs : Facts) (h : ready i n xs=true)
    (pc : s.pc=addr i) (regs : holds s xs) :
    ∃ k t, k≤n ∧ HonestCapState.Path true s t ∧ CommitExact.Segment o image k s t := by
  have model : Holds emptyContext (shape xs) s := by
    refine ⟨?_,(by intro _ _ h;cases h),(by intro _ h;cases h)⟩
    intro r v member
    obtain ⟨⟨a,b⟩,found,same⟩ := List.mem_map.mp member
    cases same
    rw [regs a b found]; exact precise _
  obtain ⟨k,fee,t,small,path,run⟩ := HonestForward.sound Artifact.openingCode image
    (Eq.refl (ArtifactEncoding.decode 32 _)) (by decide) stops n _ _ h s true pc (models_shape model)
  exact ⟨k,t,small,path,fee,0,fun fuel => by rw [run,bind_pure_comp,fixed_oracle_run_map]⟩

def plain : List (Nat×Nat) := [(1429,19),(1451,14),(1469,1),(1511,1),(1602,1),(1603,7),(1625,1),(1449,2)]

theorem arithmetic (i n : Nat) (found : (i,n) ∈ plain) : ready i n []=true := by
  simp only [plain,List.mem_cons,List.not_mem_nil,or_false] at found
  rcases found with h|h|h|h|h|h|h|h <;> cases h <;> decide +kernel

def beforeWidth (d : Nat) : Facts := [(.x0,0),(.x8,sp),(.x10,w d)]
def beforeGroup (d : Nat) : Facts := [(.x0,0),(.x8,sp),(.x10,w d),(.x21,w (8*d))]

theorem masks (d : Fin 10) : ready 1483 26 (beforeWidth d.val)=true := by
  exact (by decide +kernel : ∀ k : Fin 10, ready 1483 26 (beforeWidth k.val)=true) d

theorem groups (d : Fin 10) : ready 1581 16 (beforeGroup d.val)=true := by
  exact (by decide +kernel : ∀ k : Fin 10, ready 1581 16 (beforeGroup k.val)=true) d

end CommitGolfCandidate.Reconstruction.CapControlForward
