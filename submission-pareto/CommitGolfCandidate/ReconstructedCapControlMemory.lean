import CommitGolfCandidate.ReconstructedCapControlForward
import CommitGolfCandidate.ReconstructedCapEntry

namespace CommitGolfCandidate.Reconstruction.CapControlMemory
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp HonestCuts HonestFlow HonestCapStages
open HonestCapState (image)
open CommitBlocks (addr)
set_option maxRecDepth 18000
set_option maxHeartbeats 4500000
attribute [local irreducible] ArtifactEncoding.decode

def check : Nat→Word→Bool
  | 0,_ => false
  | n+1,pc => match HonestBlocks.readOp Artifact.openingCode pc with
    | none => false
    | some op => HonestBlocks.plain op && direct op && (HonestMemoryRanges.store op).isNone &&
      (targets pc op).all (fun p => stops p || check n p)

theorem frame (n : Nat) (pc : Word) (valid : check n pc=true) {s t : MachineState} {coin : Bool}
    (loc : s.pc=pc) (path : HonestCapState.Path coin s t) : t.mem=s.mem := by
  induction n generalizing pc s with
  | zero => cases valid
  | succ n ih =>
    cases found : HonestBlocks.readOp Artifact.openingCode pc with
    | none => simp [check,found] at valid
    | some op =>
      simp only [check,found,Bool.and_eq_true] at valid
      obtain ⟨⟨⟨plain,dir⟩,noWrite⟩,next⟩ := valid
      have reg : op≠.base .ECALL := by rintro rfl;cases plain
      have read := HonestBlocks.fetch_op Artifact.openingCode image (Eq.refl (ArtifactEncoding.decode 32 _)) (by decide)
        s op (loc ▸ found)
      have move (v : Execution) (q : v∈support (execute image 1 s coin)) (ok : v.exit=.unfinished) :
          v.state.pc∈targets pc op ∧ v.state.mem=s.mem := by
        have dest := (charged_successors image s op coin read dir (fun h => (reg h).elim) v q).2 ok
        refine ⟨loc ▸ dest.1,?_⟩
        funext addr
        apply HonestMemoryRanges.memory_frame s _ op addr (HonestAbstract.continued_step _ s op coin read reg v q ok)
        intro w someW
        rw [someW] at noWrite;cases noWrite
      cases path with
      | hit run cont stop => exact (move _ run cont).2
      | more run cont inside tail =>
        obtain ⟨target,mem⟩ := move _ run cont
        have safe := List.all_eq_true.mp next _ target
        simp only [inside,Bool.false_or] at safe
        exact (ih _ safe rfl tail).trans mem

def prices : List (Nat×Nat) := [(1429,19),(1451,14),(1469,1),(1483,26),(1511,1),(1581,16),
  (1603,7),(1625,1),(1602,1),(1449,2)]

theorem actual (i n : Nat) (known : (i,n)∈prices) (s t : MachineState) (coin : Bool)
    (pc : s.pc=addr i) (path : HonestCapState.Path coin s t) : t.mem=s.mem := by
  apply frame n _ _ pc path
  simp only [prices,List.mem_cons,List.not_mem_nil,or_false] at known
  rcases known with h|h|h|h|h|h|h|h|h|h <;> cases h <;> decide +kernel

end CommitGolfCandidate.Reconstruction.CapControlMemory
