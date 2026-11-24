import CommitGolfCandidate.ChainedCheckHashContent
import CommitGolfCandidate.ChainedCheckerArtifact

/-! Transfer the checked hash-call execution to the exact delivered artifact. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

theorem artifact_checking_hash (site : CheckerHashSite) (remaining : Nat) (small : remaining≤7)
    (s : MachineState) (args : LoopArgs s 256) (pc : s.pc=site.base)
    (counter : s.getReg .x18=BitVec.ofNat 64 remaining)
    (inputs : ∀ k : Fin 8, accessValid (s.getReg .x14+BitVec.ofNat 64 (8*k.val)) 8=true)
    (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (34+continuationInstructions remaining+fuel) s coins=
      (do let out ← checkerHashTrace site remaining s
          let result ← execute (Artifact.submission.image .check) fuel out coins
          return result.charge (41+continuationCycles remaining) (remaining+1)) := by
  rw [checking_manifest_image]
  exact checker_hash_execution site remaining small s args pc counter inputs fuel coins

end CommitGolfCandidate.Chained.Native
