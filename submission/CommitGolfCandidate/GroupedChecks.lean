import CommitGolfCandidate.MaterializedManifest
import CommitGolfCandidate.K1Manifest
import CommitGolfCandidate.K1CheckFacts
import CommitGolfCandidate.TwoPermutationPinnedBindingCertificate
import CommitGolfCandidate.GroupedCommit

/-! # Checker, admission and commit facts of the final submission

`checker_facts` is C2's `K1Check.checker_facts` (the v2 check image), `admitted` checks the image sizes and
layout of `K1Manifest`, and `resources` is the commit run at its claimed cycle count. -/

namespace TwoPermutationPrototype.GroupedChecks
open CommitGolf CommitGolf.Riscv OracleComp
abbrev actual := K1Artifact.submission
set_option maxRecDepth 16000
set_option maxHeartbeats 700000

theorem checker_facts : QuartetCertificate.CheckerFacts actual := K1Check.checker_facts

theorem admitted : actual.Admission := by
  intro p;cases p <;> simp only [actual,K1Artifact.submission,Image.Valid,Image.byteSize,LayoutValid,dataBase,
    ArtifactEncoding.length_decode] <;> decide

/-- The commit facts at the claimed cycle count (P's frozen final programs). -/
theorem resources (msg : Message) (z : Execution) (hit : z∈support (actual.run .commit msg)) :
    z.exit=.success ∧ z.cycles=504585244 ∧ z.oracleCalls≤COMMIT_BUDGET :=
  Grouped.commit_resources msg z hit

end TwoPermutationPrototype.GroupedChecks
