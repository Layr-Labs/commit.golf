import CommitGolfCandidate.RungAOrbit
import CommitGolfCandidate.RungACompose
import CommitGolfCandidate.RungAOracle
namespace CommitGolfCandidate.RungA
open CommitGolf CommitGolf.Riscv

noncomputable def rungAOpening : RungAOpening (Late.submission.image .commit) image :=
  openingOfPrelude (prelude ⟨runHash⟩)

noncomputable def openingWithCommit (commit : Image) : RungAOpening commit image :=
  rungAOpening.withCommit commit

end CommitGolfCandidate.RungA
