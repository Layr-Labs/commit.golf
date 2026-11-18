import CommitGolfCandidate.QuartetManifest
import CommitGolfCandidate.QuartetWordBridge
import CommitGolfCandidate.QuartetCommitInput
import CommitGolfCandidate.QuartetCommitUpperMeaning
import CommitGolfCandidate.Execution
import CommitGolfCandidate.QuartetCommitJoinRegs
import CommitGolfCandidate.QuartetCommitLeafOps
import CommitGolfCandidate.QuartetCommitLeafSpill
import CommitGolfCandidate.QuartetCommitRanges
import CommitGolfCandidate.TwoPermutationCommitSetup
import CommitGolfCandidate.TwoPermutationManifest
import CommitGolfCandidate.TwoPermutationPackedParents

namespace TwoPermutationPrototype.QuartetCommit
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Sampling.Quartet (leafAt)
set_option maxRecDepth 8192
set_option maxHeartbeats 1300000
attribute [local irreducible] checkEvaluation packedParentsTrace packedParentGroups

abbrev actual := QuartetArtifact.submission

def originalLeaf (oracle : Oracle) (msg : Message) (salts : CompleteSaltTape) :=
  leafAt (pinnedFullLeafDigests (BiPermutation.equiv Block oracle.permutation) msg salts)

end TwoPermutationPrototype.QuartetCommit
