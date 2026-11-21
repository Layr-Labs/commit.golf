import CommitGolfCandidate.ChainedNonceFrame
import CommitGolfCandidate.NonceChainMemory

/-! Instantiate body root/nonce contents with the delivered artifact's seed expansion. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.RV64
open CommitGolfCandidate.Permutation.NonceChain
open TwoPermutationPrototype.Sampling

def deliveredReady (oracle : Oracle) (message : Message) (key : Key) : MachineState :=
  Chain.chainFinalReady oracle.permutation (Artifact.submission.initialState .commit message) key

noncomputable def deliveredSalts (oracle : Oracle) (key : Key) (i : Index) : BitVec 128 :=
  maskSalt (actualNonces oracle.permutation key i)

theorem delivered_body_root (oracle : Oracle) (message : Message) (key : Key) :
    readBuffer (checkEvaluation oracle (chainedCommitBody (deliveredReady oracle message key))).1 4294971392 32 =
      (referenceHeap oracle (pinnedLeafNodes oracle (deliveredReady oracle message key)) 1).setWidth 256 := by
  have content := Chain.final_content oracle Artifact.submission rfl rfl message key (artifact_commit_entry message)
  exact chained_commit_body_root oracle _ content.1 _ content.2.nonces

theorem delivered_body_nonce (oracle : Oracle) (message : Message) (key : Key) (i : Index) :
    readBuffer (checkEvaluation oracle (chainedCommitBody (deliveredReady oracle message key))).1 (8*leafSalt i.val) 16 =
      deliveredSalts oracle key i := by
  have content := Chain.final_content oracle Artifact.submission rfl rfl message key (artifact_commit_entry message)
  exact chained_commit_body_nonce oracle _ content.1 _ content.2.nonces i

end CommitGolfCandidate.Chained.Native
