import CommitGolfCandidate.TruncTruthLeaves
namespace CommitGolfCandidate.Trunc
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 12000
set_option maxHeartbeats 350000
attribute [local irreducible] checkEvaluation fixedParents parentProgram commitLeaves commitInputReady enterState

theorem commit_output_matches (oracle : Oracle) (message : Message) (state : MachineState)
    (heapPointer : state.getReg .x9 = BitVec.ofNat 64 4294971424)
    (outputPointer : state.getReg .x26 = BitVec.ofNat 64 4294971392)
    (parents : Consistent oracle 0 state)
    (leaves : ∀ index : Index, heapDigest state 4294971424 (LENGTH+index.val) =
      leafDigest oracle.compression index (readBuffer state (5905584160+16*index.val) 16) (message index)) :
    CommittedState oracle message (commitExitState (commitRootCopyState state)) := by
  let finished := commitExitState (commitRootCopyState state)
  have preserved (node : Nat) (below : node < 2*LENGTH) :
      heapDigest finished 4294971424 node = heapDigest state 4294971424 node := by
    unfold heapDigest
    have := heap_offset_bound node LENGTH below
    have offsetAligned := heap_offset_aligned node
    change heapOffset node + 32 ≤ 96*16777216 at this
    exact commit_output_preserves_digest state 4294971392 (4294971424+heapOffset node) outputPointer
      (by omega) (by omega) (by omega)
  refine ⟨?_, ?_, ?_⟩
  · rw [commit_output_root state 4294971424 4294971392 heapPointer outputPointer
      (by decide) (by decide) (by decide) (by decide)]
    exact (preserved 1 (by decide)).symm
  · intro node positive below
    change heapDigest finished 4294971424 node=parent oracle.compression node (heapDigest finished 4294971424 (2*node)) (heapDigest finished 4294971424 (2*node+1))
    rw [preserved node (by omega), preserved (2*node) (by omega), preserved (2*node+1) (by omega)]
    exact parents node positive below
  · intro index
    change heapDigest finished 4294971424 (LENGTH+index.val)=leafDigest oracle.compression index (readBuffer finished (5905584160+16*index.val) 16) (message index)
    have indexBound : index.val < LENGTH := index.isLt
    rw [preserved (LENGTH+index.val) (by omega)]
    have salts := commit_output_preserves_salt state 4294971392 (5905584160+16*index.val)
      outputPointer (by omega) (by change index.val < 16777216 at indexBound; omega) (by omega)
    rw [salts]
    exact leaves index

theorem returnedTruth (o : Oracle) (m : Message) (a : BitVec (128*LENGTH)) : CommittedState o m (returned o m a) := by
  have f:=finalFrame o m a
  apply commit_output_matches o m (parentsState o m a) f.pointers.heap f.root (parentsTruth o m a)
  intro i;rw [saltTruth];exact leafTruth o m a i

theorem outputSalt (o : Oracle) (m : Message) (a : BitVec (128*LENGTH)) (i : Index) :
    readBuffer (returned o m a) (5905584160+16*i.val) 16=a.extractLsb' (128*i.val) 128 := by
  have hi : i.val<16777216:=i.isLt
  exact (commit_output_preserves_salt (parentsState o m a) 4294971392 (5905584160+16*i.val) (finalFrame o m a).root (by omega) (by omega) (by omega)).trans
    (saltTruth o m a i)

end CommitGolfCandidate.Trunc
