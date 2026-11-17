import CommitGolfCandidate.TwoPermutationBodyState

namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
open CommitGolfCandidate (checkEvaluation check_evaluation_bind check_evaluation_pure check_evaluation_support
  read_buffer_slice splitBlocks)
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
attribute [local irreducible] checkEvaluation leavesTrace parentsTrace parentBatches fullParents readBuffer
  finalReply fullLeafDigests readyState parentSetup rootPrefix transcriptHeap

theorem physical_results (candidate : Submission) (abi : CommitABI candidate) (oracle : Oracle)
    (msg : Message) (packed : BitVec (128*LENGTH)) :
    let s := candidate.initialState .commit msg
    let result := packedOutput s oracle packed
    let output := candidate.readCommit result
    let salts := splitBlocks 128 LENGTH packed
    let heap := publicTree oracle msg salts
    output.1=heap 1 ∧
    (∀ n, 0<n → n<2*LENGTH → output.2.extractLsb' (256*n) 256=heap n) ∧
    (∀ i : Index, output.2.extractLsb' (8*(80*LENGTH+16*i.val)) 128=salts i) := by
  let s := candidate.initialState .commit msg
  let ready := readyState s packed
  let leaves := (checkEvaluation oracle (leavesTrace (2^20) 0 ready)).1
  let start := parentSetup leaves 5
  let parents := (checkEvaluation oracle (fullParents start)).1
  let salts := splitBlocks 128 LENGTH packed
  let heap := publicTree oracle msg salts
  have leafEq (i : Index) : heap (LENGTH+i.val)=fullLeafDigests (BiPermutation.equiv Block oracle.permutation) msg salts i :=
    transcript_heap_leaf .. 
  have tree (n : Nat) (positive : 0<n) (inner : n<LENGTH) :
      heap n=oracle.compression (heap (2*n+1) ++ heap (2*n)) :=
    transcript_heap_parent false _ _ n positive inner
  have initial := initialize_parent_content candidate abi oracle msg packed heap leafEq
  have content : ParentContent parents heap salts 0 := all_parents_content oracle start heap salts tree initial
  have leafHit := check_evaluation_support oracle (leavesTrace (2^20) 0 ready)
  obtain ⟨_,regs,pc,out⟩ := after_leaves_parent_ready s (abi_commit_entry candidate abi msg) packed leafHit
  obtain ⟨regEnd,_,outEnd⟩ := full_parents_post start regs pc (check_evaluation_support oracle (fullParents start))
  have x8 : parents.getReg .x8=4294971392 := outEnd.trans out
  exact serialized_parent_results candidate abi parents heap salts (packedOutput s oracle packed)
    (state_of_body s oracle packed) regEnd.heap x8 content

end TwoPermutationPrototype.RV64
