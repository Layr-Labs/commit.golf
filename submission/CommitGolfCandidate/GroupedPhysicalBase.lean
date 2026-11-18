import CommitGolfCandidate.GroupedSeed
import CommitGolfCandidate.GroupedQMeaning
import CommitGolfCandidate.QuartetPhysical
import CommitGolfCandidate.MaterializedManifest

namespace TwoPermutationPrototype.Grouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.QuartetCommit (qSource qSalt qLeaf qUpper digestWords originalLeaf physicalHeap upper_sequence_semantics upper_groups_semantics UpperContent PaddedLeaves physical_heap_parent physical_heap_leaf packed_sequence_keeps_output wide_parent_full_register)
open CommitGolfCandidate.Permutation.CounterSalt (salts)
set_option maxRecDepth 18000
set_option maxHeartbeats 1000000
attribute [local irreducible] readBuffer checkEvaluation qGroups qUnits scan fixedScan packedParentsTrace packedParentGroups rootPrefix physicalHeap originalLeaf readyState
abbrev actual := MaterializedArtifact.submission
def savedKey {n : Nat} (td : BitVec n) (j : Fin 3) := td.extractLsb' (8*(2684354568+8*j.val)) 64
private theorem upper_from_quad (oracle : Oracle) (msg : Message) (salts : CompleteSaltTape)
    (leafState quad : MachineState) (post : QuadPrefix oracle (memoryView leafState)
      (fun i => digestWords (originalLeaf oracle msg salts i)) quad 4194304) :
    UpperContent (upStartPrefix quad 6) (physicalHeap oracle msg salts) (memoryView leafState) 4194303 := by
  refine ⟨?_,post.high⟩
  intro n lo hi
  let g := n-4194304
  have bound : g<4194304 := by dsimp [g];omega
  have eq : n=4194304+g := by dsimp [g];omega
  rw [eq,physical_heap_leaf oracle msg salts g bound,nodeDigest,read_buffer_memory_congr _ quad (show (upStartPrefix quad 6).mem=quad.mem from rfl)]
  apply aligned_buffer_eq _ _ _ (by decide)
  intro k hk
  have w:=congrFun (post.upper g bound) (⟨k,hk⟩ : Fin 4)
  have addr : treeWord (4194304+g)=qUpper g := by unfold treeWord qUpper;omega
  rw [addr]
  have link (children : Nat → Words 4) : quadReply oracle children g=QuartetCommit.quadReply oracle children g := rfl
  simp only [link,originalLeaf] at w
  exact w.trans (low_digest_word (QuartetCommit.quadReply oracle _ g) ⟨k,hk⟩)

theorem ready_upper_content (oracle : Oracle) (msg : Message) (salts : CompleteSaltTape)
    (leafState : MachineState) (ready : PaddedLeaves (memoryView leafState) (fun i => digestWords (originalLeaf oracle msg salts i))) :
    let quad := (checkEvaluation oracle (qGroups 512 0 (qStartPrefix leafState 3))).1
    UpperContent (upStartPrefix quad 6) (physicalHeap oracle msg salts) (memoryView leafState) 4194303 := by
  let cs := fun i => digestWords (originalLeaf oracle msg salts i)
  let s:=qStartPrefix leafState 3
  let quad := (checkEvaluation oracle (qGroups 512 0 s)).1
  have inv : QuadPrefix oracle (memoryView leafState) cs s 0 := ⟨fun _ h => False.elim (by omega),fun _ _ _ => rfl⟩
  have post := q_groups_content oracle (memoryView leafState) cs s 0 512 (by decide) ready inv
  exact upper_from_quad oracle msg salts leafState quad post


end TwoPermutationPrototype.Grouped
