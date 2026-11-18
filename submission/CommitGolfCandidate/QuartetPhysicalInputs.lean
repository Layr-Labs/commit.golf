import CommitGolfCandidate.QuartetWordBridge
import CommitGolfCandidate.QuartetCommitInput
import CommitGolfCandidate.QuartetCommitLeafMeaning
import CommitGolfCandidate.QuartetCommitQMeaning
import CommitGolfCandidate.QuartetCommitUpperMeaning
import CommitGolfCandidate.QuartetCommitJoin

namespace TwoPermutationPrototype.QuartetCommit
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Sampling.Quartet (leafAt)
set_option maxRecDepth 8192
set_option maxHeartbeats 1300000
attribute [local irreducible] checkEvaluation qReady QuartetLeaves.groups qGroups packedParentsTrace packedParentGroups rootPrefix

abbrev actual := Artifact.submission

def originalLeaf (oracle : Oracle) (msg : Message) (salts : CompleteSaltTape) :=
  leafAt (pinnedFullLeafDigests (BiPermutation.equiv Block oracle.permutation) msg salts)

theorem actual_leaf_content (oracle : Oracle) (msg : Message) (packed : BitVec (128*LENGTH)) :
    let start := qReady (actual.initialState .commit msg) packed
    let done := (checkEvaluation oracle (QuartetLeaves.groups 4096 0 start)).1
    let salts := splitBlocks 128 LENGTH packed
    PaddedLeaves (memoryView done) (fun i => digestWords (originalLeaf oracle msg salts i)) ∧
      ∀ i : Index, window (memoryView done) (qSalt i.val)=saltWords (salts i) := by
  let start := qReady (actual.initialState .commit msg) packed
  have r:=q_ready_regs _ (show CommitEntry (actual.initialState .commit msg) from ⟨rfl,rfl,rfl,rfl⟩) packed
  obtain ⟨p,h⟩ := QuartetLeaves.finished_padding_and_children oracle start r (ready_padding msg packed)
  refine ⟨⟨p.1,?_⟩,?_⟩
  · intro i hi;rw [p.2 i hi]
    let ix : Index := ⟨i,hi⟩
    have dig := ready_leaf_reference oracle msg packed ix
    change lowDigest (replyWords (QuartetLeaves.pinnedFinalReply oracle (memoryView start) i))=digestWords (originalLeaf oracle msg _ i)
    rw [originalLeaf,leafAt,dif_pos (show i<LENGTH from hi),←dig]
    funext j;exact low_digest_word _ j
  · intro i;exact (h i.val i.isLt).trans (ready_salts _ packed i)

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
  rw [addr];exact w.trans (low_digest_word _ ⟨k,hk⟩)

theorem ready_upper_content (oracle : Oracle) (msg : Message) (salts : CompleteSaltTape)
    (leafState : MachineState) (ready : PaddedLeaves (memoryView leafState) (fun i => digestWords (originalLeaf oracle msg salts i))) :
    let quad := (checkEvaluation oracle (qGroups 8192 0 (qStartPrefix leafState 3))).1
    UpperContent (upStartPrefix quad 6) (physicalHeap oracle msg salts) (memoryView leafState) 4194303 := by
  let cs := fun i => digestWords (originalLeaf oracle msg salts i)
  let s:=qStartPrefix leafState 3
  let quad := (checkEvaluation oracle (qGroups 8192 0 s)).1
  have inv : QuadPrefix oracle (memoryView leafState) cs s 0 := ⟨fun _ h => False.elim (by omega),fun _ _ _ => rfl⟩
  have post := q_groups_content oracle (memoryView leafState) cs s 0 8192 (by decide) ready inv
  exact upper_from_quad oracle msg salts leafState quad post
end TwoPermutationPrototype.QuartetCommit
