import CommitGolfCandidate.TruncHeapStates
namespace CommitGolfCandidate.Trunc
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 12000
set_option maxHeartbeats 75000
attribute [local irreducible] checkEvaluation fixedParents parentProgram commitLeaves commitInputReady enterState

private theorem observedRead (o : Oracle) (c : OracleComp World MachineState) (a n : Nat) (v : BitVec (8*n))
    (h : readBuffer (checkEvaluation o c).1 a n=v) : readBuffer (observedState o c) a n=v := h

attribute [local irreducible] observedState readBuffer

theorem inheritedLeaf (o : Oracle) (m : Message) (a : BitVec (128*LENGTH)) (i : Index) :
    readBuffer (leavesState o m a) (5100277792+heapOffset i.val) 32=leafDigest o.compression i (a.extractLsb' (128*i.val) 128) (m i) := by
  have h:=observedRead o (commitLeaves (commitInputReady m a) (LENGTH/32)) _ _ _ (commit_input_leaf_heap o m a i)
  rw [show LENGTH/32=2^19 by decide] at h;exact h

private theorem leafSalt (oracle : Oracle) (message : Message) (answer : BitVec (128*LENGTH)) (index : Index) :
    readBuffer (checkEvaluation oracle (commitLeaves (commitInputReady message answer) (LENGTH/32))).1
      (5905584160+16*index.val) 16=answer.extractLsb' (128*index.val) 128 := by
  let ready:=commitInputReady message answer
  have hL : LENGTH=16777216 := rfl
  have input:=commit_input_registers message answer
  have indexBound : index.val<2^24 := index.isLt
  rw [commit_leaves_preserves oracle ready 4072 5905584160 5100277792 (LENGTH/32)
    (5905584160+16*index.val) 16 input.1 input.2.2.1 input.2.2.2.1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)
    (Or.inr (by change 4072 + 8192*(16777216/32) ≤ _; omega))
    (by
      intro i hi
      have := heap_offset_bound i (2^23) (by rw [hL] at hi; omega)
      exact Or.inr (by omega))]
  exact commit_ready_salt message answer index


theorem inheritedSalt (o : Oracle) (m : Message) (a : BitVec (128*LENGTH)) (i : Index) :
    readBuffer (leavesState o m a) (5905584160+16*i.val) 16=a.extractLsb' (128*i.val) 128 := by
  have h:=observedRead o (commitLeaves (commitInputReady m a) (LENGTH/32)) _ _ _ (leafSalt o m a i)
  rw [show LENGTH/32=2^19 by decide] at h;exact h

end CommitGolfCandidate.Trunc
