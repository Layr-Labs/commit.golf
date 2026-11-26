import CommitGolfCandidate.TruncTruthDefs
namespace CommitGolfCandidate.Trunc
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 12000
set_option maxHeartbeats 45000
attribute [local irreducible] checkEvaluation fixedParents parentProgram commitLeaves commitInputReady enterState readBuffer observedState

private theorem initialRead (o : Oracle) (q : Nat) (s : MachineState) (f : ParentFrame q (enterState s))
    (small : q<LENGTH) (a n : Nat) (bound : a+n≤2^64)
    (sep : ∀ i,0< i → i≤q → a+n≤heapBase+heapOffset i ∨ heapBase+heapOffset i+32≤a) :
    readBuffer (fixedParents o q (enterState s)) a n=readBuffer s a n :=
  (parentsOutside o q (enterState s) f small a n bound sep).trans
    (read_buffer_memory_congr (enterState s) s (entryMem s) a n)

theorem keptRead (o : Oracle) (m : Message) (salt : BitVec (128*LENGTH)) (a n : Nat) (b : a+n≤2^64)
    (sep : ∀ i,0< i → i≤2^24-1 → a+n≤heapBase+heapOffset i ∨ heapBase+heapOffset i+32≤a) :
    readBuffer (parentsState o m salt) a n=readBuffer (leavesState o m salt) a n :=
  initialRead o (2^24-1) (leavesState o m salt) (startFrame o m salt) (by decide) a n b sep
end CommitGolfCandidate.Trunc
