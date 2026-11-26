import CommitGolfCandidate.TruncTruthFrame
import CommitGolfCandidate.TruncLeafReads
namespace CommitGolfCandidate.Trunc
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 12000
set_option maxHeartbeats 75000
attribute [local irreducible] checkEvaluation fixedParents parentProgram commitLeaves commitInputReady enterState

attribute [local irreducible] readBuffer observedState parentsState leavesState

theorem leafTruth (o : Oracle) (m : Message) (a : BitVec (128*LENGTH)) (i : Index) :
    heapDigest (parentsState o m a) heapBase (LENGTH+i.val)=leafDigest o.compression i (a.extractLsb' (128*i.val) 128) (m i) := by
  have hi : i.val<16777216:=i.isLt
  let pos:=heapBase+heapOffset (LENGTH+i.val)
  have addr : pos=5100277792+heapOffset i.val := by dsimp only [pos];rw [heap_offset_leaf];unfold heapBase;omega
  have b : pos+32≤2^64 := by dsimp [pos,heapBase,heapOffset,LENGTH,LOG_LENGTH];omega
  have keep:=keptRead o m a pos 32 b (by
    intro j _ lo;have sep:=heap_offset_disjoint (LENGTH+i.val) j (by change 16777216+i.val≠j;omega)
    dsimp only [pos];omega)
  apply keep.trans
  rw [addr];exact inheritedLeaf o m a i

theorem saltTruth (o : Oracle) (m : Message) (a : BitVec (128*LENGTH)) (i : Index) :
    readBuffer (parentsState o m a) (5905584160+16*i.val) 16=a.extractLsb' (128*i.val) 128 := by
  have hi : i.val<16777216:=i.isLt
  exact (keptRead o m a _ _ (by omega) (by intro j pos bound;right;unfold heapBase heapOffset;omega)).trans
    (inheritedSalt o m a i)
end CommitGolfCandidate.Trunc
