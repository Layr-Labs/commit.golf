import CommitGolfCandidate.S5NodeFrame
import CommitGolfCandidate.S5CachedTree
import CommitGolfCandidate.S5Prefix
namespace CommitGolfCandidate.S5Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open CommitGolfCandidate.Late (PairCoins leaf)

theorem leaf_keeps_gaps (H : Compression) (s : MachineState) (i : Index) (g : Gaps s) : Gaps (writeLeaf H s i) := by
  intro d p k pad
  have top:=padValid _ _ _ pad
  have hi : i.val<16777216:=i.isLt
  apply (write_leaf_frame H s i _ 32 (by unfold rowBase at top;omega) _).trans (g _ _ _ pad)
  constructor
  · right;unfold msgAddr unusedSlotAddr rowAddress;omega
  · left;unfold contentAddr rowAddr rowBase at *;omega
  · exact (node_pad 0 i d p k (by decide) i.isLt pad).symm

private theorem start_gaps (m : Message) (ws : List PairCoins) (len : ws.length=pairCount) :
    Gaps (prepareLeaves (sampled m ws)) := by
  let s:=prepared m
  have at_ : AtPair s 0:=ready m
  have setupMem (q : MachineState) : (initializeOps.foldl execInstrBr q).mem=q.mem := rfl
  have prepareMem (q : MachineState) : (prepareLeaves q).mem=q.mem := rfl
  intro d p k pad
  let a:=unusedSlotAddr d p k
  have high : a+32≤rowBase:=padValid _ _ _ pad
  have low : 4294975488≤a := by dsimp [a,unusedSlotAddr,rowAddress];omega
  have bound : a+32≤MEMORY_BYTES:=high.trans (by decide)
  have aside:=apply_preserves_buffer ws 0 s at_ (by omega) a 32
    (by change _≤2^36 at bound;omega) (by intro j lo _;left;unfold pairAddress;omega)
  exact (read_congr_mem _ _ _ _ (prepareMem (sampled m ws))).trans
    (aside.trans ((read_congr_mem _ _ _ _ (setupMem (startState m))).trans
      (initial_empty m _ _ (by omega) bound)))
private theorem leaf_fold_gaps (h : Compression) (n k : Nat) (s : MachineState)
    (atStart : AtLeaf s k) (g : Gaps s) (bound : k+n≤LENGTH) :
    Gaps (leafFold h n k s) := by
  induction n generalizing k s with
  | zero => exact g
  | succ n ih =>
    have cnt : 256*(k/256)+(slotIndex k).val = k := Nat.div_add_mod k 256
    have hi : k < LENGTH := by omega
    have e := leaf_state_memory h s (k/256) (slotIndex k) (toRegs atStart)
    rw [cnt] at e
    have newGaps := leaf_keeps_gaps h s ⟨k,hi⟩ g
    exact ih (k+1) _ (after_regs h s k hi atStart)
      (fun d p lane pad => (read_congr_mem _ _ _ _ ((tail_mem h s k).trans e)).trans (newGaps _ _ _ pad)) (by omega)

theorem leaves_done_gaps (o : Oracle) (m : Message) (ws : List PairCoins) (len : ws.length=pairCount) :
    Gaps (leavesDone o m ws) :=
  leaf_fold_gaps _ LENGTH 0 _ (leaf_initial m ws len) (start_gaps m ws len) (by omega)

private theorem fin_lookup {α : Type} (n : Nat) (f : Fin n → α) (j : Fin n) (defaultValue : α) :
    ((List.finRange n).map f)[j.val]?.getD defaultValue = f j := by
  have hi : j.val < (List.finRange n).length := by simpa only [List.length_finRange] using j.isLt
  simp only [List.getElem?_map,List.getElem?_eq_getElem hi,List.getElem_finRange,Option.map_some,Option.getD_some]
  congr 1

set_option maxRecDepth 12000
attribute [local irreducible] List.finRange


private theorem initialLeaf (H : Compression) (m : Message) (s : Late.SaltTape) (i : Index) :
    (initialList H m s)[i.val]?.getD 0=Late.leaf H (i.val.testBit 0) (s i) (m i) := by
  unfold initialList LateHiding.leafLayer
  exact (fin_lookup LENGTH (fun j=>LateHiding.leafDigest H (j.val.testBit 0) (s j) (m j)) i 0).trans
    (LateHiding.leaf_digest_eq ..)

theorem initial_tree (o : Oracle) (m : Message) (ws : List PairCoins) (len : ws.length=pairCount) :
    TreeState o.compression (fun k=>(initialList o.compression m (wordTape ws))[k]?.getD 0) (wordTape ws) 0 (leavesDone o m ws) := by
  have cn:=leaves_done_contents o m ws len
  refine ⟨?_,cn.salts,?_⟩
  · intro d depth j inside
    obtain rfl : d=0:=by omega
    let i : Index:=⟨j,inside⟩
    have value : (initialList o.compression m (wordTape ws))[j]?.getD 0=leaf o.compression (i.val.testBit 0) (wordTape ws i) (m i) :=
      initialLeaf o.compression m (wordTape ws) i
    rw [treeNode,if_pos inside,value];exact cn.stored i i.isLt
  · intro d p k pad
    let a:=unusedSlotAddr d p k
    let st:=leavesDone o m ws
    have raw : readBuffer st a 32=0:=leaves_done_gaps o m ws len d p k pad
    constructor
    · have split:=read_buffer_slice st a 32 8 24 (by decide)
      rw [raw] at split;exact split.symm
    · intro _;have split:=read_buffer_slice st a 32 0 8 (by decide)
      rw [raw,Nat.add_zero] at split;exact split.symm
end CommitGolfCandidate.S5Machine
