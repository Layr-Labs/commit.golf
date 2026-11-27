import CommitGolfCandidate.Stage3cNodeFrame
import CommitGolfCandidate.Stage3cLeafEntry
import CommitGolfCandidate.Stage3cPrefix
namespace CommitGolfCandidate.Chained.BinaryMachine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open CommitGolfCandidate.Late (PairCoins leaf gapOffset SaltTape)
def gapAddr (p : Nat) := 4294975488+96*p+64

theorem node_gap (d j p : Nat) :
    nodeAddress d j+32 ≤ gapAddr p ∨ gapAddr p+32 ≤ nodeAddress d j := by
  unfold nodeAddress gapOffset gapAddr levelOffset
  omega

theorem gap_index (d p : Nat) :
    nodeAddress d (2*p)+64 = gapAddr (LENGTH-levelCount d+p) := by
  unfold nodeAddress gapOffset gapAddr levelOffset
  omega

def AllGaps (s : MachineState) : Prop := ∀ p < LENGTH, readBuffer s (gapAddr p) 32 = 0

private theorem gap_valid {p : Nat} (small : p < LENGTH) : gapAddr p+32 ≤ rowBase := by
  change p < 16777216 at small
  unfold gapAddr rowBase; omega

theorem leaf_keeps_gaps (h : Compression) (s : MachineState) (i : Index) (g : AllGaps s) :
    AllGaps (writeLeaf h s i) := by
  intro p hp
  have top := gap_valid hp
  have hi := i.isLt; change i.val < 16777216 at hi
  apply (write_leaf_frame h s i _ 32 (by unfold rowBase at top; omega) _).trans (g p hp)
  constructor
  · right; unfold msgAddr gapAddr; omega
  · left; unfold contentAddr rowAddr; omega
  · exact (node_gap 0 i p).symm

private theorem start_gaps (m : Message) (ws : List PairCoins) (len : ws.length=pairCount) :
    AllGaps (prepareLeaves (sampled m ws)) := by
  let s:=prepared m
  have a : AtPair s 0 := ready m
  have setupMem (q : MachineState) : (initializeOps.foldl execInstrBr q).mem=q.mem := rfl
  have prepareMem (q : MachineState) : (prepareLeaves q).mem=q.mem := rfl
  intro p hp
  have small : gapAddr p+32 ≤ rowBase := by
    change p < 16777216 at hp; unfold gapAddr rowBase; omega
  have range : gapAddr p+32 ≤ MEMORY_BYTES := by change _ ≤ 5905588224 at small; change _ ≤ 2^36; omega
  have eq := apply_preserves_buffer ws 0 s a (by omega) (gapAddr p) 32
    (by change _ ≤ 2^36 at range; omega) (by intro j _ _; left; unfold pairAddress; omega)
  exact (read_congr_mem _ _ _ _ (prepareMem (sampled m ws))).trans
    (eq.trans ((read_congr_mem _ _ _ _ (setupMem (startState m))).trans
      (initial_empty m _ _ (by unfold gapAddr;omega) range)))

private theorem leaf_fold_gaps (h : Compression) (n k : Nat) (s : MachineState)
    (atStart : AtLeaf s k) (g : AllGaps s) (bound : k+n≤LENGTH) :
    AllGaps (leafFold h n k s) := by
  induction n generalizing k s with
  | zero => exact g
  | succ n ih =>
    have hi:k<LENGTH:=by omega
    have e:=afterLeafMemory h atStart.toLeafRegs hi
    have next:=leaf_keeps_gaps h s ⟨k,hi⟩ g
    exact ih (k+1) _ (after_at h atStart hi) (fun p hp=>(read_congr_mem _ _ _ _ e).trans (next p hp)) (by omega)

theorem leaves_done_gaps (o : Oracle) (m : Message) (ws : List PairCoins) (len : ws.length=pairCount) :
    AllGaps (leavesDone o m ws) :=
  leaf_fold_gaps _ LENGTH 0 _ (initial_leaf _ (leaf_initial m ws len)) (start_gaps m ws len) (by omega)

private theorem fin_lookup {α : Type} (n : Nat) (f : Fin n → α) (j : Fin n) (defaultValue : α) :
    ((List.finRange n).map f)[j.val]?.getD defaultValue = f j := by
  have hi : j.val < (List.finRange n).length := by simpa only [List.length_finRange] using j.isLt
  simp only [List.getElem?_map,List.getElem?_eq_getElem hi,List.getElem_finRange,Option.map_some,Option.getD_some]
  congr 1

attribute [local irreducible] List.finRange


theorem initial_tree (o : Oracle) (m : Message) (ws : List PairCoins) (len : ws.length=pairCount) :
    TreeState o.compression (fun k=>(initialList o.compression m (wordTape ws))[k]?.getD 0) (wordTape ws) 0
      (leavesDone o m ws) := by
  have cn:=leaves_done_contents o m ws len
  refine ⟨?_,cn.salts,?_⟩
  · intro d le i hi;have eqn : d=0 := by omega
    subst d;let j : Index:=⟨i,hi⟩
    have fit : (initialList o.compression m (wordTape ws))[i]?.getD 0=leaf o.compression (j.val.testBit 0) (wordTape ws j) (m j) :=
      fin_lookup LENGTH (fun z=>leaf o.compression (z.val.testBit 0) (wordTape ws z) (m z)) j 0
    exact (cn.stored j j.isLt).trans fit.symm
  · intro h p hp
    have ok:=gap_limit h p hp
    have gidx : LENGTH-levelCount h.val+p<LENGTH := by rw [tagAddr,gap_index] at ok;unfold gapAddr rowBase at ok;change _<16777216;omega
    have blank:=leaves_done_gaps o m ws len _ gidx
    have joined : readBuffer (leavesDone o m ws) (tagAddr h p) 32=0 := by rw [tagAddr,gap_index];exact blank
    constructor
    · have sl:=read_buffer_slice (leavesDone o m ws) (tagAddr h p) 32 8 24 (by decide)
      rw [joined] at sl;exact sl.symm
    · intro _;have sl:=read_buffer_slice (leavesDone o m ws) (tagAddr h p) 32 0 8 (by decide)
      rw [joined,Nat.add_zero] at sl;exact sl.symm.trans (by rfl)
end CommitGolfCandidate.Chained.BinaryMachine
