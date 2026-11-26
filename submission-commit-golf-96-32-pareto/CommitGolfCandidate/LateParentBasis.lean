import CommitGolfCandidate.LatePrefix
import CommitGolfCandidate.LateTreeMemory
import CommitGolfCandidate.LateCachedTree

namespace CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

private theorem start_gaps (m : Message) (ws : List PairCoins) (len : ws.length=pairCount) :
    Gaps (ready (sampled m ws)) := by
  let s := setupState (startState m) 16
  have a : AtPair s 0 := setup_pair (startState m) rfl rfl
  have setupMem (q : MachineState) : (setupState q 16).mem=q.mem := rfl
  have prepareMem (q : MachineState) : (ready q).mem=q.mem := rfl
  intro p hp
  have small : gapAddr p+32 ≤ rowBase := by
    change p < 16777216 at hp; unfold gapAddr rowBase; omega
  have range : gapAddr p+32 ≤ MEMORY_BYTES := by change _ ≤ 5905584160 at small; change _ ≤ 2^36; omega
  have eq := apply_preserves_buffer ws 0 s a (by omega) (gapAddr p) 32
    (by change _ ≤ 2^36 at range; omega) (by intro j _ _; left; unfold pairAddress; omega)
  exact (read_congr_mem _ _ _ _ (prepareMem (sampled m ws))).trans
    (eq.trans ((read_congr_mem _ _ _ _ (setupMem (startState m))).trans
      (initial_empty m _ _ (by unfold gapAddr;omega) range)))

private theorem leaf_fold_gaps (h : Compression) (n k : Nat) (s : MachineState)
    (atStart : AtLeaf s k) (g : Gaps s) (bound : k+n≤LENGTH) :
    Gaps (leafFold h n k s) := by
  induction n generalizing k s with
  | zero => exact g
  | succ n ih =>
    have cnt : 32*(k/32)+(slotIndex k).val = k := Nat.div_add_mod k 32
    have hi : k < LENGTH := by omega
    have e := leaf_state_memory h s (k/32) (slotIndex k) (toRegs atStart)
    rw [cnt] at e
    have newGaps := leaf_keeps_gaps h s ⟨k,hi⟩ g
    exact ih (k+1) _ (after_regs h s k hi atStart)
      (fun p hp => (read_congr_mem _ _ _ _ ((tail_mem h s k).trans e)).trans (newGaps p hp)) (by omega)

theorem leaves_done_gaps (o : Oracle) (m : Message) (ws : List PairCoins) (len : ws.length=pairCount) :
    Gaps (leavesDone o m ws) :=
  leaf_fold_gaps _ LENGTH 0 _ (hash_start m ws len) (start_gaps m ws len) (by omega)

private theorem fin_lookup {α : Type} (n : Nat) (f : Fin n → α) (j : Fin n) (defaultValue : α) :
    ((List.finRange n).map f)[j.val]?.getD defaultValue = f j := by
  have hi : j.val < (List.finRange n).length := by simpa only [List.length_finRange] using j.isLt
  simp only [List.getElem?_map,List.getElem?_eq_getElem hi,List.getElem_finRange,Option.map_some,Option.getD_some]
  congr 1

attribute [local irreducible] List.finRange

theorem initial_nodes (o : Oracle) (m : Message) (ws : List PairCoins) (len : ws.length=pairCount) :
    LevelsThrough o.compression (fun k => (initialList o.compression m (wordTape ws))[k]?.getD 0)
      0 (leavesDone o m ws) := by
  intro l hl j hj
  have zero : l=0 := by omega
  subst l
  change j < LENGTH at hj
  let idx : Index := ⟨j,hj⟩
  have fit : (initialList o.compression m (wordTape ws))[j]?.getD 0 =
      leaf o.compression (idx.val.testBit 0) (wordTape ws idx) (m idx) :=
    fin_lookup LENGTH (fun i => leaf o.compression (i.val.testBit 0) (wordTape ws i) (m i)) idx 0
  exact ((leaves_done_contents o m ws len).stored idx hj).trans fit.symm

end CommitGolfCandidate.Late
