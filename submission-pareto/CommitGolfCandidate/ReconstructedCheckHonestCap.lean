import CommitGolfCandidate.ReconstructedCheckHonestCapHeaders

namespace CommitGolfCandidate.Reconstruction.CheckHonestCap
open CommitGolf RiscvZkvm.Rv64 TwoPermutationPrototype TwoPermutationPrototype.RV64
open CheckHonestCapLow CheckCapLowMemory CapSchedule Encoding Wire
set_option maxRecDepth 14000
set_option maxHeartbeats 1400000

theorem recover (t : Encoding.Tree) (canonical : RecordDigits.canonical t) (d : Nat) (depth : d≤9)
    (ids : List Nat) (no : ids.Nodup) (fs tail : List Field) (m : Memory) :
    let w := lows d
    let s := pack (fs++(ids.flatMap (low t d)++(headers t d ids++tail)))
    let out := CheckCapHeaders.result d (fill s w ids (bits fs) m) ids s (bits fs+w*ids.length)
    out.valid=true ∧ ∀ id∈ids,∀ k : Fin 4,
      out.data (CheckCapLowStore.cell id+k.val)=CheckParentWords.digWord (t d id) k := by
  let w := lows d
  let a := fs++ids.flatMap (low t d)
  let hs := headers t d ids
  let s := pack (fs++(ids.flatMap (low t d)++(hs++tail)))
  let lowMem := fill s w ids (bits fs) m
  have range : 192≤w ∧ w≤256 := (by decide : ∀ z : Fin 10,192≤lows z.val ∧ lows z.val≤256) ⟨d,by omega⟩
  have low := items t d range.2 range.1 ids no fs (hs++tail) m s rfl
  have sz (j : Nat) : bits (CapSchedule.low t d j)=w := by rw [CapSchedule.low,low_bits];dsimp [w] at *;omega
  have bitCount : bits a=bits fs+w*ids.length := by rw [show a=fs++ids.flatMap (CapSchedule.low t d) from rfl,bits_append,flat_bits ids _ w sz]
  have layout : s=pack (a++(hs++tail)) := by simp [s,a,List.append_assoc]
  have bound (j : Nat) : digit t d j<base d := RecordDigits.digit_bound t canonical ⟨d,by omega⟩ j
  by_cases paid : 8≤d
  · have upper : w=224 ∧ base d=211 := by
      rcases (by omega : d=8 ∨ d=9) with rfl|rfl <;> decide
    have repaired := CheckHonestCapHeaders.run t d upper.1 (by intro j;exact (bound j).trans_eq upper.2) ids no
      a tail s (by simpa only [hs,headers,ite_eq_left paid] using layout) lowMem low
    change (CheckCapHeaders.result d lowMem ids s (bits fs+w*ids.length)).valid=true ∧ _
    unfold CheckCapHeaders.result
    rw [ite_eq_right (by omega : ¬d<8),←bitCount]
    exact ⟨repaired.1,fun id h k => words (repaired.2.1 id h) k⟩
  · have tiny : d<8 := by omega
    have baseOne : base d=1 := (by decide : ∀ z : Fin 8,base z.val=1) ⟨d,tiny⟩
    change (CheckCapHeaders.result d lowMem ids s (bits fs+w*ids.length)).valid=true ∧ _
    unfold CheckCapHeaders.result
    rw [ite_eq_left tiny]
    refine ⟨rfl,?_⟩
    intro id h k
    have v := low id h
    have b := bound id
    have zero : digit t d id=0 := by omega
    unfold Low at v
    rw [zero,show CheckCapScanData.W 0 <<< (lows d-192)=(0:Word) from BitVec.zero_shiftLeft _] at v
    exact words v k

end CommitGolfCandidate.Reconstruction.CheckHonestCap
