import CommitGolfCandidate.ReconstructedHonestHeap
import CommitGolfCandidate.ReconstructedCapEntry
import CommitGolfCandidate.ReconstructedCapOrder
import CommitGolfCandidate.ReconstructedCapDigits

namespace CommitGolfCandidate.Reconstruction.CapSchedule
open CommitGolf TwoPermutationPrototype.Sampling Frontier Encoding HonestCapPlan HonestSizeSchedule
set_option maxRecDepth 14000

def active (f : Nat→Bool) (d : Nat) := CapOrder.window (row f (9-d)) 0 (2^d)
def pending (f : Nat→Bool) (d : Nat) := CapOrder.ids (2^d) (row f (9-d)) 0 (pairs d)
def low (tree : Encoding.Tree) (d j : Nat) := lowFields (tree d j) (lows d)
def digit (tree : Encoding.Tree) (d j : Nat) := highDigit (tree d j) (lows d)
def rest (tree : Encoding.Tree) (f : Nat→Bool) (d : Nat) := cap tree d (active f d)
def headers (tree : Encoding.Tree) (d : Nat) (xs : List Nat) := if 8≤d then capHeaders (digit tree d) xs else []

theorem start (ps : Positions) : active (CapEntry.flags ps) 9=Frontier.flags (ps.sort (·≤·)) := by
  let xs := Frontier.flags (ps.sort (·≤·))
  have len (v : List (Fin (2^24))) (bs : List Bool) : (v.foldl mark bs).length=bs.length := by
    induction v generalizing bs with
    | nil => rfl
    | cons i v ih => rw [List.foldl_cons,ih];simp [mark]
  have size : xs.length=512 := (len _ _).trans (List.length_replicate)
  change CapOrder.window (fun i => xs[i]?.getD false) 0 512=xs
  apply List.ext_getElem
  · rw [CapOrder.window_length,size]
  · intro n _ h;rw [CapOrder.window_get _ _ _ _ (size ▸ h),Nat.zero_add,List.getElem?_eq_getElem h];rfl

theorem scan (f : Nat→Bool) (d : Nat) (small : d≤9) (pos : 0<d) :
    Frontier.scan (2^d) (active f d)=(active f (d-1),pending f d) := by
  have p := (HonestCapState.powers d pos).1
  have step := CapOrder.scan_window (2^d) (row f (9-d)) 0 (pairs d)
  simp only [Nat.mul_zero,Nat.add_zero,←p] at step
  change Frontier.scan (2^d) (CapOrder.window (row f (9-d)) 0 (2^d))=_
  rw [step]
  have depth : 9-(d-1)=(9-d)+1 := by omega
  unfold active pending
  rw [depth];rfl

theorem split (tree : Encoding.Tree) (f : Nat→Bool) (d : Nat) (small : d≤9) (pos : 0<d) :
    rest tree f d=(pending f d).flatMap (low tree d) ++ headers tree d (pending f d) ++ rest tree f (d-1) := by
  cases d with
  | zero => omega
  | succ e =>
    unfold rest
    simp only [cap,scan f (e+1) small pos];rfl

theorem header_step (f : Nat→Nat) (xs : List Nat) (nonempty : xs≠[]) :
    capHeaders f xs=⟨headerValue f (xs.take 4),31⟩::capHeaders f (xs.drop 4) := by
  match xs with
  | [] => contradiction
  | [_] | [_,_] | [_,_,_] | _::_::_::_::_ => rfl

theorem span (ps : Positions) (tree : Encoding.Tree) (salts : OpenedSalts ps) :
    Wire.bits (fields tree ps salts)+192 < OpeningPut.capacity*64 := by
  have bound : ps.card≤2^24 := by change ps.card≤LENGTH;simpa [Index] using Finset.card_le_univ ps
  have cap := HonestHeap.cursor_all (ps.sort (·≤·))
  have len : (ps.sort (·≤·)).length=ps.card := Finset.length_sort _
  change Frontier.cursor (ps.sort (·≤·)) ≤ 3633*(ps.sort (·≤·)).length+119472 at cap
  rw [len] at cap
  rw [all_bits];unfold OpeningPut.capacity;omega

theorem prefix_room (fs more : List Wire.Field) (cap : Wire.bits (fs++more)+192 < OpeningPut.capacity*64) :
    (Wire.bits fs+192)/64<OpeningPut.capacity := by rw [Wire.bits_append] at cap;omega

theorem get (f : Nat→Nat) (xs : List Nat) (i : Nat) (hi : i < xs.length) :
    headerValue f (xs.drop i)=f xs[i]+211*headerValue f (xs.drop (i+1)) := by
  induction i generalizing xs with
  | zero =>
    cases xs with
    | nil => cases hi
    | cons a b => rfl
  | succ i ih =>
    cases xs with
    | nil => cases hi
    | cons a b => exact ih b (by simpa using hi)

end CommitGolfCandidate.Reconstruction.CapSchedule
