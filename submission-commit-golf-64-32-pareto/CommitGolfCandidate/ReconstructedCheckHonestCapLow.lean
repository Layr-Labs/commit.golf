import CommitGolfCandidate.ReconstructedCheckHonestFields
import CommitGolfCandidate.ReconstructedCheckCapLowMemory
import CommitGolfCandidate.ReconstructedCheckCapHeaders

namespace CommitGolfCandidate.Reconstruction.CheckHonestCapLow
open CommitGolf RiscvZkvm.Rv64 TwoPermutationPrototype TwoPermutationPrototype.RV64
open CheckCapLowStore (cell)
open CheckCapLowMemory (fill)
open CheckCapLowItem (data)
open CheckCapScanData (W)
open Encoding CapSchedule
set_option maxRecDepth 14000
set_option maxHeartbeats 1200000

def view (m : Memory) (id : Nat) (add : Word) :=
  CheckEdge.digest (m (cell id)) (m (cell id+1)) (m (cell id+2)) (add ||| m (cell id+3))

def Low (m : Memory) (t : Encoding.Tree) (d id : Nat) :=
  view m id (W (digit t d id) <<< (lows d-192))=t d id
def Full (m : Memory) (t : Encoding.Tree) (d id : Nat) := view m id 0=t d id

def Equal (m n : Memory) (id : Nat) := ∀ k<4,m (cell id+k)=n (cell id+k)

theorem view_eq {m n : Memory} {id : Nat} (h : Equal m n id) (add : Word) : view m id add=view n id add := by
  unfold view
  rw [show m (cell id)=n (cell id) from h 0 (by decide),h 1 (by decide),h 2 (by decide),h 3 (by decide)]

theorem low_eq {m n : Memory} {id : Nat} (h : Equal m n id) (t : Encoding.Tree) (d : Nat) (good : Low n t d id) :
    Low m t d id := (view_eq h _).trans good

theorem full_eq {m n : Memory} {id : Nat} (h : Equal m n id) (t : Encoding.Tree) (d : Nat) (good : Full n t d id) :
    Full m t d id := (view_eq h _).trans good

theorem untouched (m : Memory) (id j s c w : Nat) (different : j≠id) : Equal (data m id s c w) m j := by
  intro k hk
  have off (l : Nat) (hl : l<4) : cell j+k≠cell id+l := by unfold cell;omega
  simp only [data,CheckCapLowStore.copy,writeWord,ite_eq_right (off 3 (by decide)),ite_eq_right (off 2 (by decide)),
    ite_eq_right (off 1 (by decide)),ite_eq_right (show cell j+k≠cell id from off 0 (by decide))]

theorem untouchedFill (m : Memory) (ids : List Nat) (j s c w : Nat) (absent : j∉ids) : Equal (fill s w ids c m) m j := by
  induction ids generalizing m c with
  | nil => exact fun _ _ => rfl
  | cons h xs ih =>
    have ne : j≠h := fun eq => absent (List.mem_cons.mpr (Or.inl eq))
    have more : j∉xs := fun p => absent (List.mem_cons_of_mem _ p)
    exact fun k hk => (ih _ _ more k hk).trans (untouched m h j s c w ne k hk)

private theorem placed (m : Memory) (id s c w : Nat) (dig : Nat) :
    view (data m id s c w) id (W dig <<< (w-192))=CheckLowerInput.sibling s c w dig := by
  simp [view,data,CheckCapLowStore.copy,CheckLowerInput.sibling,writeWord]

theorem items (t : Encoding.Tree) (d : Nat) (wBound : lows d≤256) (lo : 192≤lows d)
    (ids : List Nat) (nodup : ids.Nodup) (a tail : List Wire.Field) (m : Memory) (s : Nat)
    (bytes : s=Wire.pack (a++(ids.flatMap (low t d)++tail))) : ∀ j∈ids,
      Low (fill s (lows d) ids (Wire.bits a) m) t d j := by
  induction ids generalizing a m with
  | nil => intro j p;cases p
  | cons id xs ih =>
    obtain ⟨fresh,no⟩ := List.nodup_cons.mp nodup
    let more := xs.flatMap (low t d)++tail
    let next := a++low t d id
    have here : s=Wire.pack ((a++low t d id)++more) := by rw [bytes];simp [List.append_assoc,more]
    have move : Wire.bits next=Wire.bits a+lows d := by
      rw [show next=a++low t d id from rfl,Wire.bits_append,show Wire.bits (low t d id)=192+(lows d-192) from Encoding.low_bits ..];omega
    intro j mem
    rcases List.mem_cons.mp mem with eq|belongs
    · subst j
      apply low_eq (untouchedFill _ xs id s _ _ fresh) t d
      unfold Low
      rw [show CapSchedule.digit t d id=Encoding.highDigit (t d id) (lows d) from rfl,placed,here]
      exact CheckHonestFields.sibling a more _ _ wBound
    · change Low (fill s (lows d) xs (Wire.bits a+lows d) (data m id s (Wire.bits a) (lows d))) t d j
      rw [←move]
      exact ih no next _ here j belongs

theorem words {m : Memory} {t : Encoding.Tree} {d id : Nat} (good : Full m t d id) (k : Fin 4) :
    m (cell id+k.val)=CheckParentWords.digWord (t d id) k := by
  change CheckEdge.digest _ _ _ (0 ||| m (cell id+3))=t d id at good
  rw [show (0:Word) ||| m (cell id+3)=m (cell id+3) from BitVec.zero_or] at good
  rw [←good,CheckLowerInput.digWords]
  fin_cases k <;> rfl

end CommitGolfCandidate.Reconstruction.CheckHonestCapLow
