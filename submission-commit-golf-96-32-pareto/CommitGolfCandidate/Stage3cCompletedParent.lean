import CommitGolfCandidate.Stage3cParent
import CommitGolfCandidate.ChainedFinalHazard
namespace CommitGolfCandidate.Chained
open CommitGolf

def stageInput (H : Compression) (h : Height) (l r : Output) (j : Nat) :=
  (parentQueries H h l r j).getLastD 0

def Recorded (t : Trace) (H : Compression) (h : Height) (l r : Output) :=
  ∀ j<calls h, ∃ i, t.input i=stageInput H h l r j ∧ t.output i=H (stageInput H h l r j)

theorem chain_in_trace (t : Trace) (H : Compression) (h : Height) (l r : Output) (recorded : Recorded t H h l r) :
    Completed canonicalEncoding calls t (workClass h,r ++ l) ∧
    finalOutput canonicalEncoding calls t (workClass h,r ++ l)=H ((queries H h l r).getLastD 0) := by
  classical
  let row (j : Nat) : Fin t.size :=
    if v : j<calls h then (recorded j v).choose else (recorded 0 (calls_positive h)).choose
  have entry (j : Nat) (v : j<calls h) :
      t.input (row j)=stageInput H h l r j ∧ t.output (row j)=H (stageInput H h l r j) := by
    dsimp only [row];rw [dif_pos v];exact (recorded j v).choose_spec
  let e : Evaluation canonicalEncoding calls t := {
    height:=workClass h, seed:=r ++ l, positive:=calls_positive _, bounded:=calls_bound _, row:=row
    first := (entry 0 (calls_positive h)).1
    next := by
      intro j v
      rw [workClass_calls] at v
      rw [(entry (j+1) v).1,(entry j (by omega)).2]
      exact List.getLastD_concat }
  refine ⟨⟨e,rfl⟩,?_⟩
  have f:=finalOutput_of_evaluation e
  change finalOutput canonicalEncoding calls t (workClass h,r ++ l)=t.output (row (calls (workClass h)-1)) at f
  rw [workClass_calls] at f
  exact f.trans (entry _ (Nat.sub_lt (calls_positive _) (by decide))).2

theorem collision_from_parent (t : Trace) (H : Compression) (h : Height) (l r l' r' : Output)
    (recorded : Recorded t H h l r) (recorded' : Recorded t H h l' r') (diff : (l,r)≠(l',r'))
    (equal : parentDigest H h l r=parentDigest H h l' r') :
    FinalCollision canonicalEncoding calls width t := by
  obtain ⟨before,left⟩:=chain_in_trace t H h l r recorded
  obtain ⟨after,right⟩:=chain_in_trace t H h l' r' recorded'
  obtain ⟨seeds,eq⟩:=parent_witness H h l r l' r' diff equal
  refine ⟨workClass h,r ++ l,r' ++ l',seeds,before,after,?_⟩
  rw [left,right]
  apply BitVec.eq_of_toNat_eq
  have proj (w : Nat) (v : Output) : (lowBits w v).toNat=v.toNat%2^w := by
    exact (BitVec.extractLsb'_toNat 0 w v).trans (by rw [Nat.shiftRight_zero])
  exact (proj _ _).trans (eq.trans (proj _ _).symm)
end CommitGolfCandidate.Chained
