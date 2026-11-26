import CommitGolfCandidate.ReconstructedCheckHonestCapLow

namespace CommitGolfCandidate.Reconstruction.CheckHonestCapPatch
open CommitGolf RiscvZkvm.Rv64 TwoPermutationPrototype TwoPermutationPrototype.RV64
open CheckGroupRadix CheckGroupWalk CheckHonestCapLow Encoding CapSchedule
open CheckCapLowStore (cell)
set_option maxRecDepth 15000
set_option maxHeartbeats 1300000

theorem same (m : Memory) (id j v : Nat) (different : j≠id) : Equal (fix m id v) m j := by
  intro k hk
  apply unaffected;unfold cell top CheckCapScanData.cap CheckGroupRadix.cap;omega

theorem patchOther (m : Memory) (xs : List Nat) (v j : Nat) (free : j∉xs) : Equal (patch m xs v) m j := by
  induction xs generalizing m v with
  | nil => exact fun _ _ => rfl
  | cons a xs ih =>
    have ne : j≠a := fun eq => free (List.mem_cons.mpr (Or.inl eq))
    have more : j∉xs := fun h => free (List.mem_cons_of_mem _ h)
    exact fun k hk => (ih _ _ more k hk).trans (same m a j _ ne k hk)

private theorem updated (m : Memory) (t : Encoding.Tree) (d id : Nat) (w : lows d=224) (good : Low m t d id) :
    Full (fix m id (digit t d id)) t d id := by
  change view (fix m id (digit t d id)) id 0=t d id
  change view m id (W (digit t d id) <<< (lows d-192))=t d id at good
  rw [w] at good
  apply Eq.trans _ good
  have atTop : top id=cell id+3 := rfl
  simp only [view,fix,atTop,writeWord,ite_eq_left rfl,ite_eq_right (by omega : cell id≠cell id+3),
    ite_eq_right (by omega : cell id+1≠cell id+3),ite_eq_right (by omega : cell id+2≠cell id+3)]
  change CheckEdge.digest _ _ _ ((0#64) ||| (m (cell id+3) ||| (W _ <<< (32 : Nat))))=_
  rw [BitVec.zero_or,BitVec.or_comm (m (cell id+3))]

theorem patchFull (t : Encoding.Tree) (d : Nat) (w : lows d=224) (bound : ∀ j,digit t d j<211)
    (m : Memory) (ids : List Nat) (no : ids.Nodup) (good : ∀ j∈ids,Low m t d j) :
    ∀ j∈ids,Full (patch m ids (headerValue (digit t d) ids)) t d j := by
  induction ids generalizing m with
  | nil => intro j h;cases h
  | cons id xs ih =>
    let v := headerValue (digit t d) xs
    have z := bound id
    have selected : headerValue (digit t d) (id::xs)%211=digit t d id := by
      rw [headerValue,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt z]
    have next : headerValue (digit t d) (id::xs)/211=v := by
      rw [headerValue,Nat.add_mul_div_left _ _ (by decide),Nat.div_eq_of_lt z,Nat.zero_add]
    rw [patch,selected,next]
    obtain ⟨apart,tail⟩ := List.nodup_cons.mp no
    intro j member
    rcases List.mem_cons.mp member with h|h
    · subst j
      exact full_eq (patchOther _ xs v id apart) t d (updated m t d id w (good id List.mem_cons_self))
    · apply ih _ tail _ j h
      intro k hk
      have ne : k≠id := fun eq => apart (eq ▸ hk)
      exact low_eq (same m id k _ ne) t d (good k (List.mem_cons_of_mem _ hk))

end CommitGolfCandidate.Reconstruction.CheckHonestCapPatch
