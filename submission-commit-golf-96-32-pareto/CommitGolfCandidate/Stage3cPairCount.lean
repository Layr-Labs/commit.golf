import CommitGolfCandidate.Stage3cCapPairBody
/-! Only cap pairs that contain a record's bucket are hashed. With 128 records at most 128
of the 256 pairs are touched, so the cap pairs cost at most 128 x 16 = 2048 calls. -/
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Check
open CommitGolf

def touchedAt (H : Compression) (x : CheckInput) (j : Nat) : Bool :=
  touched (lookup H x 128 (2*j)) (lookup H x 128 (2*j+1))
def pairTotal (H : Compression) (x : CheckInput) : Nat → Nat → Nat
  | _, 0 => 0
  | p, n+1 => pairCalls (lookup H x 128 (2*p)) (lookup H x 128 (2*p+1)) + pairTotal H x (p+1) n

theorem pair_total_filter (H : Compression) (x : CheckInput) (p n : Nat) :
    pairTotal H x p n = 16*((List.range' p n).filter (touchedAt H x)).length := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    rw [pairTotal, ih, List.range'_succ, List.filter_cons]
    unfold pairCalls
    by_cases t : touchedAt H x p = true
    · have t' : touched (lookup H x 128 (2*p)) (lookup H x 128 (2*p+1)) = true := t
      rw [if_pos t', if_pos t, List.length_cons]; omega
    · have t' : ¬touched (lookup H x 128 (2*p)) (lookup H x 128 (2*p+1)) = true := t
      rw [if_neg t', if_neg t]; omega

theorem lookup_isSome (H : Compression) (x : CheckInput) (j : Nat) (h : (lookup H x 128 j).isSome = true) :
    ∃ r < 128, bucket x r = j := by
  unfold lookup at h
  rw [Option.isSome_map] at h
  obtain ⟨r, mem, pr⟩ := List.find?_isSome.mp h
  exact ⟨r, List.mem_range.mp mem, by simpa using pr⟩

theorem touched_record (H : Compression) (x : CheckInput) (j : Nat) (h : touchedAt H x j = true) :
    ∃ r < 128, bucket x r / 2 = j := by
  unfold touchedAt touched at h
  rcases Bool.or_eq_true_iff.mp h with a | b
  · obtain ⟨r, hr, e⟩ := lookup_isSome H x (2*j) a; exact ⟨r, hr, by omega⟩
  · obtain ⟨r, hr, e⟩ := lookup_isSome H x (2*j+1) b; exact ⟨r, hr, by omega⟩

theorem pair_total_bound (H : Compression) (x : CheckInput) : pairTotal H x 0 256 ≤ 2048 := by
  rw [pair_total_filter]
  have nd : ((List.range' 0 256).filter (touchedAt H x)).Nodup := (List.nodup_range' (s:=0) (n:=256)).filter _
  have sub : ((List.range' 0 256).filter (touchedAt H x)).toFinset ⊆
      (Finset.range 128).image (fun r => bucket x r / 2) := by
    intro j hj
    rw [List.mem_toFinset] at hj
    obtain ⟨r, hr, e⟩ := touched_record H x j (List.mem_filter.mp hj).2
    exact Finset.mem_image.mpr ⟨r, Finset.mem_range.mpr hr, e⟩
  have card := (Finset.card_le_card sub).trans Finset.card_image_le
  rw [List.toFinset_card_of_nodup nd, Finset.card_range] at card
  omega
end CommitGolfCandidate.Chained.BinaryMachine.Check
