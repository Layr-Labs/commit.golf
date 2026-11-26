import CommitGolfCandidate.ReconstructedBindingStep
import Mathlib.Data.Fintype.Card
import Mathlib.Data.FinEnum
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace CommitGolfCandidate.Reconstruction.Binding
open Finset
set_option maxRecDepth 8192
set_option maxHeartbeats 2500000
noncomputable section

attribute [local instance] Classical.propDecidable
instance : DecidableEq Seed := Classical.decEq _
instance : Fintype Seed := Classical.choice ⟨Fintype.ofEquiv
  { s : Fin 24 × Key // s.2.2.2 >>> 48 = tag (s.1.val+1) }
  ⟨fun s => ⟨s.val.1,s.val.2,s.property⟩, fun s => ⟨(s.depth,s.key),s.domain⟩,
   fun _ => rfl, fun _ => rfl⟩⟩

attribute [local irreducible] Finset.univ

def completed (m : Table) := Finset.univ.filter (fun s : Seed => (finish m s).isSome)
def atDepth (m : Table) (d : Fin 24) := (completed m).filter (fun s => s.depth = d)
def mass (m : Table) : Nat := ∑ s ∈ completed m, work s.depth

theorem mem_completed {m : Table} {s : Seed} :
    s ∈ completed m ↔ ∃ y, finish m s = some y := by
  simp [completed, Option.isSome_iff_exists]

theorem class_card (d : Nat) (t : Digest) :
    (Finset.univ.filter (fun y : Digest => project d y = t)).card ≤ fiberSize d := by
  classical
  have h := Finset.card_le_card_of_injOn
    (s := Finset.univ.filter (fun y : Digest => project d y = t)) (t := (Finset.univ : Finset (Fin (fiberSize d))))
    (rank d) (by simp) (by
      intro a ha b hb eq
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ha hb
      exact congrArg Subtype.val (rank_injective d t ⟨a,ha⟩ ⟨b,hb⟩ eq))
  simpa using h

def dangerous (m : Table) (d : Fin 24) : Finset Digest := by
  classical
  exact (atDepth m d).biUnion fun s =>
    Finset.univ.filter fun y : Digest => (finish m s).map (project d) = some (project d y)

theorem danger_card (m : Table) (d : Fin 24) :
    (dangerous m d).card ≤ (atDepth m d).card * fiberSize d := by
  classical
  unfold dangerous
  calc
    _ ≤ _ := Finset.card_biUnion_le
    _ ≤ ∑ _s ∈ atDepth m d, fiberSize d := by
      apply Finset.sum_le_sum
      intro s hs
      have hm : s ∈ completed m := ((Finset.mem_filter (s := completed m) (p := fun s : Seed => s.depth = d)).1 hs).1
      obtain ⟨v,hv⟩ := (mem_completed (m := m) (s := s)).1 hm
      simpa only [hv, Option.map_some, Option.some.injEq, eq_comm] using class_card d (project d v)
    _ = _ := by simp

def Covers (keys : Finset Key) (m : Table) := ∀ k v, m k = some v → k ∈ keys

theorem mass_bound (m : Table) (keys : Finset Key) (safe : DistinctAnswers m) (covers : Covers keys m) :
    mass m ≤ keys.card := by
  classical
  let populated := keys.filter (fun k => (m k).isSome)
  let rows : History := populated.toList.map (fun k => (k,extendTable m k))
  have read {k : Key} {y : Digest} (row : (k,y) ∈ rows) : m k = some y := by
    obtain ⟨k',mem,eq⟩ := List.mem_map.1 row
    cases eq
    obtain ⟨v,hv⟩ := Option.isSome_iff_exists.1 ((Finset.mem_filter.1 (Finset.mem_toList.1 mem)).2)
    simp [extendTable,hv]
  have noFull : ¬ FullCollision rows := by
    rintro ⟨a,b,v,ne,ha,hb⟩; exact ne (safe a b v (read ha) (read hb))
  have paid := total_paid_work (C := extendTable m) noFull (completed m).toList (Finset.nodup_toList _) (by
    intro s hs
    obtain ⟨v,hv⟩ := (mem_completed (m := m) (s := s)).1 (Finset.mem_toList.1 hs)
    intro j hj
    let k := lastKey (extendTable m) s.key j
    have real := trace_of_finish m s v hv j hj
    apply List.mem_map.2
    refine ⟨k,Finset.mem_toList.2 (Finset.mem_filter.2 ⟨covers k _ real,?_⟩),rfl⟩
    rw [show m k = some (extendTable m k) from real]; rfl)
  have card := Finset.card_le_card (Finset.filter_subset (fun k => (m k).isSome) keys)
  simpa [rows,mass,Finset.sum_toList] using (le_trans paid (by simpa [rows,populated] using card : rows.length ≤ keys.card))

theorem paid_mass_per_depth (m : Table) (d : Fin 24) :
    (atDepth m d).card * work d ≤ mass m := by
  classical
  have := Finset.sum_le_sum_of_subset_of_nonneg (f := fun s : Seed => work s.depth)
    (Finset.filter_subset (fun s : Seed => s.depth = d) (completed m))
    (fun _ _ _ => Nat.zero_le _)
  have factor : ∑ s ∈ atDepth m d, work s.depth = ∑ _s ∈ atDepth m d, work d := by
    apply Finset.sum_congr rfl
    intro s hs
    have hd : s.depth = d := ((Finset.mem_filter (s := completed m) (p := fun s : Seed => s.depth = d)).1 hs).2
    rw [hd]
  change (∑ s ∈ atDepth m d, work s.depth) ≤ mass m at this
  rw [factor] at this
  simpa using this

theorem complete_put_set (m : Table) (k : Key) (y : Digest)
    (fresh : m k = none)
    (newUnary : m (unary y) = none) (noSelf : unary y ≠ k) :
    completed (put m k y) = completed m ∪ Finset.univ.filter (Ready m k) := by
  classical
  ext t
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, mem_completed]
  constructor
  · rintro ⟨v,h⟩
    rcases finish_after_put m k y newUnary noSelf _ _ h with old | new
    · exact Or.inl ⟨v,old⟩
    · exact Or.inr new.1
  · rintro (⟨v,old⟩ | ready)
    · exact ⟨v,finish_mono _ _ (table_ext_put _ _ _ fresh) _ _ old⟩
    · change probe m t.key _ = some k at ready
      refine ⟨y,Option.bind_eq_some_iff.2 ⟨k,probe_mono _ _ (table_ext_put _ _ _ fresh) _ _ _ ready,?_⟩⟩
      simp [put]


end
end CommitGolfCandidate.Reconstruction.Binding
