import CommitGolfCandidate.ReconstructedHidingTranscript
import CommitGolfCandidate.ReconstructedHidingAdaptiveWorlds

namespace CommitGolfCandidate.Reconstruction.HidingTraffic
open CommitGolf OracleComp TwoPermutationPrototype.Sampling
open CommitGolfCandidate.Permutation
open CommitGolfCandidate.Permutation.NonceChain (mean mean_equiv)
set_option maxRecDepth 12000
set_option exponentiation.threshold 2048
set_option maxHeartbeats 1800000

noncomputable def storedInputs (c : Cache) : Finset Block := (c.entries.map Prod.fst).toFinset
noncomputable def cacheTrace (c : Cache) : Trace Block :=
  (storedInputs c).toList.map (fun x => ⟨.fwd,x,c.example.val.forward x⟩)

theorem cache_pair (c : Cache) (x y : Block) : containsPair (cacheTrace c) x y ↔ (x,y) ∈ c.entries := by
  constructor
  · rintro ⟨e,member,input,output⟩
    obtain ⟨a,inKeys,rfl⟩ := List.mem_map.mp member
    change a=x at input
    subst x
    change c.example.val.forward a=y at output
    have keyMember : a ∈ c.entries.map Prod.fst := by simpa [storedInputs] using inKeys
    obtain ⟨row,old,rowInput⟩ := List.mem_map.mp keyMember
    have readBack :=  c.example.property row old
    obtain ⟨u,v⟩ := row
    change u=a at rowInput
    subst a
    have vy : v=y := readBack.symm.trans output
    simpa only [vy] using old
  · intro old
    have keyMember : x ∈ (storedInputs c).toList := by
      rw [Finset.mem_toList,storedInputs,List.mem_toFinset]
      exact List.mem_map.mpr ⟨(x,y),old,rfl⟩
    exact ⟨_,List.mem_map.mpr ⟨x,keyMember,rfl⟩,rfl,c.example.property (x,y) old⟩

theorem cache_well (c : Cache) : (cacheTrace c).WF := by
  constructor
  · simpa [cacheTrace,List.map_map,Function.comp_def] using (Finset.nodup_toList (storedInputs c))
  · simpa [cacheTrace,List.map_map,Function.comp_def] using
      (Finset.nodup_toList (storedInputs c)).map (Function.LeftInverse.injective c.example.val.leftInverse)

theorem cache_length (c : Cache) : (cacheTrace c).length ≤ c.entries.length := by
  simpa only [cacheTrace,storedInputs,List.length_map,Finset.length_toList] using
    (List.toFinset_card_le (c.entries.map Prod.fst)).trans_eq (List.length_map (f := Prod.fst))

theorem cache_extension (c : Cache) (π : Equiv.Perm Block) :
    π ∈ (cacheTrace c).ext ↔ Agrees c.entries (BiPermutation.equiv Block π) := by
  rw [Trace.mem_ext]
  constructor
  · intro all row old
    obtain ⟨x,y⟩ := row
    obtain ⟨e,seen,a,b⟩ := (cache_pair c x y).mpr old
    change π x=y
    rw [←a,←b]
    exact all e seen
  · intro all e seen
    exact all (e.inp,e.out) ((cache_pair c e.inp e.out).mp ⟨e,seen,rfl,rfl⟩)

attribute [local irreducible] storedInputs cacheTrace Trace.ext

noncomputable def completionEquiv (c : Cache) : Completion c.entries ≃ {π : Equiv.Perm Block // π ∈ (cacheTrace c).ext} where
  toFun p := ⟨(BiPermutation.equiv Block).symm p.val,(cache_extension c ((BiPermutation.equiv Block).symm p.val)).mpr (by
    rw [Equiv.apply_symm_apply]; exact p.property)⟩
  invFun p := ⟨BiPermutation.equiv Block p.val,(cache_extension c p.val).mp p.property⟩
  left_inv p := Subtype.ext (Equiv.apply_symm_apply _ _)
  right_inv p := Subtype.ext (Equiv.symm_apply_apply _ _)

theorem cache_has_completion (c : Cache) : (cacheTrace c).ext.Nonempty :=
  ⟨(completionEquiv c c.example).val,(completionEquiv c c.example).property⟩

noncomputable instance cacheCompletionFinite (c : Cache) : Fintype (Completion c.entries) := by
  classical exact Fintype.ofFinite _

theorem completion_mean (c : Cache) (f : Equiv.Perm Block → ℝ) :
    mean (fun v : Completion c.entries => f ((BiPermutation.equiv Block).symm v.val)) =
      avg (cacheTrace c).ext f := by
  have transport := mean_equiv (completionEquiv c) (fun p => f p.val)
  refine transport.trans ?_
  simp only [mean,avg,Finset.card_univ,Fintype.card_coe,Finset.sum_coe_sort]

end CommitGolfCandidate.Reconstruction.HidingTraffic
