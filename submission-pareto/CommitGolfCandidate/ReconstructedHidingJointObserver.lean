import CommitGolfCandidate.ReconstructedHidingMarkedCache
import CommitGolfCandidate.ReconstructedHidingJointPay
import CommitGolfCandidate.ReconstructedHidingRetainedGame

namespace CommitGolfCandidate.Reconstruction.HidingTape
open CommitGolf OracleComp Generator TwoPermutationPrototype.Sampling HidingTraffic
set_option maxRecDepth 12000
set_option maxHeartbeats 2100000
set_option exponentiation.threshold 2048
set_option linter.constructorNameAsVariable false
attribute [local instance] jointFnSampler
attribute [local irreducible] pairedRows pinnedRowsNonce packedAddress blockSplit
local instance observerDiscrete {α : Type} : MeasurableSpace α := ⊤

abbrev RowSeed (I : Type) := Secrets I × Paired

noncomputable def proposedReplies {I : Type} (blocks : (I → Salt) → Group → SaltBlock) (s : Secrets I) : GenReplies :=
  fun j => blockSplit.symm (blocks s.1.2 (groupIndex j),s.2 (groupIndex j))

noncomputable def joinedRows {I : Type} (blocks : (I → Salt) → Group → SaltBlock)
    (gate : Secrets I → Prop) (seed : RowSeed I) : Paired := by
  classical exact if gate seed.1 then addRows seed.2 (genRows blocks seed.1) else ([],[])

section Sample
variable {I : Type} [Fintype I] {base : Cache} {count : Nat} (state : PinnedOpenedState base count)
    (pos : I → Position) (first : Bool → I → Reply) (msg : Bool → I → TwoPermutationPrototype.Words 32)
    (digest : I → BitVec 256) (blocks : (I → Salt) → Group → SaltBlock) (gate : Secrets I → Prop)

noncomputable def drawRowSeed : ProbComp (RowSeed I) := do
  let s ← $ᵗ (Secrets I)
  let r ← pairedRows state pos first msg digest s.1.2
  pure (s,r)

theorem joined_distribution :
    (joinedRows blocks gate <$> drawRowSeed state pos first msg digest) =ᵈ
      jointSample state pos first msg digest blocks gate := by
  classical
  unfold drawRowSeed jointSample
  simp only [map_eq_bind_pure_comp,bind_assoc,Function.comp_def,pure_bind]
  apply EvalDistEq.bind_right
  intro s
  unfold jointRows
  by_cases ok : gate s
  · simp only [ite_eq_left ok,map_eq_bind_pure_comp,Function.comp_def,joinedRows]
    exact EvalDistEq.refl _
  · simp only [ite_eq_right ok,joinedRows]
    exact EvalDistEq.of_evalDist_eq (evalDist_bind_const _ _)

theorem seed_first_distribution :
    (Prod.fst <$> drawRowSeed state pos first msg digest) =ᵈ ($ᵗ (Secrets I)) := by
  unfold drawRowSeed
  simp only [map_eq_bind_pure_comp,bind_assoc,Function.comp_def,pure_bind]
  trans (($ᵗ (Secrets I)) >>= pure)
  · apply EvalDistEq.bind_right
    intro s
    exact EvalDistEq.of_evalDist_eq (evalDist_bind_const _ _)
  · rw [bind_pure]

end Sample

noncomputable def applyLeafRows {I : Type} (w : Bool) (s : RowSeed I) (π : Perm) : Perm :=
  (BiPermutation.equiv Block).symm ((BiPermutation.equiv Block π).programRows (sideRows w s.2))

private theorem clean_joints {I : Type} (blocks : (I → Salt) → Group → SaltBlock) (gate : Secrets I → Prop)
    (s : RowSeed I) (admitted : gate s.1) (w : Bool) (π : Perm) (x : Reply)
    (clean : permitSets (fun z => rowInputs (joinedRows blocks gate z))
      (fun z => rowOutputs (joinedRows blocks gate z)) s x (π x)=true) :
    applyLeafRows w s π x=π x ∧ genPermit s.1.1.1 (proposedReplies blocks s.1) x (π x)=true := by
  classical
  have clear := of_decide_eq_true clean
  change ¬(x ∈ rowInputs (joinedRows blocks gate s) ∨ π x ∈ rowOutputs (joinedRows blocks gate s)) at clear
  rw [joinedRows,ite_eq_left admitted] at clear
  have guard (e : Row) (seen : e ∈ s.2.1++s.2.2 ∨ e∈genRows blocks s.1) : x≠e.1 ∧ π x≠e.2 := by
    have found := (extra_member s.2 _ e).mpr seen
    exact ⟨fun hit => clear (Or.inl ((left_member _ _).mpr ⟨e,found,hit⟩)),
      fun hit => clear (Or.inr ((right_member _ _).mpr ⟨e,found,hit⟩))⟩
  constructor
  · apply BiPermutation.program_rows_forward_unchanged
    intro e seen
    have included : e ∈ s.2.1++s.2.2 := by cases w <;> simp_all [sideRows]
    exact guard e (Or.inl included)
  · apply (gen_permit_iff _ _ _ _).mpr
    have per (j : Fin groupCount) :
        x ≠ packedAddress s.1.1.1 j ∧ π x ≠ proposedReplies blocks s.1 j :=
      guard _ (Or.inr (List.mem_ofFn.mpr ⟨j,rfl⟩))
    have permitted : (∀ j, packedAddress s.1.1.1 j ≠ x) ∧ (∀ j, proposedReplies blocks s.1 j ≠ π x) :=
      ⟨fun j => (per j).1.symm,fun j => (per j).2.symm⟩
    exact permitted

open Classical in
noncomputable def jointlyMarked {S A : Type} (c : Compression) (table : Cache) (seed : ProbComp S)
    (rows : S → Paired) (good : S → Prop) (g : OracleComp World A) :=
  markedCache c table seed (fun _ p => p)
    (permitSets (fun s => rowInputs (rows s)) (fun s => rowOutputs (rows s))) (fun s => decide (good s)) g

theorem joint_observer_lower {I A : Type} (c : Compression) (table : Cache) (seed : ProbComp (RowSeed I))
    (blocks : (I → Salt) → Group → SaltBlock) (gate : Secrets I → Prop)
    (g : OracleComp World A) (ev : A → Prop) (w : Bool) (actualFlag : RowSeed I → Bool)
    (pass : ∀ s ∈ support seed, gate s.1 → actualFlag s=true) :
    (Pr{let v ← jointlyMarked c table seed (joinedRows blocks gate) (fun v => gate v.1) g}[ev v.1 ∧ v.2=true]).toReal ≤
      (Pr{let v ← (markedCache c table seed (applyLeafRows w) (fun s => genPermit s.1.1.1 (proposedReplies blocks s.1)) actualFlag g)}[ev v.1 ∧ v.2=true]).toReal := by
  classical
  apply marked_cache_lower
  · intro s seen h; exact pass s seen (of_decide_eq_true h)
  intro s _ passed p _ x
  exact clean_joints blocks gate s (of_decide_eq_true passed) w p x

end CommitGolfCandidate.Reconstruction.HidingTape
