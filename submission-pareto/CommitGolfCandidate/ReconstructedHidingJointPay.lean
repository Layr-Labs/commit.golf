import CommitGolfCandidate.ReconstructedHidingJointRows

namespace CommitGolfCandidate.Reconstruction.HidingTape
open CommitGolf OracleComp Generator TwoPermutationPrototype.Sampling HidingTraffic
set_option maxRecDepth 12000
set_option maxHeartbeats 2200000
set_option exponentiation.threshold 2048
set_option linter.constructorNameAsVariable false
attribute [local instance] jointFnSampler
attribute [local irreducible] pairedRows pinnedRowsNonce genRows tagHit reverseUpper

theorem tag_zero_absent {I : Type} (pos : I → Position) (s : I → Salt) : ¬tagHit pos 0 s := by
  unfold tagHit
  rintro ⟨i,m,_⟩
  have e := congrArg BitVec.toNat m
  change 0 = (4152+256*(pos i).val)%2^64 at e
  have h := (pos i).isLt
  rw [Nat.mod_eq_of_lt (by omega)] at e
  omega

section Rows
variable {I : Type} [Fintype I] [DecidableEq I] {base : Cache} {count : Nat} (state : PinnedOpenedState base count)
    (valid : state.high.Valid count) (pos : I → Position) (unique : Function.Injective pos)
    (first : Bool → I → Reply) (msg : Bool → I → TwoPermutationPrototype.Words 32)
    (digest : I → BitVec 256) (enough : state.high.zero.entries.length + Fintype.card I ≤ 2^121)
    (blocks : (I → Salt) → Group → SaltBlock) (gate : Secrets I → Prop)

include valid unique enough

theorem joint_rare (query : QueryEnd) (x y : Reply) (ev : Paired → Prop) (empty : ¬ev ([],[]))
    (rare : ∀ s, ¬chosenHit pos blocks (reverseUpper state.high) query s →
      ¬(tagHit pos x s.1.2 ∨ ∃ a, reverseUpper state.high (outputTail y) = some a ∧ tagHit pos a s.1.2))
    (shrink : ∀ s, gate s → ¬chosenHit pos blocks (reverseUpper state.high) query s →
      ∀ r, ev (addRows r (genRows blocks s)) → rowHits (r.1++r.2) (x,y) = true) :
    Pr{let rows ← jointSample state pos first msg digest blocks gate}[ev rows] ≤
      1/2^120+2*(Fintype.card I:ENNReal)/2^1343 := by
  classical
  let bad := chosenHit pos blocks (reverseUpper state.high) query
  have single (s : Secrets I) (_ : s ∈ support ($ᵗ (Secrets I))) (clean : ¬bad s) :
      Pr{let rows ← jointRows state pos first msg digest blocks gate s}[ev rows] ≤
        2*(Fintype.card I:ENNReal)/2^1343 := by
    unfold jointRows
    split
    · rename_i validGate
      rw [prEvent_map]
      exact (prEvent_mono _ _ (fun r => rowHits (r.1++r.2) (x,y)=true) (shrink s validGate clean)).trans
        (paired_safe_charge state pos first msg digest valid enough s.1.2 x y (rare s clean))
    · rw [prEvent_pure,ite_eq_right empty]
      exact zero_le
  exact (prEvent_bind_le_prEvent_add_of_support ($ᵗ (Secrets I))
    (jointRows state pos first msg digest blocks gate) bad ev single).trans
    (add_le_add (chosen_endpoint_le pos unique blocks (reverseUpper state.high) query) le_rfl)

theorem joint_output (y : Reply)
    (gives : ∀ s, gate s → Function.Injective (blocks s.1.2) ∧
       ∀ g hi, (reverseUpper state.high hi).isSome → signature (blocks s.1.2 g) ≠ tailSignature hi) :
    Pr{let rows ← jointSample state pos first msg digest blocks gate}[y∈rowOutputs rows] ≤
      1/2^120+2*(Fintype.card I:ENNReal)/2^1343 := by
  apply joint_rare state valid pos unique first msg digest enough blocks gate (.inverse y) 0 y _
    (by simp [rowOutputs]; exact Finset.notMem_empty _)
  · rintro s safe (bad|bad)
    · exact tag_zero_absent pos s.1.2 bad
    · exact safe (Or.inl bad)
  · intro s gateOK safe r seen
    obtain ⟨e,found,hit⟩ := (right_member _ y).mp seen
    rcases (extra_member r _ e).mp found with leaf|other
    · exact List.any_eq_true.mpr ⟨e,leaf,decide_eq_true (Or.inr hit)⟩
    · exact (safe (Or.inr ⟨(gives s gateOK).1,(gives s gateOK).2, hit ▸ gen_output blocks s e other⟩)).elim

theorem joint_cached (low : PinnedLowTape) (x y : Reply) (stored : (x,y) ∈ (state.high.realize low).entries)
    (excluded : ∀ s, gate s → ∀ g, blockSplit.symm (blocks s.1.2 g,s.2 g) ≠ y) :
    Pr{let rows ← jointSample state pos first msg digest blocks gate}[x ∈ rowInputs rows ∨ y∈rowOutputs rows] ≤
      1/2^120+2*(Fintype.card I:ENNReal)/2^1343 := by
  apply joint_rare state valid pos unique first msg digest enough blocks gate (.forward x) x y _
    (by simp [rowInputs,rowOutputs]; exact ⟨Finset.notMem_empty _,Finset.notMem_empty _⟩)
  · rintro s safe (hx|⟨a,h,ha⟩)
    · exact safe (Or.inr hx)
    · rcases cache_tail_matches state.high valid low x y stored with none|known
      · rw [none] at h; cases h
      · exact safe (Or.inr (Option.some.inj (h.symm.trans known) ▸ ha))
  · intro s allowed safe r seen
    rcases seen with hit|hit
    · obtain ⟨e,found,equal⟩ := (left_member _ x).mp hit
      rcases (extra_member r _ e).mp found with leaf|other
      · exact List.any_eq_true.mpr ⟨e,leaf,decide_eq_true (Or.inl equal)⟩
      · exact (safe (Or.inl (equal ▸ gen_input blocks s e other))).elim
    · obtain ⟨e,found,equal⟩ := (right_member _ y).mp hit
      rcases (extra_member r _ e).mp found with leaf|other
      · exact List.any_eq_true.mpr ⟨e,leaf,decide_eq_true (Or.inr equal)⟩
      · obtain ⟨g,eq⟩ := gen_output blocks s e other
        exact (excluded s allowed g (eq.trans equal.symm)).elim

end Rows

end CommitGolfCandidate.Reconstruction.HidingTape
