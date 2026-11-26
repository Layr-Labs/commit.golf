import CommitGolfCandidate.ReconstructedHidingRowProb

namespace CommitGolfCandidate.Reconstruction.HidingTape
open CommitGolf OracleComp TwoPermutationPrototype.Sampling
set_option linter.constructorNameAsVariable false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option exponentiation.threshold 2048
noncomputable local instance supportSaltSampler {I : Type} [Fintype I] : SampleableType (I → Salt) :=
  by classical exact SampleableType.ofFintype _

attribute [local irreducible] pinnedPrivateSecond pinnedCachedUpper runPinnedHigh pinnedNonceAddresses
  PinnedHighCache.zero pinnedConstantPlans tagHit reverseUpper

section Rows
variable {I : Type} [Fintype I] {base : Cache} {count : Nat} (state : PinnedOpenedState base count)
    (pos : I → Position) (first : Bool → I → Reply) (msg : Bool → I → TwoPermutationPrototype.Words 32)
    (digest : I → BitVec 256)

theorem row_support (w : Bool) (s : I → Salt) (rows : List Row)
    (occurs : rows ∈ support (pinnedRowsNonce state pos (first w) (msg w) digest (fun i => (s i).setWidth 128))) :
    rows.length ≤ Fintype.card I ∧ ∀ e ∈ rows, tagHit pos e.1 s := by
  classical
  simp only [pinnedRowsNonce] at occurs
  split at occurs
  · obtain ⟨v,_,comes⟩ := (mem_support_bind_iff _ _ _).mp occurs
    simp only [support_pure,Set.mem_singleton_iff] at comes
    subst rows
    refine ⟨by simp,?_⟩
    intro e included
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp included
    exact pinned_tag_hit pos i (first w i) (msg w i) s
  · simp only [support_pure,Set.mem_singleton_iff] at occurs
    subst rows
    simp

attribute [local irreducible] pinnedRowsNonce

theorem paired_support (s : I → Salt) (rows : List Row × List Row)
    (occurs : rows ∈ support (pairedRows state pos first msg digest s)) :
    (rows.1++rows.2).length ≤ 2*Fintype.card I ∧ ∀ e ∈ rows.1++rows.2, tagHit pos e.1 s := by
  simp only [pairedRows] at occurs
  obtain ⟨l,lSeen,other⟩ := (mem_support_bind_iff _ _ _).mp occurs
  obtain ⟨r,rSeen,pair⟩ := (mem_support_bind_iff _ _ _).mp other
  simp only [support_pure,Set.mem_singleton_iff] at pair
  subst rows
  obtain ⟨lenL,left⟩ := row_support state pos first msg digest false s l lSeen
  obtain ⟨lenR,right⟩ := row_support state pos first msg digest true s r rSeen
  refine ⟨by change (l++r).length ≤ _; rw [List.length_append]; omega,?_⟩
  intro e included
  exact (List.mem_append.mp included).elim (left e) (right e)

attribute [local irreducible] pairedRows

theorem sampled_row_count (rows : List Row × List Row) (occurs : rows ∈ support (pairedSample state pos first msg digest)) :
    (rows.1++rows.2).length ≤ 2*Fintype.card I := by
  unfold pairedSample at occurs
  obtain ⟨s,_,found⟩ := (mem_support_bind_iff _ _ _).mp occurs
  exact (paired_support state pos first msg digest s rows found).1

theorem sampled_input_pay [DecidableEq I] (unique : Function.Injective pos) (x : Reply) :
    Pr{let rows ← pairedSample state pos first msg digest}[∃ e ∈ rows.1++rows.2, x=e.1] ≤ 1/2^120 := by
  classical
  have zero (s : I → Salt) (_ : s ∈ support ($ᵗ (I → Salt))) (off : ¬tagHit pos x s) :
      Pr{let rows ← pairedRows state pos first msg digest s}[∃ e ∈ rows.1++rows.2, x=e.1] ≤ 0 := by
    rw [prEvent_eq_zero_of_forall_mem_support (pairedRows state pos first msg digest s) (fun rows => ∃ e ∈ rows.1++rows.2, x=e.1) (fun rs found flag => by
      obtain ⟨e,seen,rfl⟩ := flag
      exact off ((paired_support state pos first msg digest s rs found).2 e seen))]
  have pay := prEvent_bind_le_prEvent_add_of_support ($ᵗ (I → Salt)) (pairedRows state pos first msg digest)
    (tagHit pos x) (fun rows => ∃ e ∈ rows.1++rows.2, x=e.1) zero
  rw [add_zero] at pay
  exact pay.trans (tag_hit_le pos unique x)

end Rows

private theorem zero_tag_impossible {I : Type} (pos : I → Position) (s : I → Salt) : ¬tagHit pos 0 s := by
  unfold tagHit
  rintro ⟨i,tagged,_⟩
  have e := congrArg BitVec.toNat tagged
  change 0 = (4152+256*(pos i).val)%2^64 at e
  have cap := (pos i).isLt
  rw [Nat.mod_eq_of_lt (by omega)] at e
  omega

theorem sampled_output_pay {I : Type} [Fintype I] [DecidableEq I] {base : Cache} {count : Nat}
    (state : PinnedOpenedState base count) (valid : state.high.Valid count)
    (pos : I → Position) (unique : Function.Injective pos) (first : Bool → I → Reply)
    (msg : Bool → I → TwoPermutationPrototype.Words 32) (digest : I → BitVec 256)
    (enough : state.high.zero.entries.length + Fintype.card I ≤ 2^121) (y : Reply) :
    Pr{let rows ← pairedSample state pos first msg digest}[∃ e ∈ rows.1++rows.2, y=e.2] ≤
      1/2^120+2*(Fintype.card I : ENNReal)/2^1343 := by
  classical
  refine (prEvent_mono _ _ (fun rows => rowHits (rows.1++rows.2) (0,y) = true) ?_).trans ?_
  · rintro rows ⟨e,seen,hit⟩
    exact List.any_eq_true.mpr ⟨e,seen,decide_eq_true (Or.inr hit)⟩
  refine (paired_charge state pos first msg digest valid enough 0 y).trans (add_le_add ?_ le_rfl)
  cases h : reverseUpper state.high (outputTail y) with
  | none =>
    rw [(SampleableType.prEvent_uniformSample_eq_zero_iff _).2 (by
      rintro s (bad|⟨_,bad,_⟩)
      · exact zero_tag_impossible pos s bad
      · cases bad)]
    exact zero_le
  | some a =>
    refine (prEvent_mono _ _ (tagHit pos a) ?_).trans (tag_hit_le pos unique a)
    rintro s (bad|⟨b,matchRow,present⟩)
    · exact (zero_tag_impossible pos s bad).elim
    · exact (Option.some.inj matchRow) ▸ present

end CommitGolfCandidate.Reconstruction.HidingTape
