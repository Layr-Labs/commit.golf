import CommitGolfCandidate.ReconstructedHidingRowSupport
import CommitGolfCandidate.ReconstructedHidingProgram

namespace CommitGolfCandidate.Reconstruction.HidingTape
open CommitGolf OracleComp TwoPermutationPrototype.Sampling HidingTraffic
set_option maxRecDepth 12000
set_option maxHeartbeats 1800000
set_option exponentiation.threshold 2048
set_option linter.constructorNameAsVariable false
local instance protectedDiscrete {α : Type} : MeasurableSpace α := ⊤
noncomputable local instance protectionSampler {I : Type} [Fintype I] : SampleableType (I → Salt) :=
  by classical exact SampleableType.ofFintype _

def prefixHit {I : Type} (base : Cache) (pos : I → Position) (s : I → Salt) : Prop :=
  ∃ row ∈ base.entries, tagHit pos row.1 s

theorem prefix_probability {I : Type} [Fintype I] [DecidableEq I] (base : Cache)
    (pos : I → Position) (unique : Function.Injective pos) :
    (Pr{let s ← $ᵗ (I → Salt)}[prefixHit base pos s]).toReal ≤ (base.entries.length : ℝ)/2^120 := by
  change (Pr{let s ← $ᵗ (I → Salt)}[∃ row ∈ base.entries, tagHit pos row.1 s]).toReal ≤ _
  have hit := prEvent_list_le base.entries ($ᵗ (I → Salt)) (fun row s => tagHit pos row.1 s) (1/2^120)
    (fun row _ => tag_hit_le pos unique row.1)
  have bound := ENNReal.toReal_mono (by finiteness) hit
  simpa only [prefixHit,ENNReal.toReal_mul,ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_pow,
    ENNReal.toReal_ofNat,ENNReal.toReal_natCast,mul_one_div] using bound

theorem prefix_fresh {I : Type} [Fintype I] (base : Cache) (pos : I → Position) (first : I → Reply)
    (msg : I → TwoPermutationPrototype.Words 32) (s : I → Salt) (clean : ¬prefixHit base pos s) :
    ∀ addr ∈ pinnedNonceAddresses pos first msg (fun i => (s i).setWidth 128), UnusedInput base.entries addr := by
  intro addr seen row prior same
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp seen
  exact clean ⟨row,prior,same ▸ pinned_tag_hit pos i (first i) (msg i) s⟩

section Conditional
variable {I : Type} [Fintype I] {base : Cache} {count : Nat} (state : PinnedOpenedState base count)
    (pos : I → Position) (first : Bool → I → Reply) (msg : Bool → I → TwoPermutationPrototype.Words 32)
    (digest : I → BitVec 256)

noncomputable def guardedRows (s : I → Salt) : ProbComp Paired := by
  classical exact if prefixHit base pos s then pure ([],[]) else pairedRows state pos first msg digest s

noncomputable def guardedSample := ($ᵗ (I → Salt)) >>= guardedRows state pos first msg digest

attribute [local irreducible] pairedRows pinnedRowsNonce

theorem guarded_mono (e : Paired → Prop) (empty : ¬e ([],[])) :
    Pr{let r ← guardedSample state pos first msg digest}[e r] ≤
      Pr{let r ← pairedSample state pos first msg digest}[e r] := by
  classical
  unfold guardedSample pairedSample
  rw [prEvent_bind_eq_tsum,prEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro s
  apply mul_le_mul_of_nonneg_left _ zero_le
  unfold guardedRows
  split
  · rw [prEvent_pure,ite_eq_right empty]
    exact zero_le
  · exact le_rfl

theorem guarded_count (r : Paired) (found : r ∈ support (guardedSample state pos first msg digest)) :
    (r.1++r.2).length ≤ 2*Fintype.card I := by
  classical
  unfold guardedSample at found
  obtain ⟨s,_,seen⟩ := (mem_support_bind_iff _ _ _).mp found
  unfold guardedRows at seen
  split at seen
  · simp only [support_pure,Set.mem_singleton_iff] at seen
    subst r
    exact Nat.zero_le _
  · exact (paired_support state pos first msg digest s r seen).1

end Conditional

theorem left_member (r : Paired) (x : Reply) : x ∈ rowInputs r ↔ ∃ e ∈ r.1++r.2, x=e.1 := by
  constructor
  · intro old
    obtain ⟨e,seen,h⟩ := List.mem_map.mp (List.mem_toFinset.mp old)
    exact ⟨e,seen,h.symm⟩
  · rintro ⟨e,seen,h⟩
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨e,seen,h.symm⟩)

theorem right_member (r : Paired) (y : Reply) : y ∈ rowOutputs r ↔ ∃ e ∈ r.1++r.2, y=e.2 := by
  constructor
  · intro old
    obtain ⟨e,seen,h⟩ := List.mem_map.mp (List.mem_toFinset.mp old)
    exact ⟨e,seen,h.symm⟩
  · rintro ⟨e,seen,h⟩
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨e,seen,h.symm⟩)

theorem pair_member (r : Paired) (x y : Reply) : (x ∈ rowInputs r ∨ y ∈ rowOutputs r) ↔
    rowHits (r.1++r.2) (x,y)=true := by
  rw [left_member,right_member,rowHits,List.any_eq_true]
  constructor
  · rintro (⟨e,h,m⟩|⟨e,h,m⟩)
    · exact ⟨e,h,decide_eq_true (Or.inl m)⟩
    · exact ⟨e,h,decide_eq_true (Or.inr m)⟩
  · rintro ⟨e,h,b⟩
    exact (of_decide_eq_true b).elim (fun m => Or.inl ⟨e,h,m⟩) (fun m => Or.inr ⟨e,h,m⟩)

noncomputable def rowRate (n : Nat) : ℝ := 1/2^120+2*(n:ℝ)/2^1343

theorem row_rate_real (n : Nat) :
    (1/2^120+2*(n:ENNReal)/2^1343).toReal = rowRate n := by
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [rowRate,ENNReal.toReal_mul,ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_pow,
    ENNReal.toReal_ofNat,ENNReal.toReal_natCast]

theorem guarded_distance {I A : Type} [Fintype I] [DecidableEq I] {base : Cache} {count : Nat}
    (state : PinnedOpenedState base count) (valid : state.high.Valid count)
    (pos : I → Position) (unique : Function.Injective pos) (first : Bool → I → Reply)
    (msg : Bool → I → TwoPermutationPrototype.Words 32) (digest : I → BitVec 256)
    (enough : state.high.zero.entries.length + Fintype.card I ≤ 2^121)
    (low : PinnedLowTape) (c : Compression) (g : OracleComp World A) (q : Nat) (limited : QueryBounded g q)
    (small : q ≤ 2^120) :
    let p := guardedSample state pos first msg digest
    let run := changedRun c (state.high.realize low) p g
    measureTVDist (run false) (run true) ≤
      (q:ℝ)*(rowRate (Fintype.card I)+(2*Fintype.card I:ℝ)/((2:ℝ)^1600-2^122)) := by
  classical
  have card : Fintype.card Block = 2^1600 := by
    rw [← FinEnum.card_eq_fintypeCard,FinEnum.card_bitVec]
    rfl
  let n := Fintype.card I
  let p := guardedSample state pos first msg digest
  have payment (e : Paired → Prop) (none : ¬e ([],[]))
      (max : Pr{let r ← pairedSample state pos first msg digest}[e r] ≤ 1/2^120 + 2*(n:ENNReal)/2^1343) :
      (Pr{let r ← p}[e r]).toReal ≤ rowRate n := by
    rw [←row_rate_real]
    exact ENNReal.toReal_mono (by finiteness)
      ((guarded_mono state pos first msg digest e none).trans max)
  have fits : (state.high.realize low).entries.length + q ≤ 2^122 := by
    change (state.high.realize (fun _ => 0)).entries.length + _ ≤ _ at enough
    rw [PinnedHighCache.entries_length] at enough ⊢
    omega
  have result := changed_distance c (state.high.realize low) p g q limited (2*n) (2^122) (rowRate n)
    (by unfold rowRate; positivity) (by rw [card]; decide) fits
    (guarded_count state pos first msg digest)
    (fun x => payment _ (by simp [rowInputs]) (by
      exact (prEvent_mono _ _ (fun r => ∃ e ∈ r.1++r.2, x=e.1) (fun r => (left_member r x).mp)).trans
        ((sampled_input_pay state pos first msg digest unique x).trans le_self_add)))
    (fun y => payment _ (by simp [rowOutputs]) (by
      exact (prEvent_mono _ _ (fun r => ∃ e ∈ r.1++r.2, y=e.2) (fun r => (right_member r y).mp)).trans
        (sampled_output_pay state valid pos unique first msg digest enough y)))
    (fun x y known => payment _ (by simp [rowInputs,rowOutputs]) (by
      exact (prEvent_mono _ _ (fun r => rowHits (r.1++r.2) (x,y)=true) (fun r => (pair_member r x y).mp)).trans
        (cached_pair_charge state valid pos unique first msg digest enough low x y known)))
  simpa only [card,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_mul,n,p] using result

end CommitGolfCandidate.Reconstruction.HidingTape
