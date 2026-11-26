import CommitGolfCandidate.ReconstructedBindingOracle
import CommitGolfCandidate.ReconstructedBindingCredit
import CommitGolfCandidate.ReconstructedBindingSurvival

namespace CommitGolfCandidate.Reconstruction.Binding
open CommitGolf OracleComp OracleSpec CommitGolfCandidate.JointOracle241
set_option maxRecDepth 8192
set_option maxHeartbeats 900000

structure StepBound (q : PublicSpec.Domain) (s : State) where
  w : Nat
  bound : w ≤ 9
  reject : PublicSpec.Range q × State → Prop
  rate : Pr{let r ← handler (.inr q) s}[reject r] ≤ ENNReal.ofReal (hazard (used s) s.count w)
  live : ∀ r ∈ support (handler (.inr q) s), ¬ reject r → Good r.2 ∧ used r.2 = used s+w

private theorem cast_hazard (s : State) (k : BitVec 512) (good : Good s) :
    let test := Reject (table s) (decodeKey k)
    Pr{let y ← $ᵗ BitVec 256}[test (unpack y)] ≤
      ENNReal.ofReal (hazard (used s) s.count (weight (table s) (decodeKey k))) := by
  classical
  dsimp only
  let test := Reject (table s) (decodeKey k)
  have card : (Finset.univ.filter (fun y : BitVec 256 => test (unpack y))).card ≤
      (Finset.univ.filter test).card :=
    Finset.card_le_card_of_injOn unpack
      (by intro y h; simpa only [Finset.coe_filter,Finset.mem_univ,true_and,Set.mem_ofPred_eq] using h)
      (by intro a _ b _ h; simpa using congrArg pack h)
  have c := fresh_answer_count _ _ (decodeKey k) good.1 (table_covered s) good.2.1
  have ck : (keys s).card ≤ s.count := by have := keys_le s; have := s.size; omega
  let w := weight (table s) (decodeKey k)
  have raw : (Finset.univ.filter (fun y : BitVec 256 => test (unpack y))).card ≤
      320147 * (used s+2)*w + 2*s.count+1 := by
    change 1000000 * (Finset.univ.filter test).card ≤ _ at c
    change _ ≤ 1000000 * (2*(keys s).card+1) + 1221263 * 2^18 * mass (table s)*w at c
    have rank : mass (table s) ≤ used s+2 := by unfold used; omega
    have m := Nat.mul_le_mul_right w rank
    nlinarith only [card,c,ck,m,Nat.zero_le ((used s+2)*w)]
  rw [SampleableType.prEvent_uniformSample]
  change ((Finset.univ.filter (fun y : BitVec 256 => test (unpack y))).card : ENNReal) /
      Fintype.card (BitVec 256) ≤ _
  rw [← FinEnum.card_eq_fintypeCard,FinEnum.card_bitVec]
  have sr := ENNReal.ofReal_le_ofReal (show
      ((Finset.univ.filter (fun y : BitVec 256 => test (unpack y))).card : ℝ) / 2^256 ≤
      hazard (used s) s.count w from by unfold hazard; gcongr; exact_mod_cast raw)
  simpa only [ENNReal.ofReal_div_of_pos (by positivity : (0:ℝ) < 2^256), ENNReal.ofReal_natCast,
    show ENNReal.ofReal ((2:ℝ)^256) = (2:ENNReal)^256 by norm_num,
    Nat.cast_pow,Nat.cast_ofNat] using sr

noncomputable def compression_step (k : BitVec 512) (s : State) (good : Good s) :
    StepBound (.inl k) s := by
  classical
  cases h : s.cache k with
  | some y =>
    refine ⟨0,by decide,fun _ => False,?_,?_⟩
    · simp
    · intro r hr _
      change r ∈ support (match s.cache k with
        | some a => pure (a,s.bump)
        | none => do let a ← $ᵗ CompressionSpec.Range k; pure (a,s.store k a)) at hr
      rw [h] at hr
      simp only [support_pure,Set.mem_singleton_iff] at hr
      subst r; exact ⟨good,rfl⟩
  | none =>
    refine ⟨weight (table s) (decodeKey k), weight_le _ _, fun r => Reject (table s) (decodeKey k) (unpack r.1),?_,?_⟩
    · change prEvent ((fun r => Reject (table s) (decodeKey k) (unpack r.1)) <$>
        (match s.cache k with
        | some a => pure (a,s.bump)
        | none => do let a ← $ᵗ CompressionSpec.Range k; pure (a,s.store k a))) ≤ _
      split
      · rename_i _ e; simp [h] at e
      · rw [bind_pure_comp,Functor.map_map]
        exact cast_hazard s k good
    · intro r hr ok
      change r ∈ support (match s.cache k with
        | some a => pure (a,s.bump)
        | none => do let a ← $ᵗ CompressionSpec.Range k; pure (a,s.store k a)) at hr
      rw [h] at hr
      obtain ⟨a,_,hr⟩ := (mem_support_bind_iff _ _ _).mp hr
      simp only [support_pure,Set.mem_singleton_iff] at hr
      subst r
      exact store_good s k a good h ok

end CommitGolfCandidate.Reconstruction.Binding
