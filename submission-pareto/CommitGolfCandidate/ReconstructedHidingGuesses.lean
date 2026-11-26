import CommitGolfCandidate.ReconstructedHidingDistribution
import VCVio.OracleComp.QueryTracking.RandomOracle.EagerTable

namespace CommitGolfCandidate.Reconstruction.HidingTape
open CommitGolf OracleComp Generator

set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

noncomputable local instance guessSampler {ι α : Type} [Fintype ι] [Fintype α] [Nonempty α] :
    SampleableType (ι → α) := by classical exact SampleableType.ofFintype _
local instance discreteSpace {α : Type} : MeasurableSpace α := ⊤

def tag (i : Position) := BitVec.ofNat 64 (4152+256*i.val)

private theorem tag_value (i : Position) : (tag i).toNat = 4152+256*i.val := by
  have := i.isLt
  rw [tag,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]

theorem tag_inj : Function.Injective tag := by
  intro a b h
  have e := congrArg BitVec.toNat h
  rw [tag_value, tag_value] at e
  exact Fin.ext (by omega)

def keyHit (a : Reply) (k : Key) : Prop :=
  ∃ t g, ∀ j < 25, inputWord t g k j = a.extractLsb' (64*j) 64

def tagHit {I : Type} (position : I → Position) (a : Reply) (salt : I → Salt) : Prop :=
  ∃ i, a.extractLsb' 0 64 = tag (position i) ∧ a.extractLsb' 64 120 = salt i

/-- The second input contains the final 704 entry bits and final 704 first-reply
bits, then eight zero bits and the selected 120-bit salt and 64-bit tag. -/
def leafAddress (i : Position) (value : BitVec 2048) (firstReply : Reply) (s : Salt) : Reply :=
  (value.extractLsb' 1344 704 ++ firstReply.extractLsb' 896 704 ++ 0#8) ++ (s ++ tag i)

theorem leaf_address_hit {I : Type} (position : I → Position) (i : I) (value : BitVec 2048)
    (reply : Reply) (salt : I → Salt) :
    tagHit position (leafAddress (position i) value reply (salt i)) salt := by
  refine ⟨i,?_,?_⟩
  · unfold leafAddress
    rw [BitVec.extractLsb'_append_eq_of_add_le (by decide), BitVec.extractLsb'_append_eq_right]
  · unfold leafAddress
    rw [BitVec.extractLsb'_append_eq_of_add_le (by decide), BitVec.extractLsb'_append_eq_left]

private theorem different_domains (k : Key) (a : Reply) (i : Position)
    (hit : keyHit a k) : a.extractLsb' 0 64 ≠ tag i := by
  obtain ⟨t,g,e⟩ := hit
  have first := e 0 (by decide)
  rw [zero_before t g k 0 (by unfold marker; omega)] at first
  intro bad
  have eq : (0 : BitVec 64) = tag i := first.trans bad
  have impossible := congrArg BitVec.toNat eq
  rw [tag_value] at impossible
  change 0 = 4152+256*i.val at impossible
  omega

theorem uniform_coordinate_guess {I R : Type} [Fintype I] [DecidableEq I] [Fintype R] [Nonempty R] [SampleableType R] (i : I) (guess : R) :
    Pr{let tape ← $ᵗ (I → R)}[tape i = guess] = (Fintype.card R : ENNReal)⁻¹ := by
  have marginal := evalDist_uniformSample_bind_update_map
    SampleableType.evalDist_uniformSample SampleableType.evalDist_uniformSample i
    (fun t : I → R => t i)
  simp only [Function.update_self] at marginal
  rw [bind_pure_comp] at marginal
  have dist : 𝒟[(fun a : I → R => a i) <$> ($ᵗ (I → R))] = 𝒟[$ᵗ R] := by
    calc
      _ = 𝒟[do let s ← $ᵗ R; let _ ← $ᵗ (I → R); pure s] := marginal.symm
      _ = 𝒟[($ᵗ R) >>= fun s => pure s] := by
        apply _root_.evalDist_bind_congr
        intro s
        exact OracleComp.evalDist_bind_const _ _
      _ = _ := by rw [bind_pure]
  have prob := (EvalDistEq.of_evalDist_eq dist).prEvent_eq (fun b => b = guess)
  simpa only [prEvent_map, SampleableType.prEvent_uniformSample_eq_singleton] using prob

theorem tag_hit_le {I : Type} [Fintype I] [DecidableEq I] (pos : I → Position) (inj : Function.Injective pos)
    (a : Reply) : Pr{let tape ← $ᵗ (I → Salt)}[tagHit pos a tape] ≤ 1 / (2^120 : ENNReal) := by
  classical
  by_cases h : ∃ i, a.extractLsb' 0 64 = tag (pos i)
  · obtain ⟨i,known⟩ := h
    have card : Fintype.card Salt = 2^120 := by rw [← FinEnum.card_eq_fintypeCard,FinEnum.card_bitVec]
    have bound := uniform_coordinate_guess i (a.extractLsb' 64 120)
    rw [card,Nat.cast_pow,Nat.cast_ofNat,← one_div] at bound
    refine (prEvent_mono _ _ (fun s => s i = a.extractLsb' 64 120) ?_).trans bound.le
    rintro tape ⟨j,hj,sj⟩
    have eq : j = i := inj (tag_inj (hj.symm.trans known))
    exact eq ▸ sj.symm
  · rw [(SampleableType.prEvent_uniformSample_eq_zero_iff _).2 (by
      rintro s ⟨i,hit,_⟩; exact h ⟨i,hit⟩)]
    exact zero_le

/-- An address in a public transcript can guess either a generator key or a hidden
salt. The position tag makes these classes disjoint before either secret is sampled. -/
theorem forward_guess_le {I : Type} [Fintype I] [DecidableEq I] (pos : I → Position) (inj : Function.Injective pos)
    (a : Reply) :
    Pr{let pair ← $ᵗ (Key × (I → Salt))}[keyHit a pair.1 ∨ tagHit pos a pair.2] ≤ 1 / (2^120 : ENNReal) := by
  classical
  by_cases validTag : ∃ i, a.extractLsb' 0 64 = tag (pos i)
  · obtain ⟨i,h⟩ := validTag
    apply SampleableType.prEvent_uniformSample_prod_le_of_forall_fst
    intro k
    refine (prEvent_mono _ _ (tagHit pos a) ?_).trans (tag_hit_le pos inj a)
    intro s hit
    exact hit.resolve_left (fun found => different_domains k a (pos i) found h)
  · apply SampleableType.prEvent_uniformSample_prod_le_of_forall_snd
    intro s
    refine (prEvent_mono _ _ (keyHit a) ?_).trans ((key_address_hit _).trans ?_)
    · intro k hit
      exact hit.resolve_right (fun ⟨i,h,_⟩ => validTag ⟨i,h⟩)
    · apply ENNReal.div_le_div_left
      exact pow_le_pow_right₀ (by norm_num) (by decide : 120 ≤ 192)

/-- This fixed-transcript bound allows any subset of positions to retain hidden salts.
It charges once per query across both message worlds and all generator rows. -/
theorem forward_transcript_le {I : Type} [Fintype I] [DecidableEq I] (pos : I → Position)
    (inj : Function.Injective pos) (q : Nat) (queries : Fin q → Reply) :
    Pr{let pair ← $ᵗ (Key × (I → Salt))}[∃ j, keyHit (queries j) pair.1 ∨ tagHit pos (queries j) pair.2]
      ≤ q / (2^120 : ENNReal) := by
  refine (prEvent_exists_le_card_mul _ _ (fun j => forward_guess_le pos inj (queries j))).trans_eq ?_
  simp only [Fintype.card_fin, mul_one_div]

/-- The transcript itself may be random and depend on a simulated public oracle.
The sampled key and hidden salts are independent of this transcript. -/
theorem forward_prior_le {S I : Type} [Fintype I] [DecidableEq I] (prior : ProbComp S)
    (pos : I → Position) (inj : Function.Injective pos) (q : Nat) (queries : S → Fin q → Reply) :
    Pr{let result ← (do let st ← prior; let pair ← $ᵗ (Key × (I → Salt)); pure (st,pair))}[
      ∃ j, keyHit (queries result.1 j) result.2.1 ∨ tagHit pos (queries result.1 j) result.2.2]
      ≤ q / (2^120 : ENNReal) := by
  apply prEvent_bind_le_of_forall_le_of_support
  intro st _
  rw [bind_pure_comp,prEvent_map]
  exact forward_transcript_le pos inj q (queries st)

attribute [local irreducible] blockSplit

/-- Conditional on distinct visible salt blocks, an inverse query can match at
most one group. It must still specify that group's independent 160-bit residue. -/
theorem inverse_generator_guess (blocks : Group → SaltBlock) (distinct : Function.Injective blocks)
    (candidate : Reply) :
    Pr{let tail ← $ᵗ (Group → Residue)}[
      ∃ g, blockSplit.symm (blocks g,tail g) = candidate] ≤ 1 / (2^160 : ENNReal) := by
  classical
  by_cases hit : ∃ g, blocks g = (blockSplit candidate).1
  · obtain ⟨g,hg⟩ := hit
    have card : Fintype.card Residue = 2^160 := by
      change Fintype.card (Fin 160 → Bool) = _
      rw [Fintype.card_fun,Fintype.card_bool,Fintype.card_fin]
    have bound := uniform_coordinate_guess g (blockSplit candidate).2
    rw [card,Nat.cast_pow,Nat.cast_ofNat,← one_div] at bound
    refine (prEvent_mono ($ᵗ (Group → Residue)) (fun t => ∃ j, blockSplit.symm (blocks j,t j) = candidate) (fun t => t g = (blockSplit candidate).2) ?_).trans ?_
    swap
    · exact bound.le
    rintro t ⟨j,e⟩
    have eq := blockSplit.symm_apply_eq.mp e
    have same : j = g := distinct ((congrArg Prod.fst eq).trans hg.symm)
    exact same ▸ congrArg Prod.snd eq
  · rw [(SampleableType.prEvent_uniformSample_eq_zero_iff _).2 (by
      rintro t ⟨j,e⟩; exact hit ⟨j,congrArg Prod.fst (blockSplit.symm_apply_eq.mp e)⟩)]
    exact zero_le

end CommitGolfCandidate.Reconstruction.HidingTape
