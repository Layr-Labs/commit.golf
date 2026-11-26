import CommitGolfCandidate.ReconstructedHidingTape
import CommitGolf.Oracle
import VCVio.OracleComp.Constructions.SampleableType.Measure

namespace CommitGolfCandidate.Reconstruction.HidingTape

open CommitGolf OracleComp Generator
set_option exponentiation.threshold 2048
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

noncomputable local instance functionSampler {ι α : Type} [Fintype ι] [Fintype α] [Nonempty α] :
    SampleableType (ι → α) := by classical exact SampleableType.ofFintype _

abbrev Group := Fin 4096 × Fin 342
abbrev Residue := Fin 160 → Bool
abbrev SaltBlock := Lane → Salt

private theorem card_bv (k : Nat) : Fintype.card (BitVec k) = 2^k := by
  rw [← FinEnum.card_eq_fintypeCard, FinEnum.card_bitVec]

/-- A complete block reply is equivalent to its disjoint visible and reserved coordinates. -/
noncomputable def blockSplit : Reply ≃ SaltBlock × Residue :=
  Equiv.ofBijective (fun r => (saltAt r, residual r))
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨fun _ _ e =>
      reply_ext (congrArg Prod.fst e) (congrArg Prod.snd e), by
        change Fintype.card (BitVec 1600) = Fintype.card ((Fin 12 → BitVec 120) × (Fin 160 → Bool))
        rw [Fintype.card_prod,Fintype.card_fun,Fintype.card_fun,card_bv,card_bv]
        norm_num⟩)

/-- The full ideal reply tape separates into all real salts, 32,768 spare salts
and one independent 160-bit residue per group. -/
noncomputable def tapeSplit : (Group → Reply) ≃
    (Position → Salt) × Slack × (Group → Residue) where
  toFun r :=
    let block : Blocks := fun t g => saltAt (r (t,g))
    (select block, unused block, fun g => residual (r g))
  invFun s := fun g => blockSplit.symm (assemble s.1 s.2.1 g.1 g.2, s.2.2 g)
  left_inv r := by
    funext g
    dsimp
    rw [assemble_select]
    exact blockSplit.symm_apply_apply (r g)
  right_inv s := by
    have block (g : Group) : saltAt (blockSplit.symm (assemble s.1 s.2.1 g.1 g.2, s.2.2 g)) =
        assemble s.1 s.2.1 g.1 g.2 :=
      congrArg Prod.fst (blockSplit.apply_symm_apply _)
    have high (g : Group) : residual (blockSplit.symm (assemble s.1 s.2.1 g.1 g.2, s.2.2 g)) = s.2.2 g :=
      congrArg Prod.snd (blockSplit.apply_symm_apply _)
    have reassemble : (fun t g => saltAt (blockSplit.symm (assemble s.1 s.2.1 t g, s.2.2 (t,g)))) =
        assemble s.1 s.2.1 := funext fun t => funext fun g => block (t,g)
    apply Prod.ext
    · dsimp only
      rw [reassemble,select_assemble]
    · apply Prod.ext
      · dsimp only
        rw [reassemble,unused_assemble]
      · exact funext high

/-- Sampling one independent word per group is exactly equivalent to sampling
the salt vector uniformly, even when all spare and residual bits are retained. -/
theorem ideal_tape_distribution :
    tapeSplit <$> ($ᵗ (Group → Reply)) =ᵈ ($ᵗ ((Position → Salt) × Slack × (Group → Residue))) :=
  SampleableType.map_uniformSample_evalDistEq_of_bijective tapeSplit.bijective

/-- All groups use one secret key. A given query determines at most one possible
key across the whole schedule, so the bound has no factor for the number of groups. -/
theorem key_address_hit (address : Nat → BitVec 64) :
    Pr{let k ← $ᵗ Key}[∃ (t : Fin 4096) (g : Fin 342),
      ∀ i < 25, inputWord t g k i = address i] ≤ 1 / (2^192 : ENNReal) := by
  classical
  by_cases h : ∃ (k : Key) (t : Fin 4096) (g : Fin 342), ∀ i < 25, inputWord t g k i = address i
  · obtain ⟨k,t,g,matched⟩ := h
    refine (prEvent_mono ($ᵗ Key) _ (fun x => x = k) ?_).trans ?_
    · rintro x ⟨u,v,hx⟩
      exact (input_injective u t v g x k (fun i hi => (hx i hi).trans (matched i hi).symm)).2.2
    · rw [SampleableType.prEvent_uniformSample_eq_singleton]
      have card : Fintype.card Key = 2^192 := by
        change Fintype.card (Fin 3 → BitVec 64) = _
        rw [Fintype.card_fun,card_bv,Fintype.card_fin]
        norm_num
      rw [card,Nat.cast_pow,Nat.cast_ofNat,one_div]
  · rw [(SampleableType.prEvent_uniformSample_eq_zero_iff _).2 (by
      rintro k ⟨t,g,hit⟩; exact h ⟨k,t,g,hit⟩)]
    exact zero_le

end CommitGolfCandidate.Reconstruction.HidingTape
