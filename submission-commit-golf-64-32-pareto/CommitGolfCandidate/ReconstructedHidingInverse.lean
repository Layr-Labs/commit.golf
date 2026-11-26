import CommitGolfCandidate.ReconstructedHidingGuesses

namespace CommitGolfCandidate.Reconstruction.HidingTape
open CommitGolf OracleComp Generator
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048
set_option maxHeartbeats 2000000
noncomputable local instance inverseSampler {ι α : Type} [Fintype ι] [Fintype α] [Nonempty α] :
    SampleableType (ι → α) := by classical exact SampleableType.ofFintype _
local instance inverseDiscrete {α : Type} : MeasurableSpace α := ⊤

abbrev Signature := Fin 3 → Salt
def signature (block : SaltBlock) : Signature :=
  fun t => block ⟨9+t.val,by have := t.isLt; omega⟩
def outputTail (y : Reply) := y.extractLsb' 256 1344
def tailSignature (tail : BitVec 1344) : Signature :=
  fun t => tail.extractLsb' (768 + 128*t.val) 120

theorem signature_tail (y : Reply) : signature ((blockSplit y).1) = tailSignature (outputTail y) := by
  funext t
  change y.extractLsb' (saltBit ⟨9+t.val,by have := t.isLt; omega⟩ 0) 120 =
    (y.extractLsb' 256 1344).extractLsb' (768 + 128*t.val) 120
  have bitStart : saltBit ⟨9+t.val,by have := t.isLt; omega⟩ 0 = 256+(768+128*t.val) := by
    unfold saltBit
    simp only [Fin.val_zero,Nat.add_zero]
    split <;> omega
  rw [bitStart]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have room : 768+(128*t.val+i) < 1344 := by have := t.isLt; omega
  simp [hi,room,Nat.add_assoc]

attribute [local irreducible] blockSplit

private def splitSignature : SaltBlock ≃ Signature × (Fin 9 → Salt) where
  toFun b := (signature b, fun t => b ⟨t.val,by have := t.isLt; omega⟩)
  invFun pair l := if small : l.val < 9 then pair.2 ⟨l.val,small⟩
    else pair.1 ⟨l.val-9,by have := l.isLt; omega⟩
  left_inv b := by
    funext l
    dsimp only
    split
    · rfl
    · rename_i large
      dsimp only [signature]
      congr 1
      exact Fin.ext (by change 9+(l.val-9)=l.val; omega)
  right_inv pair := by
    apply Prod.ext
    · funext t
      simp [signature]
    · funext t
      simp only [t.isLt,dite_true,Fin.eta]

private def splitSignatures {G : Type} : (G → SaltBlock) ≃ ((G → Signature) × (G → Fin 9 → Salt)) where
  toFun table := (fun g => signature (table g), fun g => (splitSignature (table g)).2)
  invFun pair g := splitSignature.symm (pair.1 g,pair.2 g)
  left_inv table := funext fun g => splitSignature.symm_apply_apply (table g)
  right_inv pair := Prod.ext
    (funext fun g => congrArg Prod.fst (splitSignature.apply_symm_apply (pair.1 g,pair.2 g)))
    (funext fun g => congrArg Prod.snd (splitSignature.apply_symm_apply (pair.1 g,pair.2 g)))

theorem signature_guess {G : Type} [Fintype G] [DecidableEq G] (g : G) (v : Signature) :
    Pr{let d ← $ᵗ (G → SaltBlock)}[signature (d g) = v] = 1/(2^360 : ENNReal) := by
  have card : Fintype.card Signature = 2^360 := by
    change Fintype.card (Fin 3 → BitVec 120) = _
    rw [Fintype.card_fun,Fintype.card_fin,← FinEnum.card_eq_fintypeCard,FinEnum.card_bitVec]
    norm_num
  have changeSpace := SampleableType.prEvent_uniformSample_equiv (splitSignatures (G := G))
    (fun p => p.1 g = v)
  rw [SampleableType.prEvent_uniformSample_fst (fun d : G → Signature => d g = v), uniform_coordinate_guess,
    card,Nat.cast_pow,Nat.cast_ofNat,← one_div] at changeSpace
  exact changeSpace

/-- A fixed collection of upper traces is exceedingly unlikely to share even
three complete visible lanes with any independent generator block. Any inverse
endpoint qualifying for both roles necessarily creates this signature event. -/
theorem tail_overlap_bound {G J : Type} [Fintype G] [DecidableEq G] [Fintype J]
    (tails : J → BitVec 1344) :
    Pr{let d ← $ᵗ (G → SaltBlock)}[∃ (g : G) (j : J),
      signature (d g) = tailSignature (tails j)] ≤
      (Fintype.card G : ENNReal)*Fintype.card J/2^360 := by
  have h := prEvent_exists_le_card_mul ($ᵗ (G → SaltBlock))
    (fun (g : G) (d : G → SaltBlock) => ∃ j, signature (d g) = tailSignature (tails j))
    (fun g => prEvent_exists_le_card_mul ($ᵗ (G → SaltBlock))
      (fun (j : J) (d : G → SaltBlock) => signature (d g) = tailSignature (tails j))
      (fun j => (signature_guess g (tailSignature (tails j))).le))
  simpa only [mul_one_div,mul_div_assoc] using h

/-- The overlap test is independent of a queried endpoint and may be charged
once for every inverse query made with the same preexisting table. -/
theorem matching_tail (blocks : Group → SaltBlock) (tails : Set (BitVec 1344))
    (noOverlap : ∀ g, ∀ tail ∈ tails, signature (blocks g) ≠ tailSignature tail)
    (candidate : Reply) (inTable : outputTail candidate ∈ tails) :
    ∀ g (r : Residue), blockSplit.symm (blocks g,r) ≠ candidate := by
  intro g r eq
  have d := congrArg Prod.fst (blockSplit.symm_apply_eq.mp eq)
  exact noOverlap g (outputTail candidate) inTable ((congrArg signature d).trans (signature_tail _))

/-- If the candidate tail resolves to an existing high row, its latent input
determines one possible nonce. Otherwise at most one compatible generator
residue can match. Both cases share the same query allowance. -/
theorem joint_inverse_guess {I : Type} [Fintype I] [DecidableEq I]
    (position : I → Position) (unique : Function.Injective position)
    (blocks : (I → Salt) → Group → SaltBlock)
    (latent : BitVec 1344 → Option Reply) (candidate : Reply) :
    Pr{let pair ← $ᵗ ((I → Salt) × (Group → Residue))}[
      (∃ a, latent (outputTail candidate) = some a ∧ tagHit position a pair.1) ∨
      (Function.Injective (blocks pair.1) ∧
        (∀ g, ∀ hi, (latent hi).isSome → signature (blocks pair.1 g) ≠ tailSignature hi) ∧
        ∃ g, blockSplit.symm (blocks pair.1 g, pair.2 g) = candidate)]
      ≤ 1/(2^120 : ENNReal) := by
  classical
  cases h : latent (outputTail candidate) with
  | some a =>
    apply SampleableType.prEvent_uniformSample_prod_le_of_forall_snd
    intro r
    refine (prEvent_mono _ _ (tagHit position a) ?_).trans (tag_hit_le position unique a)
    rintro s (⟨b,found,hit⟩ | ⟨_,sep,g,found⟩)
    · exact (Option.some.inj found) ▸ hit
    · have seen : (latent (outputTail candidate)).isSome := by rw [h]; rfl
      have same := congrArg Prod.fst (blockSplit.symm_apply_eq.mp found)
      exact (sep g _ seen ((congrArg signature same).trans (signature_tail _))).elim
  | none =>
    apply SampleableType.prEvent_uniformSample_prod_le_of_forall_fst
    intro s
    by_cases distinct : Function.Injective (blocks s)
    · refine (prEvent_mono ($ᵗ (Group → Residue)) _ (fun r => ∃ g, blockSplit.symm (blocks s g,r g) = candidate) ?_).trans
        ((inverse_generator_guess (blocks s) distinct candidate).trans ?_)
      · rintro r (⟨_,hit,_⟩ | ⟨_,_,found⟩)
        · contradiction
        · exact found
      · apply ENNReal.div_le_div_left
        exact pow_le_pow_right₀ (by norm_num) (by decide : 120 ≤ 160)
    · rw [(SampleableType.prEvent_uniformSample_eq_zero_iff _).2 (by
        rintro r (⟨_,hit,_⟩ | ⟨inj,_⟩)
        · contradiction
        · exact distinct inj)]
      exact zero_le

end CommitGolfCandidate.Reconstruction.HidingTape
