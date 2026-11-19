import CommitGolfCandidate.TaggedPinnedHiddenRows

/-! Joint nonce guesses for message worlds sharing one hidden nonce tape. -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp CommitGolfCandidate
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 2048

noncomputable local instance SharedNonceHitsFunctionSampler {ι α : Type} [Fintype ι] [Fintype α] [Nonempty α] :
    SampleableType (ι → α) := by
  classical
  exact SampleableType.ofFintype _

private theorem shared_nonce_of_address (i j : Index) (a b : Block)
    (m n : Words 32) (r s : BitVec 128)
    (same : pinnedPrivateSecond i a m r = pinnedPrivateSecond j b n s) :
    maskSalt r = maskSalt s := by
  have words := packBuffer_injective same
  have low : (maskSalt r).extractLsb' 0 64 = (maskSalt s).extractLsb' 0 64 := by
    simpa [pinnedSecondInput, saltWords] using congrFun words (1 : Fin 25)
  have high : (maskSalt r).extractLsb' 64 64 = (maskSalt s).extractLsb' 64 64 := by
    simpa [pinnedSecondInput, saltWords] using congrFun words (2 : Fin 25)
  have rebuild (x : BitVec 128) : x.extractLsb' 64 64 ++ x.extractLsb' 0 64 = x :=
    BitVec.extractLsb'_append_extractLsb'
  rw [← rebuild (maskSalt r), ← rebuild (maskSalt s), low, high]

section Tape
variable {I W : Type} [Fintype I] [DecidableEq I]

theorem shared_fixed_address_hit_le (position : I → Index) (different : Function.Injective position)
    (reply : W → I → Block) (message : W → I → Words 32) (guess : Block) :
    Pr{let nonce ← $ᵗ (I → BitVec 128)}[∃ w i,
      pinnedPrivateSecond (position i) (reply w i) (message w i) (nonce i) = guess] ≤
      (1 : ENNReal)/2^122 := by
  classical
  let event (nonce : I → BitVec 128) := ∃ w i,
    pinnedPrivateSecond (position i) (reply w i) (message w i) (nonce i) = guess
  by_cases found : ∃ (w : W) (nonce : I → BitVec 128) (i : I),
      pinnedPrivateSecond (position i) (reply w i) (message w i) (nonce i) = guess
  · obtain ⟨w₀, nonce₀, i₀, anchor⟩ := found
    refine (prEvent_mono ($ᵗ (I → BitVec 128)) (p := event)
      (q := fun nonce => ∃ i,
        pinnedPrivateSecond (position i) (reply w₀ i) (message w₀ i) (nonce i) = guess) ?_).trans
      (pinned_fixed_address_hit_le position different (reply w₀) (message w₀) guess)
    rintro nonce ⟨w, i, hit⟩
    have index : i = i₀ := different (pinned_second_input_distinct_indices
      (position i) (position i₀) _ _ _ _ _ _ (hit.trans anchor.symm))
    subst i
    have salt := shared_nonce_of_address (position i₀) (position i₀)
      (reply w i₀) (reply w₀ i₀) (message w i₀) (message w₀ i₀)
      (nonce i₀) (nonce₀ i₀) (hit.trans anchor.symm)
    refine ⟨i₀, ?_⟩
    unfold pinnedPrivateSecond
    rw [salt]
    exact anchor
  · rw [prEvent_eq_zero_of_forall_mem_support _ _ (fun nonce _ ⟨w, i, hit⟩ =>
      found ⟨w, nonce, i, hit⟩)]
    exact zero_le

theorem shared_known_address_hit_le (position : I → Index) (different : Function.Injective position)
    (reply : W → I → Block) (message : W → I → Words 32) (known : List Block) :
    Pr{let nonce ← $ᵗ (I → BitVec 128)}[∃ address ∈ known, ∃ w i,
      pinnedPrivateSecond (position i) (reply w i) (message w i) (nonce i) = address] ≤
      (known.length : ENNReal)/2^122 := by
  simpa only [mul_one_div] using prEvent_list_le known ($ᵗ (I → BitVec 128))
    (fun address nonce => ∃ w i,
      pinnedPrivateSecond (position i) (reply w i) (message w i) (nonce i) = address)
    (1/2^122) (fun address _ => shared_fixed_address_hit_le position different reply message address)

theorem shared_reused_output_hit_le (position : I → Index) (different : Function.Injective position)
    (reply : W → I → Block) (message : W → I → Words 32)
    (latent : Block → Option (BitVec 1344))
    (unique : ∀ a b hi, latent a = some hi → latent b = some hi → a = b)
    (digest : I → BitVec 256) (guess : Block) :
    Pr{let nonce ← $ᵗ (I → BitVec 128)}[∃ w i,
      (latent (pinnedPrivateSecond (position i) (reply w i) (message w i) (nonce i))).map
        (fun hi => (hi ++ digest i : Block)) = some guess] ≤ (1 : ENNReal)/2^122 := by
  classical
  let event (nonce : I → BitVec 128) := ∃ w i,
    (latent (pinnedPrivateSecond (position i) (reply w i) (message w i) (nonce i))).map
      (fun hi => (hi ++ digest i : Block)) = some guess
  have tailHit (nonce : I → BitVec 128) : event nonce → ∃ w i,
      latent (pinnedPrivateSecond (position i) (reply w i) (message w i) (nonce i)) =
        some (pinnedOutputTail guess) := by
    rintro ⟨w, i, found⟩
    let address := pinnedPrivateSecond (position i) (reply w i) (message w i) (nonce i)
    change (latent address).map (fun hi => (hi ++ digest i : Block)) = some guess at found
    cases eq : latent address with
    | none => simp [eq] at found
    | some hi =>
      have foundEq : (some (hi ++ digest i) : Option Block) = some guess := by
        rw [eq] at found
        exact found
      have output : (hi ++ digest i : Block) = guess := Option.some.inj foundEq
      have split : pinnedOutputTail (hi ++ digest i) = hi := BitVec.extractLsb'_append_eq_left
      exact ⟨w, i, eq.trans (congrArg some (split.symm.trans (congrArg pinnedOutputTail output)))⟩
  by_cases present : ∃ address, latent address = some (pinnedOutputTail guess)
  · obtain ⟨address, known⟩ := present
    refine (prEvent_mono ($ᵗ (I → BitVec 128)) (p := event)
      (q := fun nonce => ∃ w i,
        pinnedPrivateSecond (position i) (reply w i) (message w i) (nonce i) = address) ?_).trans
      (shared_fixed_address_hit_le position different reply message address)
    intro nonce hit
    obtain ⟨w, i, found⟩ := tailHit nonce hit
    exact ⟨w, i, unique _ _ _ found known⟩
  · rw [prEvent_eq_zero_of_forall_mem_support _ _ (fun nonce _ hit => by
      obtain ⟨w, i, found⟩ := tailHit nonce hit
      exact present ⟨_, found⟩)]
    exact zero_le

end Tape
end TwoPermutationPrototype.Sampling
