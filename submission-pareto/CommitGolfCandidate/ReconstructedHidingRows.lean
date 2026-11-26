import CommitGolfCandidate.ReconstructedHidingPinned
import CommitGolfCandidate.ReconstructedHidingInverse
import CommitGolfCandidate.SharedPinnedRows

namespace CommitGolfCandidate.Reconstruction.HidingTape
open CommitGolf OracleComp TwoPermutationPrototype.Sampling TwoPermutationPrototype.RV64
set_option maxRecDepth 12000
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2048

theorem pinned_address_salt (i : Index) (reply : Reply) (m : TwoPermutationPrototype.Words 32)
    (s : Salt) :
    (pinnedPrivateSecond i reply m (s.setWidth 128)).extractLsb' 64 120 = s := by
  unfold pinnedPrivateSecond
  rw [mask_widen]
  let words := pinnedSecondInput i (saltWords (s.setWidth 128)) (replyWords reply) m
  change (packBuffer words).extractLsb' 64 120 = s
  have lo : (packBuffer words).extractLsb' 64 64 = (s.setWidth 128).extractLsb' 0 64 :=
    packed_word words (1 : Fin 25)
  have hi : (packBuffer words).extractLsb' 128 64 = (s.setWidth 128).extractLsb' 64 64 :=
    packed_word words (2 : Fin 25)
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  by_cases lower : j < 64
  · have b := congrArg (fun w : BitVec 64 => w.getLsbD j) lo
    simpa [hj,lower,show j<128 by omega] using b
  · have b := congrArg (fun w : BitVec 64 => w.getLsbD (j-64)) hi
    have inHigh : j-64<64 := by omega
    have col : 64+(j-64)=j := by omega
    have off : 128+(j-64)=64+j := by omega
    simpa [hj,inHigh,col,off,show j<128 by omega] using b

theorem pinned_tag_hit {I : Type} (pos : I → Position) (i : I) (reply : Reply)
    (m : TwoPermutationPrototype.Words 32) (salt : I → Salt) :
    tagHit pos (pinnedPrivateSecond (pos i) reply m ((salt i).setWidth 128)) salt :=
  ⟨i,pinned_second_tag (pos i) (saltWords (maskSalt ((salt i).setWidth 128))) reply m,
    pinned_address_salt _ _ _ _⟩

theorem pinned_input_nonzero (i : Index) (reply : Reply) (m : TwoPermutationPrototype.Words 32)
    (s : BitVec 128) : pinnedPrivateSecond i reply m s ≠ 0 := by
  intro eq
  have z := congrArg (fun b : Reply => (b.extractLsb' 0 64).toNat) eq
  have tagEq := pinned_second_tag i (saltWords (maskSalt s)) reply m
  change ((pinnedPrivateSecond i reply m s).extractLsb' 0 64).toNat = 0 at z
  change (pinnedPrivateSecond i reply m s).extractLsb' 0 64 = pinnedPositionTag i at tagEq
  rw [tagEq,pinnedPositionTag,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have h : i.val<2^24 := i.isLt; omega)] at z
  omega

noncomputable def reverseUpper {base : Cache} (cache : PinnedHighCache base) (high : BitVec 1344) : Option Reply := by
  classical exact if h : ∃ x, pinnedAddedUpper cache x = some high then some (Classical.choose h) else none

theorem reverse_upper_lookup {base : Cache} (cache : PinnedHighCache base) {slot : Nat} (valid : cache.Valid slot)
    {a : Reply} {hi : BitVec 1344} (stored : pinnedAddedUpper cache a = some hi) :
    reverseUpper cache hi = some a := by
  classical
  have existsHit : ∃ x, pinnedAddedUpper cache x = some hi := ⟨a,stored⟩
  rw [reverseUpper,dite_eq_left existsHit]
  exact congrArg some (pinned_added_upper_injective cache valid _ _ _ (Classical.choose_spec existsHit) stored)

theorem latent_output_guess {I : Type} {base : Cache} (cache : PinnedHighCache base) {slot : Nat}
    (valid : cache.Valid slot) (pos : I → Position) (first : I → Reply)
    (msg : I → TwoPermutationPrototype.Words 32) (digest : I → BitVec 256) (salt : I → Salt) (y : Reply)
    (reused : ∃ i, (pinnedAddedUpper cache (pinnedPrivateSecond (pos i) (first i) (msg i) ((salt i).setWidth 128))).map
      (fun hi => (hi ++ digest i : Reply)) = some y) :
    ∃ a, reverseUpper cache (outputTail y) = some a ∧ tagHit pos a salt := by
  obtain ⟨i,matched⟩ := reused
  let a := pinnedPrivateSecond (pos i) (first i) (msg i) ((salt i).setWidth 128)
  change (pinnedAddedUpper cache a).map (fun hi => (hi ++ digest i : Reply)) = some y at matched
  cases h : pinnedAddedUpper cache a with
  | none => rw [h] at matched; cases matched
  | some hi =>
    rw [h] at matched
    have same : (hi ++ digest i : Reply) = y := Option.some.inj matched
    have top : outputTail y = hi := by rw [←same]; exact BitVec.extractLsb'_append_eq_left
    exact ⟨a,top ▸ reverse_upper_lookup cache valid h,pinned_tag_hit pos i (first i) (msg i) salt⟩

theorem new_output_le {I : Type} [Fintype I] {base : Cache} {count : Nat}
    (state : PinnedOpenedState base count) (valid : state.high.Valid count)
    (pos : I → Position) (first : I → Reply) (msg : I → TwoPermutationPrototype.Words 32)
    (digest : I → BitVec 256) (salt : I → Salt) (y : Reply)
    (room : state.high.zero.entries.length + Fintype.card I ≤ 2^121)
    (unmatched : ¬∃ a, reverseUpper state.high (outputTail y) = some a ∧ tagHit pos a salt) :
    Pr{let rows ← pinnedRowsNonce state pos first msg digest (fun i => (salt i).setWidth 128)}[
      ∃ e ∈ rows, e.2 = y] ≤ (Fintype.card I : ENNReal)/2^1343 := by
  classical
  let nonce := fun i => (salt i).setWidth 128
  have safe : ¬ ((∃ i, pinnedPrivateSecond (pos i) (first i) (msg i) (nonce i) = (0 : Reply)) ∨
      ∃ i, (pinnedAddedUpper state.high (pinnedPrivateSecond (pos i) (first i) (msg i) (nonce i))).map
      (fun hi => (hi ++ digest i : Reply)) = some y) := by
    rintro (⟨i,bad⟩|old)
    · exact pinned_input_nonzero _ _ _ _ bad
    · exact unmatched (latent_output_guess state.high valid pos first msg digest salt y old)
  have estimate := rows_nonce_fresh_hit_le state valid pos first msg digest room (0,y) nonce safe
  refine (prEvent_mono _ _ (fun rows => rowHits rows (0,y) = true) ?_).trans estimate
  rintro rows ⟨e,inRows,hit⟩
  exact List.any_eq_true.mpr ⟨e,inRows,decide_eq_true (Or.inr hit.symm)⟩

end CommitGolfCandidate.Reconstruction.HidingTape
