import CommitGolfCandidate.Layout2CapRoundtrip
import CommitGolfCandidate.TwoPermutationPackedNearCap
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.DefEqTransformations

/-! # One-byte search: decoding the truncated honest proof

The opener leaves out the final byte of a k = 128 proof of 72,160 bytes (`obEnc`); the checker reads the missing byte as
0. The final CAP-B byte holds exactly bits 6..7 of V1 cap bytes 3689, 3719, 3749, 3779 (`dec_final`, via Astra's
inverse tables), which are bits 230..237 of the last frontier digest (`pack_clear_128`). So the truncated honest proof
decodes to `nearCheckInput` (`near_decode`). -/
open CommitGolf

namespace CommitGolfCandidate.Layout2.Cap

/-- The V1 bits of a full block that the block's last CAP-B byte holds. -/
theorem dec_final (i : Nat) (hi : i < 8*952) :
    dec 32 i / 8 = 951 ↔ (i = 6670 ∨ i = 6671 ∨ i = 6910 ∨ i = 6911 ∨ i = 7150 ∨ i = 7151 ∨ i = 7390 ∨ i = 7391) := by
  constructor
  · intro h
    have valid := dec_valid 32 (by decide) (by decide) i (by rw [show size 32 = 952 by decide]; exact hi)
    have inv := dec_inverse 32 (by decide) (by decide) i (by rw [show size 32 = 952 by decide]; exact hi)
    rw [show size 32 = 952 by decide] at valid
    generalize hc : dec 32 i = c at h valid inv
    have : 7608 ≤ c ∧ c < 7616 := by omega
    obtain ⟨lo, hi'⟩ := this
    subst inv
    interval_cases c <;> decide
  · rintro (h|h|h|h|h|h|h|h) <;> subst h <;> decide

end CommitGolfCandidate.Layout2.Cap

namespace CommitGolfCandidate.Layout2.Quartet
open CommitGolf

theorem conv_get (τ : Tables) (k : Nat) (T : Proof) (q : Nat) (hq : q < T.length) :
    (convert τ k T)[q]? = some (convertAt τ k (fun j => T[j]?.getD 0) q) := by
  simp [convert, hq]

theorem trans_getD (b : Bool) (k : Nat) (qs : Selectors) (P : Proof) (complete : 534*k ≤ P.length) (j : Nat) :
    (transform b k qs P)[j]?.getD 0 = P[index b k qs j]?.getD 0 := by
  by_cases inside : j < P.length
  · exact read_transform b k qs P j complete inside
  · have big : P.length ≤ j := by omega
    have idx : index b k qs j = j := by unfold index; rw [if_neg (by omega)]
    rw [idx, List.getElem?_eq_none (by simpa using big), List.getElem?_eq_none big]

/-- The quartet decoder is the identity on the cap. -/
theorem decoder_cap (p : Positions) (P : Proof) (complete : 534*p.card ≤ P.length) (q : Nat) (hq : 534*p.card ≤ q) :
    (decoder p P)[q]? = P[q]? := by
  unfold decoder
  by_cases inside : q < P.length
  · rw [conv_get _ _ _ _ (by simpa using inside)]
    unfold convertAt
    rw [if_neg (by omega)]
    beta_reduce
    rw [trans_getD _ _ _ _ complete]
    have idx : index false p.card (selectors p) q = q := by unfold index; rw [if_neg (by omega)]
    rw [idx, List.getElem?_eq_getElem inside]
    rfl
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

/-- The quartet encoder is the identity on the cap. -/
theorem encoder_cap (p : Positions) (P : Proof) (complete : 534*p.card ≤ P.length) (q : Nat) (hq : 534*p.card ≤ q) :
    (encoder p P)[q]? = P[q]? := by
  unfold encoder
  by_cases inside : q < P.length
  · rw [List.getElem?_eq_getElem (by simpa using inside)]
    have t := trans_getD true p.card (selectors p) (convert encTables p.card P) (by simpa using complete) q
    have idx : index true p.card (selectors p) q = q := by unfold index; rw [if_neg (by omega)]
    rw [idx, List.getElem?_eq_getElem (by simpa using inside), conv_get _ _ _ _ inside] at t
    simp only [Option.getD_some] at t
    rw [List.getElem?_eq_getElem inside]
    congr 1
    rw [t]
    unfold convertAt
    rw [if_neg (by omega)]
    beta_reduce
    rw [List.getElem?_eq_getElem inside]
    rfl
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

/-- The quartet decoder's record part depends only on the record bytes. -/
theorem decoder_records (p : Positions) (P P' : Proof) (len : P'.length = P.length) (complete : 534*p.card ≤ P.length)
    (same : ∀ q, q < 534*p.card → P'[q]?.getD 0 = P[q]?.getD 0) (q : Nat) (hq : q < 534*p.card) :
    (decoder p P')[q]? = (decoder p P)[q]? := by
  unfold decoder
  rw [conv_get _ _ _ _ (by simp; omega), conv_get _ _ _ _ (by simp; omega)]
  apply congrArg some
  unfold convertAt
  rw [if_pos hq, if_pos hq]
  have g := q/2136
  have r := blockSize p.card (q/2136)
  have rpos : 1 ≤ blockSize p.card (q/2136) ∧ blockSize p.card (q/2136) ≤ 4 := by
    unfold blockSize; split <;> omega
  have inBlock : q%2136 < 534*blockSize p.card (q/2136) := by unfold blockSize; split <;> omega
  apply gather_congr dec_wellFormed rpos.1 rpos.2 inBlock
  intro b hb
  have abs : 2136*(q/2136)+b < 534*p.card := by unfold blockSize at hb; split at hb <;> omega
  beta_reduce
  rw [trans_getD _ _ _ _ (by omega), trans_getD _ _ _ _ complete]
  exact same _ ((index_facts false p.card (selectors p) _).1 abs)

end CommitGolfCandidate.Layout2.Quartet

namespace CommitGolfCandidate.Layout2.Cap
open CommitGolf

def mask4 (c : Nat) (v : Byte) : Byte := if c = 3689 ∨ c = 3719 ∨ c = 3749 ∨ c = 3779 then v &&& 63#8 else v

/-- Zeroing the final CAP-B byte of a k = 128 proof of 72,160 bytes clears exactly the top two bits of four V1 cap
bytes. -/
theorem cap_final_zero (E : Proof) (len : E.length = 72160) (c : Nat) (hc : c < 3808) :
    (transform dec 128 (E.take 72159 ++ [0]))[68352+c]?.getD 0 = mask4 c ((transform dec 128 E)[68352+c]?.getD 0) := by
  have len' : (E.take 72159 ++ [0]).length = 72160 := by simp [len]
  rw [read_transform _ _ _ _ (by omega), read_transform _ _ _ _ (by omega), if_pos (by omega), if_pos (by omega),
    len', len, show 68352+c-534*128 = c by omega, show 72160-534*128 = 3808 by rfl]
  unfold atByte
  have ch : chunk 3808 c = 32 := by unfold chunk; rw [if_pos (by omega)]
  rw [ch]
  have src (x : Nat) : (E.take 72159 ++ [0])[534*128+x]?.getD 0 = if x = 3807 then 0 else E[534*128+x]?.getD 0 := by
    by_cases e : x = 3807
    · subst e
      rw [if_pos rfl, List.getElem?_append_right (by simp only [List.length_take, len]; omega)]
      simp [len]
    · rw [if_neg e]
      by_cases small : x < 3807
      · rw [List.getElem?_append_left (by simp; omega), List.getElem?_take_of_lt (by omega)]
      · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  have dv := dec_valid 32 (by decide) (by decide) (8*(c%952)+b) (by rw [show size 32 = 952 by decide]; omega)
  rw [show size 32 = 952 by decide] at dv
  rw [gather_bit _ _ _ _ _ hb]
  beta_reduce
  rw [src]
  have final := dec_final (8*(c%952)+b) (by omega)
  unfold mask4
  by_cases hit : 952*(c/952)+dec 32 (8*(c%952)+b)/8 = 3807
  · -- the bit comes from the zeroed byte
    rw [if_pos hit]
    have g3 : c/952 = 3 := by omega
    have d951 : dec 32 (8*(c%952)+b)/8 = 951 := by omega
    have inS := final.mp d951
    have cIn : c = 3689 ∨ c = 3719 ∨ c = 3749 ∨ c = 3779 := by omega
    have bHigh : 6 ≤ b := by omega
    have m63 : (63#8).getLsbD b = false := by interval_cases b <;> first | omega | decide
    rw [if_pos cIn, BitVec.getLsbD_and, m63, Bool.and_false]
    simp
  · rw [if_neg hit]
    by_cases cIn : c = 3689 ∨ c = 3719 ∨ c = 3749 ∨ c = 3779
    · rw [if_pos cIn, BitVec.getLsbD_and, gather_bit _ _ _ _ _ hb]
      have bLow : b < 6 := by
        by_contra big
        have : 8*(c%952)+b = 6670 ∨ 8*(c%952)+b = 6671 ∨ 8*(c%952)+b = 6910 ∨ 8*(c%952)+b = 6911 ∨
          8*(c%952)+b = 7150 ∨ 8*(c%952)+b = 7151 ∨ 8*(c%952)+b = 7390 ∨ 8*(c%952)+b = 7391 := by omega
        have := final.mpr this
        omega
      have m63 : (63#8).getLsbD b = true := by interval_cases b <;> first | omega | decide
      rw [m63, Bool.and_true]
    · rw [if_neg cIn, gather_bit _ _ _ _ _ hb]


/-- The truncated honest encoding, padded with 0, decodes to the honest V1 proof with the top two bits of four cap
bytes cleared. -/
theorem decode_trunc (p : Positions) (k128 : p.card = 128) (H H' : Proof) (len : H.length = 72160)
    (len' : H'.length = 72160) (good : Good p.card H.length)
    (same : ∀ q, q < 68352 → H'[q]? = H[q]?)
    (cap : ∀ c, c < 3808 → H'[68352+c]?.getD 0 = mask4 c (H[68352+c]?.getD 0)) :
    decoder p ((encoder p H).take 72159 ++ [0]) = H' := by
  let E := encoder p H
  have elen : E.length = 72160 := by simp [E, len]
  let Q := Quartet.encoder p H
  have qlen : Q.length = 72160 := by simp [Q, len]
  have goodQ : Good p.card Q.length := by rw [qlen, ← len]; exact good
  have Y : transform dec p.card E = Q := inverse dec_valid dec_inverse _ _ goodQ
  let E' := E.take 72159 ++ [0]
  have elen' : E'.length = 72160 := by simp [E', elen]
  have ylen' : (transform dec p.card E').length = 72160 := by simp [elen']
  unfold decoder
  apply List.ext_getElem?
  intro q
  by_cases inRange : q < 72160
  · by_cases rec : q < 68352
    · have below : ∀ i, i < 534*p.card → (transform dec p.card E')[i]?.getD 0 = (transform dec p.card E)[i]?.getD 0 := by
        intro i hi
        rw [read_transform _ _ _ _ (by omega), read_transform _ _ _ _ (by omega), if_neg (by omega), if_neg (by omega)]
        rw [List.getElem?_append_left (by simp [elen]; omega), List.getElem?_take_of_lt (by omega)]
      rw [Quartet.decoder_records p _ _ (by simp [elen', elen]) (by simp [elen]; omega) below q (by omega), Y,
        Quartet.decode_encode p H (by omega), same q rec]
    · rw [Quartet.decoder_cap p _ (by simp [elen']; omega) q (by omega)]
      have c := q-68352
      have zero := cap_final_zero E elen (q-68352) (by omega)
      rw [k128]
      rw [show 68352+(q-68352) = q by omega] at zero
      rw [List.getElem?_eq_getElem (by simp [elen']; omega), List.getElem?_eq_getElem (by omega)]
      apply congrArg some
      have z' := zero
      rw [List.getElem?_eq_getElem (by simp [elen']; omega), Option.getD_some] at z'
      rw [z', ← k128, Y]
      have qe := Quartet.encoder_cap p H (by omega) q (by omega)
      have hc := cap (q-68352) (by omega)
      rw [show 68352+(q-68352) = q by omega] at hc
      rw [qe, ← hc, List.getElem?_eq_getElem (by omega)]
      rfl
  · rw [List.getElem?_eq_none (by simp [elen']; omega), List.getElem?_eq_none (by omega)]

end CommitGolfCandidate.Layout2.Cap

namespace CommitGolfCandidate.Layout2.Cap
open CommitGolf TwoPermutationPrototype TwoPermutationPrototype.Packed.Checker TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.QuartetCertificate (honestCheckInput)

/-- The one-byte search's encoding: , less the final byte when  and the encoded proof has 72,160
bytes. -/
theorem honest_good' (o : Oracle) (msg : Message) (p : Positions) (salts : Index → BitVec 128) :
    Good p.card (honestCheckInput o msg p salts).proof.length := by
  rw [PackedHonest.honest_proof_length,←size_eq]
  apply good_shape
  intro empty;simp [Opening.openingNodes,empty]

def obEnc (p : Positions) (P : Proof) : Proof :=
  if p.card=128 ∧ (encoder p P).length=72160 then (encoder p P).take 72159 else encoder p P

theorem near_decode (o : Oracle) (m : Message) (p : Positions) (s : CompleteSaltTape) (k128 : p.card = 128)
    (f128 : (honestNodes o m p s).length = 128) :
    decoder p ((encoder p (honestCheckInput o m p s).proof).take 72159 ++ [0]) = (nearCheckInput o m p s).proof := by
  let H := (honestCheckInput o m p s).proof
  have parts := PackedHonest.honest_proof_parts o m p s
  have nonempty : (Opening.groupsBefore p p.card).isEmpty = false := by
    apply Bool.eq_false_of_not_eq_true
    intro e
    rw [List.isEmpty_iff] at e
    unfold honestNodes at f128
    rw [e] at f128
    simp [capFrontierNodes, capIsMarked] at f128
  have frontier : TwoPermutationPrototype.Sampling.Quartet.frontierProof238 (PackedHonest.honestHeap o m s) (Opening.groupsBefore p p.card) =
      TwoPermutationPrototype.Sampling.Quartet.packNodes (honestNodes o m p s) := by
    unfold TwoPermutationPrototype.Sampling.Quartet.frontierProof238 honestNodes
    rw [if_neg (by rw [nonempty]; decide)]
  rw [frontier] at parts
  obtain ⟨R, partsR, width⟩ : ∃ R : List Byte, H = R ++ TwoPermutationPrototype.Sampling.Quartet.packNodes (honestNodes o m p s) ∧
      R.length = 534*p.card :=
    ⟨_, parts, by
      rw [PackedHonest.fixed_flatmap_length _ 534 (fun _ => TwoPermutationPrototype.Sampling.Quartet.opening_record_length _ _ _ _) _,
        PackedHonest.honest_order_length]⟩
  have plen : (TwoPermutationPrototype.Sampling.Quartet.packNodes (honestNodes o m p s)).length = 3808 := by
    rw [pack_nodes_length', f128]
  have hlen : H.length = 72160 := by rw [partsR, List.length_append, width, plen, k128]
  have near := near_honest_input o m p s (by omega)
  have nlen : (nearCheckInput o m p s).proof.length = 72160 := near.length.trans hlen
  have nproof : (nearCheckInput o m p s).proof = H.take (534*p.card) ++
      TwoPermutationPrototype.Sampling.Quartet.packNodes (clearLast (honestNodes o m p s)) := rfl
  have takeR : H.take (534*p.card) = R := by
    rw [partsR, List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
  apply decode_trunc p k128 H _ hlen nlen (honest_good' o m p s)
  · intro q hq
    rw [nproof, takeR, partsR, List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)]
  · intro c hc
    rw [nproof, takeR, partsR, List.getElem?_append_right (by omega), List.getElem?_append_right (by omega), width,
      k128, show 68352+c-534*128 = c by omega, pack_clear_128 _ f128 c]
    unfold mask4
    cases (TwoPermutationPrototype.Sampling.Quartet.packNodes (honestNodes o m p s))[c]? <;> (try rfl) <;> split <;> rfl

end CommitGolfCandidate.Layout2.Cap
