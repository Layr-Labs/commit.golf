import CommitGolfCandidate.S3PermUnary
import Mathlib.Data.FinEnum

/-!
# The stage-3 byte layout as a two-call hash, with its counts

`s3TwoCall` is the `TwoCall` instance on the 1600-bit state behind `s3First`, `s3Second` and
`s3LeafDigest` (S3Leaf.lean; the link is proved in S3LeafBinding.lean):

* first-call input `x1`: leaf bytes 0..184 (1472 bits), placed after 16 zero bytes;
* chaining value: bytes 96..200 of a reply (832 bits);
* second-call input: nonce (192 bits), chaining value, leaf bytes 184..256 (576 bits);
* digest: bytes 0..32 of a reply.

Counts: `2^1472` valid first-call inputs, `2^768` states per chaining value, `2^768` second-call
inputs per chaining slot, `2^1344` states per digest. `s3_union_bound_le` reads the union bound
at these sizes: for `q` adversary queries and `e` probed leaves with `q + 2 e ≤ 2^128`,
it is at most `(q + 2 e)^2 / 2^256 + q / 2^127`. This file needs Mathlib only.
-/

set_option exponentiation.threshold 2100

namespace CommitGolfCandidate.Permutation

open Finset

/-- The state of the ideal permutation. -/
abbrev S3State := BitVec 1600

/-- Input of the two-call leaf hash: first message part, nonce, second message part. -/
abbrev S3LeafInput := BitVec 1472 × BitVec 192 × BitVec 576

theorem s3_card_bitvec (n : ℕ) : Fintype.card (BitVec n) = 2 ^ n := by
  rw [← FinEnum.card_eq_fintypeCard, FinEnum.card_bitVec]

theorem s3_card_state : Fintype.card S3State = 2 ^ 1600 := s3_card_bitvec _

theorem s3_state_lt (s : S3State) : s.toNat < 2 ^ 1600 := s.isLt

theorem s3_enc1_injective :
    Function.Injective fun x : BitVec 1472 => (BitVec.ofNat 1600 (x.toNat * 2 ^ 128) : S3State) := by
  intro x y h
  have hx := x.isLt
  have hy := y.isLt
  have h' := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at h'
  apply BitVec.eq_of_toNat_eq
  omega

theorem s3_enc2_injective :
    Function.Injective fun i : BitVec 192 × BitVec 832 × BitVec 576 =>
      (BitVec.ofNat 1600 (i.1.toNat + i.2.1.toNat * 2 ^ 192 + i.2.2.toNat * 2 ^ 1024) : S3State) := by
  rintro ⟨r, c, m⟩ ⟨r', c', m'⟩ h
  have hr := r.isLt
  have hc := c.isLt
  have hm := m.isLt
  have hr' := r'.isLt
  have hc' := c'.isLt
  have hm' := m'.isLt
  have h' := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at h'
  have e1 : r.toNat = r'.toNat := by omega
  have e2 : c.toNat = c'.toNat := by omega
  have e3 : m.toNat = m'.toNat := by omega
  rw [BitVec.eq_of_toNat_eq e1, BitVec.eq_of_toNat_eq e2, BitVec.eq_of_toNat_eq e3]

/-- The stage-3 leaf hash as a two-call hash on the 1600-bit state. A leaf input is
`(first message part, nonce, second message part)`; the second call encodes
`(nonce, chaining value, second message part)`. -/
def s3TwoCall : TwoCall S3State (BitVec 1472) (BitVec 192) (BitVec 832) (BitVec 576) (BitVec 256)
    where
  enc1 x := BitVec.ofNat 1600 (x.toNat * 2 ^ 128)
  chop o := BitVec.ofNat 832 (o.toNat / 2 ^ 768)
  enc2 i := BitVec.ofNat 1600 (i.1.toNat + i.2.1.toNat * 2 ^ 192 + i.2.2.toNat * 2 ^ 1024)
  trunc o := BitVec.ofNat 256 o.toNat
  enc1_inj := s3_enc1_injective
  enc2_inj := s3_enc2_injective

/-! ### Counts -/

theorem s3_first_inputs : Fintype.card (BitVec 1472) ≤ 2 ^ 1472 := (s3_card_bitvec _).le

theorem s3_second_inputs : Fintype.card (BitVec 192) * Fintype.card (BitVec 576) ≤ 2 ^ 768 := by
  rw [s3_card_bitvec, s3_card_bitvec, ← pow_add]

/-- At most `2^768` states have a given chaining value. -/
theorem s3_chop_fiber (c : BitVec 832) :
    (univ.filter fun s : S3State => s3TwoCall.chop s = c).card ≤ 2 ^ 768 := by
  have h := Finset.card_le_card_of_injOn (s := univ.filter fun s : S3State => s3TwoCall.chop s = c)
    (t := (univ : Finset (BitVec 768))) (fun s => BitVec.ofNat 768 s.toNat)
    (by intro a _; simp) (by
      intro a ha b hb hab
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ha hb
      have e1 := congrArg BitVec.toNat (ha.trans hb.symm)
      have e2 := congrArg BitVec.toNat hab
      simp only [s3TwoCall, BitVec.toNat_ofNat] at e1 e2
      have hA := s3_state_lt a
      have hB := s3_state_lt b
      apply BitVec.eq_of_toNat_eq
      omega)
  rwa [Finset.card_univ, s3_card_bitvec] at h

/-- At most `2^1344` states have a given digest. -/
theorem s3_trunc_fiber (d : BitVec 256) :
    (univ.filter fun s : S3State => s3TwoCall.trunc s = d).card ≤ 2 ^ 1344 := by
  have h := Finset.card_le_card_of_injOn (s := univ.filter fun s : S3State => s3TwoCall.trunc s = d)
    (t := (univ : Finset (BitVec 1344))) (fun s => BitVec.ofNat 1344 (s.toNat / 2 ^ 256))
    (by intro a _; simp) (by
      intro a ha b hb hab
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ha hb
      have e1 := congrArg BitVec.toNat (ha.trans hb.symm)
      have e2 := congrArg BitVec.toNat hab
      simp only [s3TwoCall, BitVec.toNat_ofNat] at e1 e2
      have hA := s3_state_lt a
      have hB := s3_state_lt b
      apply BitVec.eq_of_toNat_eq
      omega)
  rwa [Finset.card_univ, s3_card_bitvec] at h

/-! ### The union bound at these sizes -/

/-- Real-number core: with `N = a 2^256` states, `K ≤ 3a/2` bad answers per older entry and
`a 2^128` unary bad answers, `Q ≤ 2^128` queries of which `q` may be inverse. -/
theorem s3_union_core (a K Q q : ℝ) (ha : 1 ≤ a) (hK0 : 0 ≤ K) (hK : K ≤ 3 / 2 * a)
    (hQ0 : 0 ≤ Q) (hQ : Q ≤ 2 ^ 128) (hq0 : 0 ≤ q) :
    (Q * (Q - 1) / 2 * K + q * (a * 2 ^ 128)) / (a * 2 ^ 256 - Q) ≤
      Q ^ 2 / 2 ^ 256 + q / 2 ^ 127 := by
  have h128 : (2 : ℝ) ^ 128 ≤ 1 / 4 * 2 ^ 256 := by norm_num
  have hbig : (2 : ℝ) ^ 256 ≤ a * 2 ^ 256 := by nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) 256]
  have hD : 3 / 4 * (a * 2 ^ 256) ≤ a * 2 ^ 256 - Q := by linarith
  have hDpos : 0 < a * 2 ^ 256 - Q := by
    have : (0 : ℝ) < a * 2 ^ 256 := by positivity
    linarith
  rw [div_le_iff₀ hDpos]
  have h1 : Q * (Q - 1) / 2 * K ≤ 3 / 4 * a * Q ^ 2 := by
    have s1 : Q * (Q - 1) / 2 * K ≤ Q ^ 2 / 2 * K :=
      mul_le_mul_of_nonneg_right (by nlinarith) hK0
    have s2 : Q ^ 2 / 2 * K ≤ Q ^ 2 / 2 * (3 / 2 * a) :=
      mul_le_mul_of_nonneg_left hK (by positivity)
    linarith
  have h2 : (Q ^ 2 / 2 ^ 256 + q / 2 ^ 127) * (3 / 4 * (a * 2 ^ 256)) =
      3 / 4 * a * Q ^ 2 + 3 / 2 * (q * (a * 2 ^ 128)) := by
    field_simp
    ring
  have h3 : (Q ^ 2 / 2 ^ 256 + q / 2 ^ 127) * (3 / 4 * (a * 2 ^ 256)) ≤
      (Q ^ 2 / 2 ^ 256 + q / 2 ^ 127) * (a * 2 ^ 256 - Q) :=
    mul_le_mul_of_nonneg_left hD (by positivity)
  have h4 : (0 : ℝ) ≤ q * (a * 2 ^ 128) := by positivity
  linarith

/-- **The union bound at the stage-3 sizes.** `q` adversary queries (forward or inverse) and `e`
probed leaves (two forward queries each), with `q + 2 e ≤ 2^128`. -/
theorem s3_union_bound_le (q e : ℕ) (hsmall : q + 2 * e ≤ 2 ^ 128) :
    (((q + 2 * e : ℕ) : ℝ) * (((q + 2 * e : ℕ) : ℝ) - 1) / 2 *
        ((2 ^ 1344 + 2 * 2 ^ 768 + 2 ^ 768 : ℕ) : ℝ) + (q : ℝ) * ((2 ^ 1472 : ℕ) : ℝ)) /
      ((Fintype.card S3State : ℝ) - ((q + 2 * e : ℕ) : ℝ)) ≤
      ((q : ℝ) + 2 * e) ^ 2 / 2 ^ 256 + (q : ℝ) / 2 ^ 127 := by
  have hcore := s3_union_core ((2 : ℝ) ^ 1344) (((2 ^ 1344 + 2 * 2 ^ 768 + 2 ^ 768 : ℕ) : ℝ))
    ((q + 2 * e : ℕ) : ℝ) (q : ℝ) (one_le_pow₀ (by norm_num)) (Nat.cast_nonneg _)
    (by
      have : (2 ^ 1344 + 2 * 2 ^ 768 + 2 ^ 768 : ℕ) * 2 ≤ 3 * 2 ^ 1344 := by norm_num
      have h' : (((2 ^ 1344 + 2 * 2 ^ 768 + 2 ^ 768 : ℕ) * 2 : ℕ) : ℝ) ≤ ((3 * 2 ^ 1344 : ℕ) : ℝ) :=
        Nat.cast_le.2 this
      push_cast at h' ⊢
      linarith)
    (Nat.cast_nonneg _) (by exact_mod_cast hsmall) (Nat.cast_nonneg _)
  have hN : (Fintype.card S3State : ℝ) = (2 : ℝ) ^ 1344 * 2 ^ 256 := by
    rw [s3_card_state, ← pow_add]
    norm_num
  have hV : ((2 ^ 1472 : ℕ) : ℝ) = (2 : ℝ) ^ 1344 * 2 ^ 128 := by
    rw [← pow_add]
    norm_num
  rw [hN, hV]
  have hcast : ((q + 2 * e : ℕ) : ℝ) = (q : ℝ) + 2 * e := by push_cast; ring
  rw [hcast] at hcore ⊢
  exact hcore

end CommitGolfCandidate.Permutation
