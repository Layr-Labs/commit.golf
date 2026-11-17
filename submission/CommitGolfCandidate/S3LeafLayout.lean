import CommitGolfCandidate.S3Overlap
import Mathlib.Data.FinEnum

/-!
# The stage-3 byte layout as a two-call hash with an overlap, with its counts

`s3TwoCall` is the `TwoCall` instance on the 1600-bit state behind `s3First`, `s3Second` and
`s3LeafDigest` (S3Leaf.lean; the link is proved in S3LeafBinding.lean):

* first-call input `x1`: leaf bytes 0..200, the whole state (no fixed prefix);
* chaining value: bytes 120..176 of a reply (448 bits);
* second-call input: chaining value, nonce (192 bits), leaf bytes 136..256 (960 bits);
* digest: bytes 0..32 of a reply;
* overlap: leaf bytes 136..200 (512 bits), the top of the first window (`s3OvA`) and the bottom
  of the second message part (`s3OvM`).

Counts: `2^1152` states per chaining value, `2^1152` second-call inputs per chaining slot,
`2^1344` states per digest, `2^1088` first-call inputs per overlap. `s3_union_bound_le` reads the
union bound at these sizes: for `q` adversary queries and `e` probed leaves with
`q + 2 e ≤ 2^128`, it is at most `(q + 2 e)^2 / 2^256 + q / 2^127` (the second term is slack kept
for the callers; the lone bad event costs `2^-448` per query here). This file needs Mathlib only.
-/

set_option exponentiation.threshold 2100

namespace CommitGolfCandidate.Permutation

open Finset

/-- The state of the ideal permutation. -/
abbrev S3State := BitVec 1600

/-- Input of the two-call leaf hash: first window, nonce, second message part. -/
abbrev S3LeafInput := BitVec 1600 × BitVec 192 × BitVec 960

theorem s3_card_bitvec (n : ℕ) : Fintype.card (BitVec n) = 2 ^ n := by
  rw [← FinEnum.card_eq_fintypeCard, FinEnum.card_bitVec]

theorem s3_card_state : Fintype.card S3State = 2 ^ 1600 := s3_card_bitvec _

theorem s3_state_lt (s : S3State) : s.toNat < 2 ^ 1600 := s.isLt

theorem s3_enc2_injective :
    Function.Injective fun i : BitVec 192 × BitVec 448 × BitVec 960 =>
      (BitVec.ofNat 1600 (i.2.1.toNat + i.1.toNat * 2 ^ 448 + i.2.2.toNat * 2 ^ 640) : S3State) := by
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
`(first window, nonce, second message part)`; the second call encodes
`(chaining value, nonce, second message part)` in that byte order. -/
def s3TwoCall : TwoCall S3State (BitVec 1600) (BitVec 192) (BitVec 448) (BitVec 960) (BitVec 256)
    where
  enc1 x := x
  chop o := BitVec.ofNat 448 (o.toNat / 2 ^ 960)
  enc2 i := BitVec.ofNat 1600 (i.2.1.toNat + i.1.toNat * 2 ^ 448 + i.2.2.toNat * 2 ^ 640)
  trunc o := BitVec.ofNat 256 o.toNat
  enc1_inj := fun _ _ h => h
  enc2_inj := s3_enc2_injective

/-- Leaf bytes 136..200 as they sit in the first window. -/
def s3OvA (x : BitVec 1600) : BitVec 512 := BitVec.ofNat 512 (x.toNat / 2 ^ 1088)

/-- Leaf bytes 136..200 as they sit in the second message part. -/
def s3OvM (m : BitVec 960) : BitVec 512 := BitVec.ofNat 512 m.toNat

/-! ### Counts -/

theorem s3_second_inputs : Fintype.card (BitVec 192) * Fintype.card (BitVec 960) ≤ 2 ^ 1152 := by
  rw [s3_card_bitvec, s3_card_bitvec, ← pow_add]

/-- At most `2^1152` states have a given chaining value. -/
theorem s3_chop_fiber (c : BitVec 448) :
    (univ.filter fun s : S3State => s3TwoCall.chop s = c).card ≤ 2 ^ 1152 := by
  have h := Finset.card_le_card_of_injOn (s := univ.filter fun s : S3State => s3TwoCall.chop s = c)
    (t := (univ : Finset (BitVec 1152)))
    (fun s => BitVec.ofNat 1152 (s.toNat % 2 ^ 960 + s.toNat / 2 ^ 1408 * 2 ^ 960))
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

/-- At most `2^1088` first windows have a given overlap. -/
theorem s3_overlap_fiber (o : BitVec 512) :
    (univ.filter fun x : BitVec 1600 => s3OvA x = o).card ≤ 2 ^ 1088 := by
  have h := Finset.card_le_card_of_injOn (s := univ.filter fun x : BitVec 1600 => s3OvA x = o)
    (t := (univ : Finset (BitVec 1088))) (fun x => BitVec.ofNat 1088 x.toNat)
    (by intro a _; simp) (by
      intro a ha b hb hab
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ha hb
      have e1 := congrArg BitVec.toNat (ha.trans hb.symm)
      have e2 := congrArg BitVec.toNat hab
      simp only [s3OvA, BitVec.toNat_ofNat] at e1 e2
      have hA := s3_state_lt a
      have hB := s3_state_lt b
      apply BitVec.eq_of_toNat_eq
      omega)
  rwa [Finset.card_univ, s3_card_bitvec] at h

/-! ### The union bound at these sizes -/

/-- Real-number core: with `N = a 2^256` states, `K ≤ 3a/2` bad answers per older entry and
`u ≤ K/2` bad answers of a query by itself, `Q ≤ 2^128` queries. The lone events are paid by the
`Q (Q - 1)` against `Q^2` slack; `q / 2^127` is not needed and is kept for the callers. -/
theorem s3_union_core (a K u Q q : ℝ) (ha : 1 ≤ a) (hK : K ≤ 3 / 2 * a) (hu : u ≤ K / 2)
    (hQ0 : 0 ≤ Q) (hQ : Q ≤ 2 ^ 128) (hq0 : 0 ≤ q) :
    (Q * (Q - 1) / 2 * K + Q * u) / (a * 2 ^ 256 - Q) ≤ Q ^ 2 / 2 ^ 256 + q / 2 ^ 127 := by
  have h128 : (2 : ℝ) ^ 128 ≤ 1 / 4 * 2 ^ 256 := by norm_num
  have hbig : (2 : ℝ) ^ 256 ≤ a * 2 ^ 256 := by nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) 256]
  have hD : 3 / 4 * (a * 2 ^ 256) ≤ a * 2 ^ 256 - Q := by linarith
  have hDpos : 0 < a * 2 ^ 256 - Q := by
    have : (0 : ℝ) < a * 2 ^ 256 := by positivity
    linarith
  rw [div_le_iff₀ hDpos]
  have h1 : Q * (Q - 1) / 2 * K + Q * u ≤ 3 / 4 * a * Q ^ 2 := by
    have s0 : Q * u ≤ Q * (K / 2) := mul_le_mul_of_nonneg_left hu hQ0
    have s1 : Q * (Q - 1) / 2 * K + Q * (K / 2) = Q ^ 2 / 2 * K := by ring
    have s2 : Q ^ 2 / 2 * K ≤ Q ^ 2 / 2 * (3 / 2 * a) :=
      mul_le_mul_of_nonneg_left hK (by positivity)
    linarith
  have h2 : Q ^ 2 / 2 ^ 256 * (3 / 4 * (a * 2 ^ 256)) = 3 / 4 * a * Q ^ 2 := by
    have h256 : (2 : ℝ) ^ 256 ≠ 0 := by positivity
    field_simp
  have h3 : (Q ^ 2 / 2 ^ 256 + q / 2 ^ 127) * (3 / 4 * (a * 2 ^ 256)) ≤
      (Q ^ 2 / 2 ^ 256 + q / 2 ^ 127) * (a * 2 ^ 256 - Q) :=
    mul_le_mul_of_nonneg_left hD (by positivity)
  have h4 : (0 : ℝ) ≤ q / 2 ^ 127 * (3 / 4 * (a * 2 ^ 256)) := by positivity
  have h5 : (Q ^ 2 / 2 ^ 256 + q / 2 ^ 127) * (3 / 4 * (a * 2 ^ 256)) =
      3 / 4 * a * Q ^ 2 + q / 2 ^ 127 * (3 / 4 * (a * 2 ^ 256)) := by rw [add_mul, h2]
  linarith

/-- **The union bound at the stage-3 sizes.** `q` adversary queries (forward or inverse) and `e`
probed leaves (two forward queries each), with `q + 2 e ≤ 2^128`. -/
theorem s3_union_bound_le (q e : ℕ) (hsmall : q + 2 * e ≤ 2 ^ 128) :
    unionBound (Fintype.card S3State) (2 ^ 1344 + 2 * 2 ^ 1152 + 2 ^ 1152 + 2 * 2 ^ 1088)
        (2 ^ 1152) (q + 2 * e) ≤
      ((q : ℝ) + 2 * e) ^ 2 / 2 ^ 256 + (q : ℝ) / 2 ^ 127 := by
  unfold unionBound
  have hcore := s3_union_core ((2 : ℝ) ^ 1344)
    (((2 ^ 1344 + 2 * 2 ^ 1152 + 2 ^ 1152 + 2 * 2 ^ 1088 : ℕ) : ℝ)) (((2 ^ 1152 : ℕ) : ℝ))
    ((q + 2 * e : ℕ) : ℝ) (q : ℝ) (one_le_pow₀ (by norm_num))
    (by
      have : (2 ^ 1344 + 2 * 2 ^ 1152 + 2 ^ 1152 + 2 * 2 ^ 1088 : ℕ) * 2 ≤ 3 * 2 ^ 1344 := by
        norm_num
      have h' : (((2 ^ 1344 + 2 * 2 ^ 1152 + 2 ^ 1152 + 2 * 2 ^ 1088 : ℕ) * 2 : ℕ) : ℝ) ≤
          ((3 * 2 ^ 1344 : ℕ) : ℝ) := Nat.cast_le.2 this
      push_cast at h' ⊢
      linarith)
    (by
      have : (2 ^ 1152 : ℕ) * 2 ≤ 2 ^ 1344 + 2 * 2 ^ 1152 + 2 ^ 1152 + 2 * 2 ^ 1088 := by
        norm_num
      have h' : (((2 ^ 1152 : ℕ) * 2 : ℕ) : ℝ) ≤
          ((2 ^ 1344 + 2 * 2 ^ 1152 + 2 ^ 1152 + 2 * 2 ^ 1088 : ℕ) : ℝ) := Nat.cast_le.2 this
      push_cast at h' ⊢
      linarith)
    (Nat.cast_nonneg _) (by exact_mod_cast hsmall) (Nat.cast_nonneg _)
  have hN : (Fintype.card S3State : ℝ) = (2 : ℝ) ^ 1344 * 2 ^ 256 := by
    rw [s3_card_state, ← pow_add]
    norm_num
  rw [hN]
  have hcast : ((q + 2 * e : ℕ) : ℝ) = (q : ℝ) + 2 * e := by push_cast; ring
  rw [hcast] at hcore ⊢
  exact hcore

end CommitGolfCandidate.Permutation
