import CommitGolfCandidate.S4PermOverlap
import Mathlib.Data.FinEnum

/-!
# The leaf layout as a two-call hash with an overlap, with its counts

`s3TwoCall` is the `TwoCall` instance on the 1600-bit state behind `s3First`, `s3Second` and
`s3LeafDigest` (S3Leaf.lean; the link is proved in S3LeafBinding.lean):

* first-call input `x1`: the whole 200-byte window (nonce, tag, leaf bytes 0..176);
* chaining value: bytes 136..200 of a reply (512 bits);
* second-call input: chaining value, leaf bytes 120..256 (1088 bits); the salt enters the first
  call only, so the second call has no salt part (`Unit`);
* digest: bytes 0..32 of a reply.

`s3Overlap` reads the repeated field, leaf bytes 120..176: bytes 144..200 of a first-call input
(`ovA`) and bytes 64..120 of a second-call input (`ovB`).

Counts: `2^1088` states per chaining value, `2^1088` second-call inputs per chaining slot,
`2^1344` states per digest, `2^1152` states per overlap field. `s3_union_bound_le` reads the union
bound at these sizes: for `q` adversary queries and `e` probed leaves with `q + 2 e ≤ 2^128`, it is
at most `(q + 2 e)^2 / 2^256`. Every digest has exactly `2^1344` preimages (`s3_trunc_exact`).
-/

set_option exponentiation.threshold 2100

namespace CommitGolfCandidate.Permutation

open Finset

/-- The state of the ideal permutation. -/
abbrev S3State := BitVec 1600

/-- Input of the two-call leaf hash: first-call input, no salt in the second call, second message
part. -/
abbrev S3LeafInput := BitVec 1600 × Unit × BitVec 1088

theorem s3_card_bitvec (n : ℕ) : Fintype.card (BitVec n) = 2 ^ n := by
  rw [← FinEnum.card_eq_fintypeCard, FinEnum.card_bitVec]

theorem s3_card_state : Fintype.card S3State = 2 ^ 1600 := s3_card_bitvec _

theorem s3_state_lt (s : S3State) : s.toNat < 2 ^ 1600 := s.isLt

theorem s3_enc2_injective :
    Function.Injective fun i : Unit × BitVec 512 × BitVec 1088 =>
      (BitVec.ofNat 1600 (i.2.1.toNat + i.2.2.toNat * 2 ^ 512) : S3State) := by
  rintro ⟨⟨⟩, c, m⟩ ⟨⟨⟩, c', m'⟩ h
  have hc := c.isLt
  have hm := m.isLt
  have hc' := c'.isLt
  have hm' := m'.isLt
  have h' := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at h'
  have e2 : c.toNat = c'.toNat := by omega
  have e3 : m.toNat = m'.toNat := by omega
  rw [BitVec.eq_of_toNat_eq e2, BitVec.eq_of_toNat_eq e3]

/-- The leaf hash as a two-call hash on the 1600-bit state. A leaf input is
`(first-call input, (), second message part)`; the second call encodes
`(chaining value, second message part)`. -/
def s3TwoCall : TwoCall S3State (BitVec 1600) Unit (BitVec 512) (BitVec 1088) (BitVec 256) where
  enc1 x := x
  chop o := BitVec.ofNat 512 (o.toNat / 2 ^ 1088)
  enc2 i := BitVec.ofNat 1600 (i.2.1.toNat + i.2.2.toNat * 2 ^ 512)
  trunc o := BitVec.ofNat 256 o.toNat
  enc1_inj := fun _ _ h => h
  enc2_inj := s3_enc2_injective

/-- The repeated field, leaf bytes 120..176: bytes 144..200 of a first-call input, bytes 64..120
of a second-call input. -/
def s3Overlap : Overlap s3TwoCall (BitVec 448) where
  ovA s := BitVec.ofNat 448 (s.toNat / 2 ^ 1152)
  ovB s := BitVec.ofNat 448 (s.toNat / 2 ^ 512)

/-! ### Counts -/

theorem s3_second_inputs : Fintype.card Unit * Fintype.card (BitVec 1088) ≤ 2 ^ 1088 := by
  rw [Fintype.card_unit, s3_card_bitvec, one_mul]

/-- At most `2^1088` states have a given chaining value. -/
theorem s3_chop_fiber (c : BitVec 512) :
    (univ.filter fun s : S3State => s3TwoCall.chop s = c).card ≤ 2 ^ 1088 := by
  have h := Finset.card_le_card_of_injOn (s := univ.filter fun s : S3State => s3TwoCall.chop s = c)
    (t := (univ : Finset (BitVec 1088))) (fun s => BitVec.ofNat 1088 s.toNat)
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

/-- At most `2^1152` states have a given overlap field (first-call position). -/
theorem s3_overlap_fiber (o : BitVec 448) :
    (univ.filter fun s : S3State => s3Overlap.ovA s = o).card ≤ 2 ^ 1152 := by
  have h := Finset.card_le_card_of_injOn (s := univ.filter fun s : S3State => s3Overlap.ovA s = o)
    (t := (univ : Finset (BitVec 1152))) (fun s => BitVec.ofNat 1152 s.toNat)
    (by intro a _; simp) (by
      intro a ha b hb hab
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ha hb
      have e1 := congrArg BitVec.toNat (ha.trans hb.symm)
      have e2 := congrArg BitVec.toNat hab
      simp only [s3Overlap, BitVec.toNat_ofNat] at e1 e2
      have hA := s3_state_lt a
      have hB := s3_state_lt b
      apply BitVec.eq_of_toNat_eq
      omega)
  rwa [Finset.card_univ, s3_card_bitvec] at h

/-! ### The union bound at these sizes -/

/-- Real-number core: with `N = a 2^256` states, `K ≤ 3a/2` bad answers per older entry,
`u ≤ a/8` bad answers of a single entry and `Q ≤ 2^128` queries, the union bound is at most
`Q^2 / 2^256`. -/
theorem s3_union_core (a K u Q : ℝ) (ha : 1 ≤ a) (hK0 : 0 ≤ K) (hK : K ≤ 3 / 2 * a)
    (hu : u ≤ a / 8) (hQ0 : 0 ≤ Q) (hQ : Q ≤ 2 ^ 128) (hQQ : Q ≤ Q ^ 2) :
    (Q * (Q - 1) / 2 * K + Q * u) / (a * 2 ^ 256 - Q) ≤ Q ^ 2 / 2 ^ 256 := by
  have h128 : (2 : ℝ) ^ 128 ≤ 1 / 8 * 2 ^ 256 := by norm_num
  have hbig : (2 : ℝ) ^ 256 ≤ a * 2 ^ 256 := by nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) 256]
  have hD : 7 / 8 * (a * 2 ^ 256) ≤ a * 2 ^ 256 - Q := by linarith
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
  have h1' : Q * u ≤ 1 / 8 * a * Q ^ 2 := by
    have s1 : Q * u ≤ Q * (a / 8) := mul_le_mul_of_nonneg_left hu hQ0
    have s2 : Q * (a / 8) ≤ Q ^ 2 * (a / 8) :=
      mul_le_mul_of_nonneg_right hQQ (by linarith)
    linarith
  have h2 : Q ^ 2 / 2 ^ 256 * (7 / 8 * (a * 2 ^ 256)) = 7 / 8 * a * Q ^ 2 := by
    rw [div_mul_eq_mul_div, div_eq_iff (by positivity)]
    ring
  have h3 : Q ^ 2 / 2 ^ 256 * (7 / 8 * (a * 2 ^ 256)) ≤ Q ^ 2 / 2 ^ 256 * (a * 2 ^ 256 - Q) :=
    mul_le_mul_of_nonneg_left hD (by positivity)
  linarith

/-- **The union bound at the leaf sizes.** `q` adversary queries (forward or inverse) and `e`
probed leaves (two forward queries each), with `q + 2 e ≤ 2^128`. -/
theorem s3_union_bound_le (q e : ℕ) (hsmall : q + 2 * e ≤ 2 ^ 128) :
    unionBound (Fintype.card S3State) (2 ^ 1344 + 2 * 2 ^ 1088 + 2 ^ 1088 + 2 * 2 ^ 1152) (2 ^ 1088)
        (q + 2 * e) ≤
      ((q : ℝ) + 2 * e) ^ 2 / 2 ^ 256 := by
  have hcore := s3_union_core ((2 : ℝ) ^ 1344)
    (((2 ^ 1344 + 2 * 2 ^ 1088 + 2 ^ 1088 + 2 * 2 ^ 1152 : ℕ) : ℝ)) (((2 ^ 1088 : ℕ) : ℝ))
    ((q + 2 * e : ℕ) : ℝ) (one_le_pow₀ (by norm_num)) (Nat.cast_nonneg _)
    (by
      have : (2 ^ 1344 + 2 * 2 ^ 1088 + 2 ^ 1088 + 2 * 2 ^ 1152 : ℕ) * 2 ≤ 3 * 2 ^ 1344 := by
        norm_num
      have h' : (((2 ^ 1344 + 2 * 2 ^ 1088 + 2 ^ 1088 + 2 * 2 ^ 1152 : ℕ) * 2 : ℕ) : ℝ) ≤
          ((3 * 2 ^ 1344 : ℕ) : ℝ) :=
        Nat.cast_le.2 this
      push_cast at h' ⊢
      linarith)
    (by
      have : (2 ^ 1088 : ℕ) * 8 ≤ 2 ^ 1344 := by norm_num
      have h' : (((2 ^ 1088 : ℕ) * 8 : ℕ) : ℝ) ≤ ((2 ^ 1344 : ℕ) : ℝ) := Nat.cast_le.2 this
      push_cast at h' ⊢
      linarith)
    (Nat.cast_nonneg _) (by exact_mod_cast hsmall)
    (by
      have : (q + 2 * e : ℕ) ≤ (q + 2 * e) ^ 2 := by nlinarith
      exact_mod_cast this)
  have hN : (Fintype.card S3State : ℝ) = (2 : ℝ) ^ 1344 * 2 ^ 256 := by
    rw [s3_card_state, ← pow_add]
    norm_num
  have hcast : ((q + 2 * e : ℕ) : ℝ) = (q : ℝ) + 2 * e := by push_cast; ring
  unfold unionBound
  rw [hN]
  rw [hcast] at hcore ⊢
  exact hcore

/-- Every digest has exactly `2^1344` preimages among the 1600-bit states. -/
theorem s3_trunc_exact (d : BitVec 256) :
    (univ.filter fun s : S3State => s3TwoCall.trunc s = d).card = 2 ^ 1344 := by
  by_contra h
  have hlt : (univ.filter fun s : S3State => s3TwoCall.trunc s = d).card < 2 ^ 1344 :=
    lt_of_le_of_ne (s3_trunc_fiber d) h
  have hsum : (univ : Finset S3State).card =
      ∑ b ∈ (univ : Finset (BitVec 256)),
        (univ.filter fun s : S3State => s3TwoCall.trunc s = b).card :=
    Finset.card_eq_sum_card_fiberwise (by intro x _; simp)
  have hlt2 : ∑ b ∈ (univ : Finset (BitVec 256)),
        (univ.filter fun s : S3State => s3TwoCall.trunc s = b).card <
      ∑ _b ∈ (univ : Finset (BitVec 256)), 2 ^ 1344 :=
    Finset.sum_lt_sum (fun b _ => s3_trunc_fiber b) ⟨d, Finset.mem_univ _, hlt⟩
  rw [← hsum, Finset.card_univ, s3_card_state, Finset.sum_const, Finset.card_univ,
    s3_card_bitvec, smul_eq_mul, ← pow_add] at hlt2
  exact absurd hlt2 (lt_irrefl _)

end CommitGolfCandidate.Permutation
