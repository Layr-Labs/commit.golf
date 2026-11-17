import CommitGolfCandidate.S3Leaf
import CommitGolfCandidate.S3PermUnary
import Mathlib.Data.FinEnum

/-!
# The stage-3 byte layout as a two-call hash (hiding view), with its counts

`s3TwoCall` is the `TwoCall` instance on the 1600-bit state behind `s3First`, `s3Second` and
`s3LeafDigest` (S3Leaf.lean, pinned layout), used for hiding:

* first-call input `x1`: leaf bytes 0..200 (1600 bits), the whole first window;
* chaining value: bytes 112..200 of a reply (704 bits);
* second-call input: nonce (192 bits), chaining value, leaf bytes 168..256 (704 bits);
* digest: bytes 0..32 of a reply.

Hiding needs only that the nonce is a fresh field of the second window. The leaf bytes 168..200
that occur in both windows are part of `x1` and of the second message part; the generic hiding
adversary chooses the two parts freely, which covers the consistent pairs. The binding view of
the same layout, which uses the shared bytes, is `Permutation.s3PinCall` (S3LeafLayout.lean).
`s3_trunc_fiber` counts `2^1344` states per digest.
-/

set_option exponentiation.threshold 2100

namespace CommitGolfCandidate

open CommitGolf Permutation Finset

/-- The state of the ideal permutation. -/
abbrev S3State := BitVec PERMUTATION_WIDTH

theorem s3_card_bitvec (n : ℕ) : Fintype.card (BitVec n) = 2 ^ n := by
  rw [← FinEnum.card_eq_fintypeCard, FinEnum.card_bitVec]

theorem s3_card_state : Fintype.card S3State = 2 ^ 1600 := s3_card_bitvec _

theorem s3_state_lt (s : S3State) : s.toNat < 2 ^ 1600 := s.isLt

theorem s3_hide_entry_lt (value : Entry) : value.toNat < 2 ^ 2048 := value.isLt

/-- First-call input: the first window, leaf bytes 0..200. -/
def s3Enc1 (x : BitVec 1600) : S3State := BitVec.ofNat PERMUTATION_WIDTH x.toNat

/-- The chaining value: bytes 112..200 of a permutation reply. -/
def s3Chop (s : S3State) : BitVec 704 := BitVec.ofNat 704 (s.toNat / 2 ^ 896)

/-- Second-call input: nonce, chaining value, second message part (leaf bytes 168..256). -/
def s3Enc2 (p : BitVec 192 × BitVec 704 × BitVec 704) : S3State :=
  BitVec.ofNat PERMUTATION_WIDTH (p.1.toNat + p.2.1.toNat * 2 ^ 192 + p.2.2.toNat * 2 ^ 896)

/-- The digest: bytes 0..32 of a permutation reply. -/
def s3Trunc (s : S3State) : BitVec 256 := BitVec.ofNat 256 s.toNat

theorem s3Enc1_injective : Function.Injective s3Enc1 := by
  intro x y h
  have hx := x.isLt
  have hy := y.isLt
  have h' := congrArg BitVec.toNat h
  simp only [s3Enc1, PERMUTATION_WIDTH, BitVec.toNat_ofNat] at h'
  apply BitVec.eq_of_toNat_eq
  omega

theorem s3Enc2_injective : Function.Injective s3Enc2 := by
  rintro ⟨r, c, m⟩ ⟨r', c', m'⟩ h
  have hr := r.isLt
  have hc := c.isLt
  have hm := m.isLt
  have hr' := r'.isLt
  have hc' := c'.isLt
  have hm' := m'.isLt
  have h' := congrArg BitVec.toNat h
  simp only [s3Enc2, PERMUTATION_WIDTH, BitVec.toNat_ofNat] at h'
  have e1 : r.toNat = r'.toNat := by omega
  have e2 : c.toNat = c'.toNat := by omega
  have e3 : m.toNat = m'.toNat := by omega
  rw [BitVec.eq_of_toNat_eq e1, BitVec.eq_of_toNat_eq e2, BitVec.eq_of_toNat_eq e3]

/-- The stage-3 leaf hash as a two-call hash on the 1600-bit state. -/
def s3TwoCall : TwoCall S3State (BitVec 1600) (BitVec 192) (BitVec 704) (BitVec 704) (BitVec 256)
    where
  enc1 := s3Enc1
  enc1_inj := s3Enc1_injective
  chop := s3Chop
  enc2 := s3Enc2
  enc2_inj := s3Enc2_injective
  trunc := s3Trunc

/-- The two-call input of a leaf: leaf bytes 0..200, nonce, leaf bytes 168..256. The top 64 bits
of the salt are ignored. -/
def s3HideInput (salt : BitVec 256) (value : Entry) : BitVec 1600 × BitVec 192 × BitVec 704 :=
  (BitVec.ofNat 1600 value.toNat, BitVec.ofNat 192 salt.toNat,
    BitVec.ofNat 704 (value.toNat / 2 ^ 1344))

theorem s3First_eq (salt : BitVec 256) (value : Entry) :
    s3First value = s3Enc1 (s3HideInput salt value).1 := by
  simp only [s3First, s3Enc1, s3HideInput, BitVec.toNat_ofNat]

theorem s3Second_eq (salt : BitVec 256) (reply : S3State) (value : Entry) :
    s3Second salt reply value =
      s3Enc2 ((s3HideInput salt value).2.1, s3Chop reply, (s3HideInput salt value).2.2) := by
  have hreply := s3_state_lt reply
  have hvalue := s3_hide_entry_lt value
  have h1 : reply.toNat / 2 ^ 896 % 2 ^ 704 = reply.toNat / 2 ^ 896 :=
    Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul (by rw [← pow_add]; exact hreply))
  have h2 : value.toNat / 2 ^ 1344 % 2 ^ 704 = value.toNat / 2 ^ 1344 :=
    Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul (by rw [← pow_add]; exact hvalue))
  simp only [s3Second, s3Enc2, s3HideInput, s3Chop, BitVec.toNat_ofNat, h1, h2]

theorem s3LeafDigest_eq (permutation : Perm) (salt : BitVec 256) (value : Entry) :
    s3LeafDigest permutation salt value =
      s3Trunc (permutation (s3Enc2 ((s3HideInput salt value).2.1,
        s3Chop (permutation (s3Enc1 (s3HideInput salt value).1)), (s3HideInput salt value).2.2))) := by
  unfold s3LeafDigest
  rw [s3Second_eq, s3First_eq salt value]
  simp only [s3Trunc]

/-- Different leaf values give different two-call inputs, whatever the salts. -/
theorem s3Input_ne {salt salt' : BitVec 256} {value value' : Entry} (h : value ≠ value') :
    s3HideInput salt value ≠ s3HideInput salt' value' := by
  intro heq
  apply h
  have hvalue := s3_hide_entry_lt value
  have hvalue' := s3_hide_entry_lt value'
  have h1 := congrArg (fun p => p.1.toNat) heq
  have h2 := congrArg (fun p => p.2.2.toNat) heq
  simp only [s3HideInput, BitVec.toNat_ofNat] at h1 h2
  apply BitVec.eq_of_toNat_eq
  omega

/-! ### Counts -/

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
      simp only [s3TwoCall, s3Trunc, BitVec.toNat_ofNat] at e1 e2
      have hA := s3_state_lt a
      have hB := s3_state_lt b
      apply BitVec.eq_of_toNat_eq
      omega)
  rwa [Finset.card_univ, s3_card_bitvec] at h

end CommitGolfCandidate
