import CommitGolf.Parameters
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Byte-level codec between the checker's record layout and the delivered proof.

Unpacked layout, for `k` positions and `n = 15k + b` internal digests: record `r` sits at
`498r` with a 48-byte head (salt and leaf sibling) and fifteen 30-byte digests, and `b`
footer digests follow at `498k`. Internal digests keep 238 bits, so byte 29 of an honest
digest is below 64.

Packed layout: the same fields in the same order, each digest cut to its first 29 bytes,
followed by a remainder block that stores the six low bits of every digest's byte 29,
four digests per three bytes. -/
namespace CommitGolfCandidate.ProofCodec
open CommitGolf

def unpackedLength (k n : Nat) : Nat := 498*k + 30*(n - 15*k)
def bodyLength (k n : Nat) : Nat := 48*k + 29*n
def packedLength (k n : Nat) : Nat := bodyLength k n + 3*((n+3)/4)

/-- Unpacked start of digest `j`. -/
def unpackedDigest (k j : Nat) : Nat :=
  if j < 15*k then 498*(j/15) + 48 + 30*(j%15) else 498*k + 30*(j - 15*k)

/-- Unpacked index of packed body byte `p`. -/
def packedSource (k p : Nat) : Nat :=
  if p < 483*k then
    if p%483 < 48 then 498*(p/483) + p%483
    else 498*(p/483) + 48 + 30*((p%483 - 48)/29) + (p%483 - 48)%29
  else 498*k + 30*((p - 483*k)/29) + (p - 483*k)%29

/-- The six stored bits of digest `j` of an unpacked proof. -/
def remainderBits (P : Proof) (k j : Nat) : Nat := (P.getD (unpackedDigest k j + 29) 0).toNat % 64

/-- The 24-bit word holding the remainders of digests `4g .. 4g+3`. -/
def remainderWord (P : Proof) (k n g : Nat) : Nat :=
  ∑ m ∈ Finset.range 4, if 4*g + m < n then remainderBits P k (4*g + m) * 64^m else 0

def packedByte (P : Proof) (k n p : Nat) : Byte :=
  if p < bodyLength k n then P.getD (packedSource k p) 0
  else BitVec.ofNat 8 (remainderWord P k n ((p - bodyLength k n)/3) / 256^((p - bodyLength k n)%3))

/-- Digest count of an unpacked proof of length `L`. -/
def unpackedCount (k L : Nat) : Nat := (L - 48*k)/30

def pack (k : Nat) (P : Proof) : Proof :=
  let n := unpackedCount k P.length
  List.ofFn (fun p : Fin (packedLength k n) => packedByte P k n p.val)

/-- Digest count of a packed proof of length `L`. -/
def packedCount (k L : Nat) : Nat := 4*(L - 48*k)/119

/-- The packed 24-bit remainder word of group `g`. -/
def packedWord (Q : Proof) (k n g : Nat) : Nat :=
  let base := bodyLength k n + 3*g
  (Q.getD base 0).toNat + 256*(Q.getD (base+1) 0).toNat + 65536*(Q.getD (base+2) 0).toNat

def unpackedByte (Q : Proof) (k n i : Nat) : Byte :=
  let field := if i < 498*k then
      (if i%498 < 48 then (none, 483*(i/498) + i%498)
       else (some (15*(i/498) + (i%498 - 48)/30), 483*(i/498) + 48 + 29*((i%498 - 48)/30) + (i%498 - 48)%30))
    else (some (15*k + (i - 498*k)/30), 483*k + 29*((i - 498*k)/30) + (i - 498*k)%30)
  match field with
  | (some j, p) =>
    if (if i < 498*k then (i%498 - 48)%30 else (i - 498*k)%30) = 29 then
      BitVec.ofNat 8 (packedWord Q k n (j/4) / 64^(j%4) % 64)
    else Q.getD p 0
  | (none, p) => Q.getD p 0

/-- Packed proofs the checker accepts for unpacking. -/
def WellFormed (k L : Nat) : Prop :=
  L ≤ 2^33 ∧ 48*k ≤ L ∧ 15*k ≤ packedCount k L ∧ L = packedLength k (packedCount k L)

instance (k L : Nat) : Decidable (WellFormed k L) := by unfold WellFormed; infer_instance

def unpack (k : Nat) (Q : Proof) : Option Proof :=
  if WellFormed k Q.length then
    let n := packedCount k Q.length
    some (List.ofFn (fun i : Fin (unpackedLength k n) => unpackedByte Q k n i.val))
  else none

/-! ### Codec correctness -/
theorem pack_length (k : Nat) (P : Proof) :
    (pack k P).length = packedLength k (unpackedCount k P.length) := by
  simp [pack]

theorem packed_count_exact (k b : Nat) :
    packedCount k (packedLength k (15*k+b)) = 15*k+b := by
  unfold packedCount packedLength bodyLength
  omega

theorem packed_length_le (k b : Nat) (hk : k ≤ 128) (hb : b ≤ 128) :
    packedLength k (15*k+b) ≤ 67072 := by
  unfold packedLength bodyLength
  omega

theorem getD_pack (k : Nat) (P : Proof) (p : Nat)
    (hp : p < packedLength k (unpackedCount k P.length)) :
    (pack k P).getD p 0 = packedByte P k (unpackedCount k P.length) p := by
  simp [pack, List.getD_eq_getElem?_getD, hp]


theorem bytes24 (W : Nat) (h : W < 2^24) :
    W % 256 + 256 * (W / 256 % 256) + 65536 * (W / 65536 % 256) = W := by
  omega


theorem remainderWord_digits (P : Proof) (k n g m : Nat) (hm : m < 4) (hg : 4*g + m < n) :
    remainderWord P k n g < 2^24 ∧
    remainderWord P k n g / 64^m % 64 = remainderBits P k (4*g+m) := by
  have hb : ∀ j, remainderBits P k j < 64 := fun j => Nat.mod_lt _ (by decide)
  have key : remainderWord P k n g =
      (if 4*g+0 < n then remainderBits P k (4*g+0) else 0) +
      (if 4*g+1 < n then remainderBits P k (4*g+1) else 0) * 64 +
      (if 4*g+2 < n then remainderBits P k (4*g+2) else 0) * 4096 +
      (if 4*g+3 < n then remainderBits P k (4*g+3) else 0) * 262144 := by
    simp only [remainderWord, Finset.sum_range_succ, Finset.sum_range_zero]
    split_ifs <;> simp
  have hb' : ∀ m, (if 4*g+m < n then remainderBits P k (4*g+m) else 0) < 64 := by
    intro m; split_ifs <;> simp [hb]
  have b0 := hb' 0
  have b1 := hb' 1
  have b2 := hb' 2
  have b3 := hb' 3
  rw [key]
  generalize ha0 : (if 4*g+0 < n then remainderBits P k (4*g+0) else 0) = a0 at b0 ⊢
  generalize ha1 : (if 4*g+1 < n then remainderBits P k (4*g+1) else 0) = a1 at b1 ⊢
  generalize ha2 : (if 4*g+2 < n then remainderBits P k (4*g+2) else 0) = a2 at b2 ⊢
  generalize ha3 : (if 4*g+3 < n then remainderBits P k (4*g+3) else 0) = a3 at b3 ⊢
  refine ⟨by omega, ?_⟩
  rcases (show m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 by omega) with rfl | rfl | rfl | rfl
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hg)] at ha0; subst ha0; simp only [Nat.add_zero] at b0 ⊢; norm_num; omega
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hg)] at ha1; subst ha1; norm_num; omega
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hg)] at ha2; subst ha2; norm_num; omega
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hg)] at ha3; subst ha3; norm_num; omega

theorem packedWord_pack (k : Nat) (P : Proof) (j : Nat) (hj : j < unpackedCount k P.length) :
    packedWord (pack k P) k (unpackedCount k P.length) (j/4) =
      remainderWord P k (unpackedCount k P.length) (j/4) := by
  set n := unpackedCount k P.length with hn
  have hw := (remainderWord_digits P k n (j/4) (j%4) (Nat.mod_lt _ (by decide)) (by omega)).1
  unfold packedWord
  simp only
  rw [getD_pack k P _ (by unfold packedLength; rw [← hn]; omega), getD_pack k P _ (by unfold packedLength; rw [← hn]; omega),
    getD_pack k P _ (by unfold packedLength; rw [← hn]; omega)]
  simp only [packedByte, ← hn, show ¬ (bodyLength k n + 3*(j/4) < bodyLength k n) by omega,
    show ¬ (bodyLength k n + 3*(j/4) + 1 < bodyLength k n) by omega,
    show ¬ (bodyLength k n + 3*(j/4) + 2 < bodyLength k n) by omega,
    ↓reduceIte, BitVec.toNat_ofNat]
  have e0 : (bodyLength k n + 3*(j/4) - bodyLength k n) / 3 = j/4 := by omega
  have e1 : (bodyLength k n + 3*(j/4) + 1 - bodyLength k n) / 3 = j/4 := by omega
  have e2 : (bodyLength k n + 3*(j/4) + 2 - bodyLength k n) / 3 = j/4 := by omega
  have f0 : (bodyLength k n + 3*(j/4) - bodyLength k n) % 3 = 0 := by omega
  have f1 : (bodyLength k n + 3*(j/4) + 1 - bodyLength k n) % 3 = 1 := by omega
  have f2 : (bodyLength k n + 3*(j/4) + 2 - bodyLength k n) % 3 = 2 := by omega
  rw [e0, e1, e2, f0, f1, f2]
  norm_num
  omega

theorem byte29_pack (k : Nat) (P : Proof) (j : Nat) (hj : j < unpackedCount k P.length)
    (top : (P.getD (unpackedDigest k j + 29) 0).toNat < 64) :
    BitVec.ofNat 8 (packedWord (pack k P) k (unpackedCount k P.length) (j/4) / 64^(j%4) % 64) =
      P.getD (unpackedDigest k j + 29) 0 := by
  rw [packedWord_pack k P j hj]
  have h := (remainderWord_digits P k (unpackedCount k P.length) (j/4) (j%4)
    (Nat.mod_lt _ (by decide)) (by omega)).2
  rw [show 4*(j/4) + j%4 = j by omega] at h
  rw [h, remainderBits, Nat.mod_eq_of_lt top]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  omega


theorem unpack_pack (k b : Nat) (P : Proof) (len : P.length = 498*k + 30*b)
    (small : packedLength k (15*k+b) ≤ 2^33)
    (top : ∀ j < 15*k+b, (P.getD (unpackedDigest k j + 29) 0).toNat < 64) :
    unpack k (pack k P) = some P := by
  have hcount : unpackedCount k P.length = 15*k+b := by
    rw [len, unpackedCount]; omega
  have hQlen : (pack k P).length = packedLength k (15*k+b) := by rw [pack_length, hcount]
  have hpc := packed_count_exact k b
  have hwf : WellFormed k (pack k P).length := by
    rw [hQlen]
    refine ⟨small, ?_, ?_, ?_⟩
    · unfold packedLength bodyLength; omega
    · rw [hpc]; omega
    · rw [hpc]
  rw [unpack, ite_eq_left_of_eq_true _ _ (eq_true hwf), hQlen, hpc]
  simp only [Option.some.injEq]
  apply List.ext_getElem
  · simp [unpackedLength, len]
  intro i h1 h2
  rw [List.getElem_ofFn, show P[i] = P.getD i 0 by simp [List.getD_eq_getElem?_getD, h2]]
  have hi : i < 498*k + 30*b := len ▸ h2
  have hQ : ∀ p < bodyLength k (15*k+b), (pack k P).getD p 0 = P.getD (packedSource k p) 0 := by
    intro p hp
    rw [getD_pack k P p (by rw [hcount]; unfold packedLength; omega), hcount, packedByte,
      ite_eq_left_of_eq_true _ _ (eq_true hp)]
  have h29 : ∀ j < 15*k+b, BitVec.ofNat 8
      (packedWord (pack k P) k (15*k+b) (j/4) / 64^(j%4) % 64) = P.getD (unpackedDigest k j + 29) 0 := by
    intro j hj
    rw [← hcount]
    exact byte29_pack k P j (by omega) (top j hj)
  unfold unpackedByte
  by_cases hA : i < 498*k
  · by_cases hB : i%498 < 48
    · simp only [hA, hB, ↓reduceIte]
      rw [hQ _ (by unfold bodyLength; omega)]
      unfold packedSource
      rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega)), ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
      congr 1; omega
    · by_cases hC : (i%498 - 48)%30 = 29
      · simp only [hA, hB, hC, ↓reduceIte]
        rw [h29 _ (by omega)]
        unfold unpackedDigest
        rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
        congr 1; omega
      · simp only [hA, hB, hC, ↓reduceIte]
        rw [hQ _ (by unfold bodyLength; omega)]
        have hd : (i%498 - 48)/30 < 15 := by omega
        have hc : (i%498 - 48)%30 < 29 := by omega
        have hr : i/498 < k := by omega
        have hi' : i = 498*(i/498) + 48 + 30*((i%498 - 48)/30) + (i%498 - 48)%30 := by omega
        generalize i/498 = r at hr hi' ⊢
        generalize (i%498 - 48)/30 = d at hd hi' ⊢
        generalize (i%498 - 48)%30 = c at hc hi' ⊢
        subst hi'
        have e1 : (483*r + 48 + 29*d + c) % 483 = 48 + 29*d + c := by omega
        have e2 : (483*r + 48 + 29*d + c) / 483 = r := by omega
        have e3 : (48 + 29*d + c - 48) / 29 = d := by omega
        have e4 : (48 + 29*d + c - 48) % 29 = c := by omega
        unfold packedSource
        rw [e1, e2, e3, e4, ite_eq_left_of_eq_true _ _ (eq_true (by omega)),
          ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
  · by_cases hC : (i - 498*k)%30 = 29
    · simp only [hA, hC, ↓reduceIte]
      rw [h29 _ (by omega)]
      unfold unpackedDigest
      rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
      congr 1; omega
    · simp only [hA, hC, ↓reduceIte]
      rw [hQ _ (by unfold bodyLength; omega)]
      unfold packedSource
      rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
      congr 1; omega

end CommitGolfCandidate.ProofCodec
