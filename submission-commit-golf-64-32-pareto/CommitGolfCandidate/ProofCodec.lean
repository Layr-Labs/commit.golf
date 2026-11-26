import CommitGolf.Parameters
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Byte-level codec between the checker's record layout and the delivered proof (version 2).

Unpacked layout, for `k` positions and `n = 15k + b` internal digests: record `r` sits at
`498r` with a 48-byte head (salt bytes 0-15, leaf-sibling bytes 16-47) and fifteen 30-byte
digests, and `b` footer digests follow at `498k`. Internal digests keep 238 bits, so byte 29
of an honest digest is below 64. Honest salts keep 122 bits (head byte 15 below 4) and honest
leaf siblings 244 bits (head byte 46 below 32, head byte 47 zero).

Packed layout: record `r` at `481r` holds head bytes 0-14, head bytes 16-45, one combined
byte `(head[15] & 3) | ((head[46] & 31) << 2)`, then its fifteen digests cut to their first
29 bytes; the footer digests follow, also cut to 29 bytes, then a remainder block that stores
the six low bits of every digest's byte 29, four digests per three bytes. -/
namespace CommitGolfCandidate.ProofCodec
open CommitGolf

def unpackedLength (k n : Nat) : Nat := 498*k + 30*(n - 15*k)
def bodyLength (k n : Nat) : Nat := 46*k + 29*n
def packedLength (k n : Nat) : Nat := bodyLength k n + 3*((n+3)/4)

/-- Unpacked start of digest `j`. -/
def unpackedDigest (k j : Nat) : Nat :=
  if j < 15*k then 498*(j/15) + 48 + 30*(j%15) else 498*k + 30*(j - 15*k)

/-- Unpacked index of packed body byte `p`. The combined head byte (record offset 45) is
mapped to the salt byte 15 it partly stores; `packedByte` treats it separately. -/
def packedSource (k p : Nat) : Nat :=
  if p < 481*k then
    if p%481 < 15 then 498*(p/481) + p%481
    else if p%481 < 45 then 498*(p/481) + p%481 + 1
    else if p%481 = 45 then 498*(p/481) + 15
    else 498*(p/481) + 48 + 30*((p%481 - 46)/29) + (p%481 - 46)%29
  else 498*k + 30*((p - 481*k)/29) + (p - 481*k)%29

/-- The combined head byte of record `r`: the two low bits of salt byte 15 and the five
low bits of leaf-sibling byte 30 (head byte 46). -/
def headByte (P : Proof) (r : Nat) : Byte :=
  BitVec.ofNat 8 ((P.getD (498*r+15) 0).toNat % 4 + 4*((P.getD (498*r+46) 0).toNat % 32))

/-- The six stored bits of digest `j` of an unpacked proof. -/
def remainderBits (P : Proof) (k j : Nat) : Nat := (P.getD (unpackedDigest k j + 29) 0).toNat % 64

/-- The 24-bit word holding the remainders of digests `4g .. 4g+3`. -/
def remainderWord (P : Proof) (k n g : Nat) : Nat :=
  ∑ m ∈ Finset.range 4, if 4*g + m < n then remainderBits P k (4*g + m) * 64^m else 0

def packedByte (P : Proof) (k n p : Nat) : Byte :=
  if p < bodyLength k n then
    (if p < 481*k ∧ p%481 = 45 then headByte P (p/481) else P.getD (packedSource k p) 0)
  else BitVec.ofNat 8 (remainderWord P k n ((p - bodyLength k n)/3) / 256^((p - bodyLength k n)%3))

/-- Digest count of an unpacked proof of length `L`. -/
def unpackedCount (k L : Nat) : Nat := (L - 48*k)/30

def pack (k : Nat) (P : Proof) : Proof :=
  let n := unpackedCount k P.length
  List.ofFn (fun p : Fin (packedLength k n) => packedByte P k n p.val)

/-- Digest count of a packed proof of length `L`. -/
def packedCount (k L : Nat) : Nat := 4*(L - 46*k)/119

/-- The packed 24-bit remainder word of group `g`. -/
def packedWord (Q : Proof) (k n g : Nat) : Nat :=
  let base := bodyLength k n + 3*g
  (Q.getD base 0).toNat + 256*(Q.getD (base+1) 0).toNat + 65536*(Q.getD (base+2) 0).toNat

/-- Byte 29 of digest `j`, restored from the packed remainder block. -/
def remByte (Q : Proof) (k n j : Nat) : Byte := BitVec.ofNat 8 (packedWord Q k n (j/4) / 64^(j%4) % 64)

def unpackedByte (Q : Proof) (k n i : Nat) : Byte :=
  if i < 498*k then
    if i%498 < 15 then Q.getD (481*(i/498) + i%498) 0
    else if i%498 = 15 then BitVec.ofNat 8 ((Q.getD (481*(i/498) + 45) 0).toNat % 4)
    else if i%498 < 46 then Q.getD (481*(i/498) + i%498 - 1) 0
    else if i%498 = 46 then BitVec.ofNat 8 ((Q.getD (481*(i/498) + 45) 0).toNat / 4)
    else if i%498 < 48 then 0
    else if (i%498 - 48)%30 = 29 then remByte Q k n (15*(i/498) + (i%498 - 48)/30)
    else Q.getD (481*(i/498) + 46 + 29*((i%498 - 48)/30) + (i%498 - 48)%30) 0
  else if (i - 498*k)%30 = 29 then remByte Q k n (15*k + (i - 498*k)/30)
  else Q.getD (481*k + 29*((i - 498*k)/30) + (i - 498*k)%30) 0

/-- Packed proofs the checker accepts for unpacking. -/
def WellFormed (k L : Nat) : Prop :=
  L ≤ 2^33 ∧ 46*k ≤ L ∧ 15*k ≤ packedCount k L ∧ L = packedLength k (packedCount k L)

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
    packedLength k (15*k+b) ≤ 66816 := by
  unfold packedLength bodyLength
  have : (15*k+b+3)/4 ≤ 512 := by omega
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
    remByte (pack k P) k (unpackedCount k P.length) j =
      P.getD (unpackedDigest k j + 29) 0 := by
  rw [remByte, packedWord_pack k P j hj]
  have h := (remainderWord_digits P k (unpackedCount k P.length) (j/4) (j%4)
    (Nat.mod_lt _ (by decide)) (by omega)).2
  rw [show 4*(j/4) + j%4 = j by omega] at h
  rw [h, remainderBits, Nat.mod_eq_of_lt top]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  omega


theorem headByte_toNat (P : Proof) (r : Nat) :
    (headByte P r).toNat = (P.getD (498*r+15) 0).toNat % 4 + 4*((P.getD (498*r+46) 0).toNat % 32) := by
  unfold headByte
  rw [BitVec.toNat_ofNat]
  omega

theorem unpack_pack (k b : Nat) (P : Proof) (len : P.length = 498*k + 30*b)
    (small : packedLength k (15*k+b) ≤ 2^33)
    (top : ∀ j < 15*k+b, (P.getD (unpackedDigest k j + 29) 0).toNat < 64)
    (salt : ∀ r < k, (P.getD (498*r+15) 0).toNat < 4)
    (leaf : ∀ r < k, (P.getD (498*r+46) 0).toNat < 32)
    (leafTop : ∀ r < k, P.getD (498*r+47) 0 = 0) :
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
  have hQ : ∀ p < bodyLength k (15*k+b), ¬ (p < 481*k ∧ p%481 = 45) →
      (pack k P).getD p 0 = P.getD (packedSource k p) 0 := by
    intro p hp hh
    rw [getD_pack k P p (by rw [hcount]; unfold packedLength; omega), hcount, packedByte,
      if_pos hp, if_neg hh]
  have hH : ∀ r < k, (pack k P).getD (481*r + 45) 0 = headByte P r := by
    intro r hr
    rw [getD_pack k P _ (by rw [hcount]; unfold packedLength bodyLength; omega), hcount, packedByte,
      if_pos (by unfold bodyLength; omega), if_pos (by omega), show (481*r+45)/481 = r by omega]
  have h29 : ∀ j < 15*k+b, remByte (pack k P) k (15*k+b) j = P.getD (unpackedDigest k j + 29) 0 := by
    intro j hj
    rw [← hcount]
    exact byte29_pack k P j (by omega) (top j hj)
  change unpackedByte (pack k P) k (15*k+b) i = P.getD i 0
  unfold unpackedByte
  by_cases hA : i < 498*k
  · rw [if_pos hA]
    obtain ⟨r, o, ho, rfl⟩ : ∃ r o, o < 498 ∧ i = 498*r + o :=
      ⟨i/498, i%498, Nat.mod_lt _ (by decide), by omega⟩
    have hr : r < k := by omega
    have e1 : (498*r+o)/498 = r := by omega
    have e2 : (498*r+o)%498 = o := by omega
    rw [e1, e2]
    clear e1 e2 h1 h2
    by_cases o1 : o < 15
    · rw [if_pos o1, hQ (481*r + o) (by unfold bodyLength; omega) (by omega)]
      unfold packedSource
      rw [if_pos (by omega), if_pos (by omega), show (481*r + o)/481 = r by omega,
        show (481*r + o)%481 = o by omega]
    rw [if_neg o1]
    by_cases o2 : o = 15
    · subst o2
      rw [if_pos rfl, hH _ hr]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, headByte_toNat]
      have hs := salt _ hr
      omega
    rw [if_neg o2]
    by_cases o3 : o < 46
    · rw [if_pos o3, hQ (481*r + o - 1) (by unfold bodyLength; omega) (by omega)]
      unfold packedSource
      rw [if_pos (by omega), if_neg (by omega), if_pos (by omega),
        show (481*r + o - 1)/481 = r by omega, show (481*r + o - 1)%481 = o - 1 by omega]
      congr 1; omega
    rw [if_neg o3]
    by_cases o4 : o = 46
    · subst o4
      rw [if_pos rfl, hH _ hr]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, headByte_toNat]
      have hs := leaf _ hr
      omega
    rw [if_neg o4]
    by_cases o5 : o < 48
    · rw [if_pos o5, show o = 47 by omega, leafTop _ hr]
    rw [if_neg o5]
    obtain ⟨d, c, hc, hd, rfl⟩ : ∃ d c, c < 30 ∧ d < 15 ∧ o = 48 + 30*d + c :=
      ⟨(o-48)/30, (o-48)%30, Nat.mod_lt _ (by decide), by omega, by omega⟩
    have f1 : (48 + 30*d + c - 48)/30 = d := by omega
    have f2 : (48 + 30*d + c - 48)%30 = c := by omega
    rw [f1, f2]
    clear f1 f2 o1 o2 o3 o4 o5
    by_cases hC : c = 29
    · subst hC
      rw [if_pos rfl, h29 _ (by omega)]
      unfold unpackedDigest
      rw [if_pos (by omega), show (15*r+d)/15 = r by omega, show (15*r+d)%15 = d by omega]
      congr 1; omega
    · have g1 : (481*r + 46 + 29*d + c) % 481 = 46 + 29*d + c := by omega
      have g2 : (481*r + 46 + 29*d + c) / 481 = r := by omega
      have g3 : (46 + 29*d + c - 46) / 29 = d := by omega
      have g4 : (46 + 29*d + c - 46) % 29 = c := by omega
      have hp : ¬(481*r + 46 + 29*d + c < 481*k ∧ (481*r + 46 + 29*d + c) % 481 = 45) := by
        rw [g1]; omega
      rw [if_neg hC, hQ (481*r + 46 + 29*d + c) (by unfold bodyLength; omega) hp]
      unfold packedSource
      rw [g1, g2, g3, g4, if_pos (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      congr 1; omega
  · rw [if_neg hA]
    by_cases hC : (i - 498*k)%30 = 29
    · rw [if_pos hC, h29 _ (by omega)]
      unfold unpackedDigest
      rw [if_neg (by omega)]
      congr 1; omega
    · rw [if_neg hC, hQ (481*k + 29*((i - 498*k)/30) + (i - 498*k)%30) (by unfold bodyLength; omega)
        (by omega)]
      unfold packedSource
      rw [if_neg (by omega)]
      congr 1; omega

end CommitGolfCandidate.ProofCodec
