import CommitGolf.Parameters
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! Mathematical model of the r=1 3-ary-bottom, left-aligned binary, cap C=14 (683 cap leaves)
vector commitment tree with paired 192-bit late salts (shared-midpoint 40-byte pair rows),
domain-separated iterated hash chains on levels `L9..L16` (`c_l^2 * 2^{w_l} >= 2^238`),
per-level variable-width digest truncation, and two-end variable-bit tail stream proofs.
Parameterized over any 768->256 compression function. -/
namespace CommitGolfCandidate
open CommitGolf

abbrev Salt192 := BitVec 192
abbrev PairRand := BitVec 320
abbrev Digest := BitVec 256
abbrev Comp96 := BitVec 768 → Digest

/-! ### Per-Level Width and Chain Schedule (`c_l^2 * 2^{w_l} >= 2^238`) -/

def levelWidth : Nat → Nat
  | 0 => 256
  | 1 => 256
  | 2 => 240
  | 3 => 240
  | 4 => 240
  | 5 => 240
  | 6 => 238
  | 7 => 238
  | 8 => 238
  | 9 => 236
  | 10 => 234
  | 11 => 232
  | 12 => 231
  | 13 => 230
  | 14 => 230
  | 15 => 230
  | 16 => 233
  | 17 => 238
  | 18 => 238
  | 19 => 238
  | 20 => 238
  | 21 => 238
  | 22 => 238
  | 23 => 238
  | _ => 256

def levelChain : Nat → Nat
  | 9 => 2
  | 10 => 4
  | 11 => 8
  | 12 => 12
  | 13 => 16
  | 14 => 16
  | 15 => 16
  | 16 => 6
  | _ => 1

def levelBodyBytes (l : Nat) : Nat := levelWidth l / 8
def levelTailBits (l : Nat) : Nat := levelWidth l % 8
def levelShift (l : Nat) : Nat := 256 - levelWidth l
def levelTagStart (l : Nat) : Nat := if levelChain l > 1 then 256 * l + 1 else 0
def levelTag (l s : Nat) : BitVec 64 := BitVec.ofNat 64 (256 * l + s)

def commitMeta3C (l : Nat) : Nat :=
  (levelChain l - 1) + levelShift l * 256 + levelTagStart l * 2 ^ 32

def levelMetaOC (l : Nat) : Nat :=
  levelBodyBytes l + levelTailBits l * 256 + levelChain l * 65536 +
    levelShift l * 16777216 + levelTagStart l * 2 ^ 32

theorem levelWidth_ge_192 (l : Nat) : 192 ≤ levelWidth l := by
  by_cases h : l < 25
  · interval_cases l <;> decide
  · match l with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
    | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 => omega
    | n + 24 => simp [levelWidth]

theorem levelWidth_le_256 (l : Nat) : levelWidth l ≤ 256 := by
  by_cases h : l < 25
  · interval_cases l <;> decide
  · match l with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
    | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 => omega
    | n + 24 => simp [levelWidth]

theorem levelTailBits_lt_8 (l : Nat) : levelTailBits l < 8 :=
  Nat.mod_lt _ (by decide)

theorem levelBodyBytes_mul_add_tail (l : Nat) :
    8 * levelBodyBytes l + levelTailBits l = levelWidth l := by
  unfold levelBodyBytes levelTailBits; omega

theorem levelChain_security (l : Nat) (hl : l ≤ 24) :
    2 ^ 238 ≤ levelChain l ^ 2 * 2 ^ levelWidth l := by
  interval_cases l <;> decide

/-! ### Generic `w`-bit, `240`-bit, and `238`-bit Truncation -/

def lowWidth (w : Nat) (d : Digest) : BitVec w := d.extractLsb' 0 w

def maskWidth (w : Nat) (d : Digest) : Digest :=
  (d.extractLsb' 0 w).setWidth 256

theorem maskWidth_getLsbD (w : Nat) (d : Digest) (i : Nat) :
    (maskWidth w d).getLsbD i = (decide (i < w) && d.getLsbD i) := by
  unfold maskWidth
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb', Nat.zero_add]
  by_cases hi : i < 256
  · simp [hi]
  · have hge : d.getLsbD i = false := BitVec.getLsbD_of_ge d i (by omega)
    simp [hi, hge]

theorem maskWidth_256 (d : Digest) : maskWidth 256 d = d := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [maskWidth_getLsbD]
  simp [hi]

theorem lowWidth_maskWidth (w : Nat) (hw : w ≤ 256) (d : Digest) :
    lowWidth w (maskWidth w d) = lowWidth w d := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [lowWidth, BitVec.getLsbD_extractLsb', hi, maskWidth_getLsbD]

theorem maskWidth_idempotent (w : Nat) (d : Digest) :
    maskWidth w (maskWidth w d) = maskWidth w d := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [maskWidth_getLsbD]
  by_cases h : i < w <;> simp [h]

theorem maskWidth_eq_iff (w : Nat) (hw : w ≤ 256) (a b : Digest) :
    maskWidth w a = maskWidth w b ↔ lowWidth w a = lowWidth w b := by
  constructor
  · intro h
    have := congrArg (lowWidth w) h
    simpa only [lowWidth_maskWidth w hw] using this
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [maskWidth_getLsbD]
    by_cases hlt : i < w
    · have hb := congrArg (fun v : BitVec w => v.getLsbD i) h
      simp only [lowWidth, BitVec.getLsbD_extractLsb', hlt, decide_true, Bool.true_and, Nat.zero_add] at hb
      simp [hlt, hb]
    · simp [hlt]

theorem extractLsb'_192_maskWidth (w : Nat) (hw : 192 ≤ w) (d : Digest) :
    (maskWidth w d).extractLsb' 0 192 = d.extractLsb' 0 192 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and, Nat.zero_add,
    maskWidth_getLsbD, show i < w by omega]

theorem maskWidth_byte_lt (w : Nat) (d : Digest) (j : Nat) (hj : j < w / 8) :
    (maskWidth w d).extractLsb' (8 * j) 8 = d.extractLsb' (8 * j) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp only [BitVec.getLsbD_extractLsb', hb, decide_true, Bool.true_and, maskWidth_getLsbD,
    show 8 * j + b < w by omega]

theorem maskWidth_byte_gt (w : Nat) (d : Digest) (j : Nat) (hj : (w + 7) / 8 ≤ j) :
    (maskWidth w d).extractLsb' (8 * j) 8 = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  have hge : ¬ (8 * j + b < w) := by omega
  simp [BitVec.getLsbD_extractLsb', hb, maskWidth_getLsbD, hge]

theorem maskWidth_byte_partial (w : Nat) (hw : w ≤ 256) (d : Digest) :
    (maskWidth w d).extractLsb' (8 * (w / 8)) 8 =
      BitVec.ofNat 8 (d.extractLsb' (8 * (w / 8)) (w % 8)).toNat := by
  rw [BitVec.ofNat_toNat]
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, hb, decide_true, Bool.true_and,
    maskWidth_getLsbD]
  by_cases hlt : b < w % 8
  · simp [hlt, show 8 * (w / 8) + b < w by omega]
  · simp [hlt, show ¬ (8 * (w / 8) + b < w) by omega]

def low240 (d : Digest) : BitVec 240 := d.extractLsb' 0 240
def mask240 (d : Digest) : Digest := (0#16) ++ low240 d

theorem low240_mask240 (d : Digest) : low240 (mask240 d) = low240 d := by
  unfold low240 mask240; exact BitVec.extractLsb'_append_eq_right

theorem mask240_idempotent (d : Digest) : mask240 (mask240 d) = mask240 d := by
  change (0#16) ++ low240 (mask240 d) = mask240 d; rw [low240_mask240]; rfl

theorem mask240_eq_iff (a b : Digest) : mask240 a = mask240 b ↔ low240 a = low240 b := by
  constructor
  · intro h; have := congrArg low240 h; simpa only [low240_mask240] using this
  · intro h; simp only [mask240, h]

theorem mask240_getLsbD (d : Digest) (i : Nat) :
    (mask240 d).getLsbD i = (decide (i < 240) && d.getLsbD i) := by
  unfold mask240 low240; rw [BitVec.getLsbD_append]
  by_cases hi : i < 240 <;> simp [hi]

theorem maskWidth_240 (d : Digest) : maskWidth 240 d = mask240 d := by
  apply BitVec.eq_of_getLsbD_eq; intro i _; rw [maskWidth_getLsbD, mask240_getLsbD]

theorem extractLsb'_192_mask240 (d : Digest) :
    (mask240 d).extractLsb' 0 192 = d.extractLsb' 0 192 := by
  rw [← maskWidth_240]; exact extractLsb'_192_maskWidth 240 (by omega) d

theorem mask240_byte_lt30 (d : Digest) (j : Nat) (hj : j < 30) :
    (mask240 d).extractLsb' (8 * j) 8 = d.extractLsb' (8 * j) 8 := by
  rw [← maskWidth_240]; exact maskWidth_byte_lt 240 d j (by omega)

theorem mask240_byte_ge30 (d : Digest) (j : Nat) (hj : 30 ≤ j) :
    (mask240 d).extractLsb' (8 * j) 8 = 0 := by
  rw [← maskWidth_240]; exact maskWidth_byte_gt 240 d j (by omega)

def low238 (d : Digest) : BitVec 238 := d.extractLsb' 0 238
def mask238 (d : Digest) : Digest := (0#18) ++ low238 d
def tail6 (d : Digest) : BitVec 6 := d.extractLsb' 232 6

theorem low238_mask238 (d : Digest) : low238 (mask238 d) = low238 d := by
  unfold low238 mask238; exact BitVec.extractLsb'_append_eq_right

theorem mask238_idempotent (d : Digest) : mask238 (mask238 d) = mask238 d := by
  change (0#18) ++ low238 (mask238 d) = mask238 d; rw [low238_mask238]; rfl

theorem mask238_getLsbD (d : Digest) (i : Nat) :
    (mask238 d).getLsbD i = (decide (i < 238) && d.getLsbD i) := by
  unfold mask238 low238; rw [BitVec.getLsbD_append]
  by_cases hi : i < 238 <;> simp [hi]

theorem maskWidth_238 (d : Digest) : maskWidth 238 d = mask238 d := by
  apply BitVec.eq_of_getLsbD_eq; intro i _; rw [maskWidth_getLsbD, mask238_getLsbD]

theorem mask238_byte_lt29 (d : Digest) (j : Nat) (hj : j < 29) :
    (mask238 d).extractLsb' (8 * j) 8 = d.extractLsb' (8 * j) 8 := by
  rw [← maskWidth_238]; exact maskWidth_byte_lt 238 d j (by omega)

theorem mask238_byte_29 (d : Digest) :
    (mask238 d).extractLsb' (8 * 29) 8 = (0#2) ++ tail6 d := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  unfold tail6
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  simp only [hb, decide_true, Bool.true_and, mask238_getLsbD]
  by_cases h6 : b < 6
  · simp [h6, show 8 * 29 + b < 238 by omega, show 232 + b = 8 * 29 + b by omega]
  · simp [h6, show ¬ (8 * 29 + b < 238) by omega]

theorem mask238_byte_ge30 (d : Digest) (j : Nat) (hj : 30 ≤ j) :
    (mask238 d).extractLsb' (8 * j) 8 = 0 := by
  rw [← maskWidth_238]; exact maskWidth_byte_gt 238 d j (by omega)

def maskLevel (l : Nat) (d : Digest) : Digest := maskWidth (levelWidth l) d

theorem maskLevel_idempotent (l : Nat) (d : Digest) : maskLevel l (maskLevel l d) = maskLevel l d :=
  maskWidth_idempotent (levelWidth l) d

theorem extractLsb'_192_maskLevel (l : Nat) (d : Digest) :
    (maskLevel l d).extractLsb' 0 192 = d.extractLsb' 0 192 :=
  extractLsb'_192_maskWidth (levelWidth l) (levelWidth_ge_192 l) d

theorem maskLevel_eq_mask240 (l : Nat) (hl1 : 2 ≤ l) (hl2 : l ≤ 5) (d : Digest) :
    maskLevel l d = mask240 d := by
  interval_cases l <;> exact maskWidth_240 d

theorem maskLevel_eq_mask238_lo (l : Nat) (hl1 : 6 ≤ l) (hl2 : l ≤ 8) (d : Digest) :
    maskLevel l d = mask238 d := by
  interval_cases l <;> exact maskWidth_238 d

theorem maskLevel_eq_mask238_hi (l : Nat) (hl1 : 17 ≤ l) (hl2 : l ≤ 23) (d : Digest) :
    maskLevel l d = mask238 d := by
  interval_cases l <;> exact maskWidth_238 d

theorem maskLevel_24 (d : Digest) : maskLevel 24 d = d :=
  maskWidth_256 d

/-! ### Exact r=1 Tree Geometry and Paired Late-Salt Row Layout -/

def FULL_TRIPLETS : Nat := LENGTH / 3
def CAP_CUT_LVL : Nat := 14
def PAIR_STRIDE : Nat := 184
def PAIR_RAND_BYTES : Nat := 40

def levelSize : Nat → Nat
  | 0 => LENGTH
  | 1 => (LENGTH + 2) / 3
  | n + 2 => (levelSize (n + 1) + 1) / 2

def levelBytes (l : Nat) : Nat :=
  if l = 0 then levelSize 0 * 32
  else if l < 24 then ((levelSize l + 1) / 2) * 96
  else 32

def levelBase : Nat → Nat
  | 0 => 0
  | n + 1 => levelBase n + levelBytes n

def treeBytes : Nat := levelBase 24 + levelBytes 24
def rowOff : Nat := treeBytes
def rowBytes : Nat := (LENGTH / 2) * PAIR_STRIDE
def trapdoorBytes : Nat := rowOff + rowBytes
def proofCap : Nat := 8556390424
def tailBufBase : Nat := 20000000000
def commitChainScratch : Nat := 8589934592

def saltOff (i : Index) : Nat :=
  rowOff + PAIR_STRIDE * (i.val / 2) + if i.val % 2 = 0 then 72 else 88

def gapOffset (idx : Nat) : Nat := 32 * (idx + idx / 2)

def nodeOffset (l idx : Nat) : Nat :=
  if l = 0 then 32 * idx else gapOffset idx

def capMarkOff : Nat → Nat
  | 0 => 0
  | n + 1 =>
    if n < 14 then 0
    else capMarkOff n + ((levelSize n + 7) / 8) * 8

def capValOff : Nat → Nat
  | 0 => 0
  | n + 1 =>
    if n < 14 then 0
    else capValOff n + ((levelSize n + 1) / 2) * 96

theorem full_triplets_eq : FULL_TRIPLETS = 5592405 := by decide
theorem levelSize_0 : levelSize 0 = 16777216 := by decide
theorem levelSize_1 : levelSize 1 = 5592406 := by decide
theorem levelSize_2 : levelSize 2 = 2796203 := by decide
theorem levelSize_5 : levelSize 5 = 349526 := by decide
theorem levelSize_8 : levelSize 8 = 43691 := by decide
theorem levelSize_14 : levelSize 14 = 683 := by decide
theorem levelSize_15 : levelSize 15 = 342 := by decide
theorem levelSize_16 : levelSize 16 = 171 := by decide
theorem levelSize_17 : levelSize 17 = 86 := by decide
theorem levelSize_23 : levelSize 23 = 2 := by decide
theorem levelSize_24 : levelSize 24 = 1 := by decide
theorem treeBytes_eq : treeBytes = 1073742880 := by decide
theorem rowOff_eq : rowOff = 1073742880 := by decide
theorem rowBytes_eq : rowBytes = 1543503872 := by decide
theorem trapdoorBytes_eq : trapdoorBytes = 2617246752 := by decide

theorem saltOff_even (j : Nat) (hj : 2 * j < LENGTH) :
    saltOff ⟨2 * j, hj⟩ = rowOff + 184 * j + 72 := by
  unfold saltOff PAIR_STRIDE
  simp [show 2 * j / 2 = j by omega, show 2 * j % 2 = 0 by omega]

theorem saltOff_odd (j : Nat) (hj : 2 * j + 1 < LENGTH) :
    saltOff ⟨2 * j + 1, hj⟩ = rowOff + 184 * j + 88 := by
  unfold saltOff PAIR_STRIDE
  simp [show (2 * j + 1) / 2 = j by omega, show (2 * j + 1) % 2 = 1 by omega]

theorem saltOff_add_24_le (i : Index) : saltOff i + 24 ≤ trapdoorBytes := by
  unfold saltOff trapdoorBytes rowBytes PAIR_STRIDE
  have hi : i.val < 16777216 := i.isLt
  have hlen : LENGTH / 2 = 8388608 := by decide
  rw [hlen]
  split_ifs <;> omega

theorem levelSize_step (l : Nat) (hl : 1 ≤ l) :
    levelSize (l + 1) = (levelSize l + 1) / 2 := by
  cases l with
  | zero => omega
  | succ k => rfl

theorem levelSize_pos (l : Nat) (hl : l ≤ 24) : 0 < levelSize l := by
  interval_cases l <;> decide

theorem levelSize_ge_two (l : Nat) (hl : l < 24) : 2 ≤ levelSize l := by
  interval_cases l <;> decide

theorem levelBase_bound (l : Nat) (hl : l ≤ 24) :
    levelBase l + levelBytes l ≤ treeBytes := by
  interval_cases l <;> decide

theorem capMarkOff_bound (l : Nat) (hl : 14 ≤ l) (hl2 : l ≤ 24) :
    capMarkOff l + levelSize l ≤ 1416 := by
  interval_cases l <;> decide

theorem capValOff_bound (l : Nat) (hl : 14 ≤ l) (hl2 : l ≤ 24) :
    capValOff l + levelBytes l ≤ 65984 := by
  interval_cases l <;> decide

theorem gapOffset_even (q : Nat) : gapOffset (2 * q) = 96 * q := by
  unfold gapOffset; omega

theorem gapOffset_odd (q : Nat) : gapOffset (2 * q + 1) = 96 * q + 32 := by
  unfold gapOffset; omega

theorem gapOffset_lt_levelBytes (l idx : Nat) (hl1 : 1 ≤ l) (hl2 : l < 24)
    (hidx : idx < levelSize l) :
    gapOffset idx + 32 ≤ levelBytes l := by
  unfold gapOffset levelBytes
  have h0 : l ≠ 0 := by omega
  simp only [h0, ite_false, hl2, ite_true]
  omega

/-! ### Shared-Midpoint Paired Late-Salt Decomposition -/

def pairSL (r : PairRand) : BitVec 128 := r.extractLsb' 0 128
def pairSM (r : PairRand) : BitVec 64 := r.extractLsb' 128 64
def pairSR (r : PairRand) : BitVec 128 := r.extractLsb' 192 128

def pairSaltEven (r : PairRand) : Salt192 := r.extractLsb' 0 192
def pairSaltOdd (r : PairRand) : Salt192 := r.extractLsb' 128 192

def pairSalts (rand : Fin (LENGTH / 2) → PairRand) (i : Index) : Salt192 :=
  let j : Fin (LENGTH / 2) := ⟨i.val / 2, by have := i.isLt; unfold LENGTH LOG_LENGTH at *; omega⟩
  if i.val % 2 = 0 then pairSaltEven (rand j) else pairSaltOdd (rand j)

theorem pairSaltEven_eq (r : PairRand) : pairSaltEven r = pairSM r ++ pairSL r := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  unfold pairSaltEven pairSM pairSL
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hb, decide_true, Bool.true_and,
    Nat.zero_add]
  by_cases h128 : b < 128
  · simp [h128]
  · have h64 : b - 128 < 64 := by omega
    simp [h128, h64, show 128 + (b - 128) = b by omega]

theorem pairSaltOdd_eq (r : PairRand) : pairSaltOdd r = pairSR r ++ pairSM r := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  unfold pairSaltOdd pairSR pairSM
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hb, decide_true, Bool.true_and]
  by_cases h64 : b < 64
  · simp [h64]
  · have h128 : b - 64 < 128 := by omega
    simp [h64, h128, show 192 + (b - 64) = 128 + b by omega]

theorem pairRand_eq_parts (r : PairRand) : r = (pairSR r ++ pairSM r) ++ pairSL r := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  unfold pairSR pairSM pairSL
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb', Nat.zero_add]
  by_cases h128 : b < 128
  · simp [h128]
  · by_cases h192 : b < 192
    · have h64 : b - 128 < 64 := by omega
      simp [h128, h64, show 128 + (b - 128) = b by omega]
    · have h64 : ¬ (b - 128 < 64) := by omega
      have hhi : b - 128 - 64 < 128 := by omega
      simp [h128, h64, hhi, show 192 + (b - 128 - 64) = b by omega]

/-! ### Leaf Compression Inputs, Domain-Separated Chains, and Tree Semantics -/

def leafUInput (val : Entry) : BitVec 768 := val.extractLsb' 0 768
def leafAInput (u : Digest) (val : Entry) : BitVec 768 := val.extractLsb' 768 512 ++ u
def leafBInput (val : Entry) : BitVec 768 := val.extractLsb' 1280 768

def leafA (c : Comp96) (val : Entry) : Digest :=
  c (leafAInput (c (leafUInput val)) val)

def leafB (c : Comp96) (val : Entry) : Digest :=
  c (leafBInput val)

def leafFinalEven (a b : Digest) (salt : Salt192) : BitVec 768 :=
  ((salt ++ (0#64)) ++ b) ++ a

def leafFinalOdd (a b : Digest) (salt : Salt192) : BitVec 768 :=
  ((b ++ a) ++ (0#64)) ++ salt

def leafFinalInput (i : Index) (a b : Digest) (salt : Salt192) : BitVec 768 :=
  if i.val % 2 = 0 then leafFinalEven a b salt else leafFinalOdd a b salt

def leafDigest (c : Comp96) (i : Index) (salt : Salt192) (val : Entry) : Digest :=
  c (leafFinalInput i (leafA c val) (leafB c val) salt)

theorem leafAInput_u (u : Digest) (val : Entry) :
    (leafAInput u val).extractLsb' 0 256 = u :=
  BitVec.extractLsb'_append_eq_right

theorem leafAInput_mid (u : Digest) (val : Entry) :
    (leafAInput u val).extractLsb' 256 512 = val.extractLsb' 768 512 := by
  unfold leafAInput
  rw [BitVec.extractLsb'_append_eq_of_le (by decide : 256 ≤ 256)]
  simpa using BitVec.extractLsb'_eq_self (x := val.extractLsb' 768 512)

theorem leafFinalEven_a (a b : Digest) (salt : Salt192) :
    (leafFinalEven a b salt).extractLsb' 0 256 = a :=
  BitVec.extractLsb'_append_eq_right

theorem leafFinalEven_b (a b : Digest) (salt : Salt192) :
    (leafFinalEven a b salt).extractLsb' 256 256 = b := by
  unfold leafFinalEven
  rw [BitVec.extractLsb'_append_eq_of_le (by decide : 256 ≤ 256)]
  exact BitVec.extractLsb'_append_eq_right

theorem leafFinalEven_zero (a b : Digest) (salt : Salt192) :
    (leafFinalEven a b salt).extractLsb' 512 64 = 0#64 := by
  unfold leafFinalEven
  rw [BitVec.extractLsb'_append_eq_of_le (by decide : 256 ≤ 512)]
  rw [BitVec.extractLsb'_append_eq_of_le (by decide : 256 ≤ 512 - 256)]
  exact BitVec.extractLsb'_append_eq_right

theorem leafFinalEven_salt (a b : Digest) (salt : Salt192) :
    (leafFinalEven a b salt).extractLsb' 576 192 = salt := by
  unfold leafFinalEven
  rw [BitVec.extractLsb'_append_eq_of_le (by decide : 256 ≤ 576)]
  rw [BitVec.extractLsb'_append_eq_of_le (by decide : 256 ≤ 576 - 256)]
  rw [BitVec.extractLsb'_append_eq_of_le (by decide : 64 ≤ 576 - 256 - 256)]
  simpa using BitVec.extractLsb'_eq_self (x := salt)

theorem leafFinalOdd_salt (a b : Digest) (salt : Salt192) :
    (leafFinalOdd a b salt).extractLsb' 0 192 = salt :=
  BitVec.extractLsb'_append_eq_right

theorem leafFinalOdd_zero (a b : Digest) (salt : Salt192) :
    (leafFinalOdd a b salt).extractLsb' 192 64 = 0#64 := by
  unfold leafFinalOdd
  rw [BitVec.extractLsb'_append_eq_of_le (by decide : 192 ≤ 192)]
  exact BitVec.extractLsb'_append_eq_right

theorem leafFinalOdd_a (a b : Digest) (salt : Salt192) :
    (leafFinalOdd a b salt).extractLsb' 256 256 = a := by
  unfold leafFinalOdd
  rw [BitVec.extractLsb'_append_eq_of_le (by decide : 192 ≤ 256)]
  rw [BitVec.extractLsb'_append_eq_of_le (by decide : 64 ≤ 256 - 192)]
  exact BitVec.extractLsb'_append_eq_right

theorem leafFinalOdd_b (a b : Digest) (salt : Salt192) :
    (leafFinalOdd a b salt).extractLsb' 512 256 = b := by
  unfold leafFinalOdd
  rw [BitVec.extractLsb'_append_eq_of_le (by decide : 192 ≤ 512)]
  rw [BitVec.extractLsb'_append_eq_of_le (by decide : 64 ≤ 512 - 192)]
  rw [BitVec.extractLsb'_append_eq_of_le (by decide : 256 ≤ 512 - 192 - 64)]
  simpa using BitVec.extractLsb'_eq_self (x := b)

theorem leafFinalEven_inj {a1 b1 a2 b2 : Digest} {s1 s2 : Salt192}
    (h : leafFinalEven a1 b1 s1 = leafFinalEven a2 b2 s2) :
    a1 = a2 ∧ b1 = b2 ∧ s1 = s2 := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [leafFinalEven_a] using congrArg (fun v => v.extractLsb' 0 256) h
  · simpa [leafFinalEven_b] using congrArg (fun v => v.extractLsb' 256 256) h
  · simpa [leafFinalEven_salt] using congrArg (fun v => v.extractLsb' 576 192) h

theorem leafFinalOdd_inj {a1 b1 a2 b2 : Digest} {s1 s2 : Salt192}
    (h : leafFinalOdd a1 b1 s1 = leafFinalOdd a2 b2 s2) :
    a1 = a2 ∧ b1 = b2 ∧ s1 = s2 := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [leafFinalOdd_a] using congrArg (fun v => v.extractLsb' 256 256) h
  · simpa [leafFinalOdd_b] using congrArg (fun v => v.extractLsb' 512 256) h
  · simpa [leafFinalOdd_salt] using congrArg (fun v => v.extractLsb' 0 192) h

theorem leafFinalInput_inj {i : Index} {a1 b1 a2 b2 : Digest} {s1 s2 : Salt192}
    (h : leafFinalInput i a1 b1 s1 = leafFinalInput i a2 b2 s2) :
    a1 = a2 ∧ b1 = b2 ∧ s1 = s2 := by
  unfold leafFinalInput at h
  split_ifs at h
  · exact leafFinalEven_inj h
  · exact leafFinalOdd_inj h

theorem entry_eq_of_late_slices (a b : Entry)
    (h0 : a.extractLsb' 0 768 = b.extractLsb' 0 768)
    (h1 : a.extractLsb' 768 512 = b.extractLsb' 768 512)
    (h2 : a.extractLsb' 1280 768 = b.extractLsb' 1280 768) :
    a = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  change k < 2048 at hk
  by_cases c0 : k < 768
  · have := congrArg (fun v => v.getLsbD k) h0
    simpa [BitVec.getLsbD_extractLsb', c0] using this
  · by_cases c1 : k < 1280
    · have := congrArg (fun v => v.getLsbD (k - 768)) h1
      simpa [BitVec.getLsbD_extractLsb', show k - 768 < 512 by omega,
        show 768 + (k - 768) = k by omega] using this
    · have := congrArg (fun v => v.getLsbD (k - 1280)) h2
      simpa [BitVec.getLsbD_extractLsb', show k - 1280 < 768 by omega,
        show 1280 + (k - 1280) = k by omega] using this

def ternaryInput (d0 d1 d2 : Digest) : BitVec 768 := (d2 ++ d1) ++ d0

def binaryInput (left right : Digest) : BitVec 768 := ((0#256) ++ right) ++ left

def binaryTaggedInput (left right : Digest) (tag : BitVec 64) : BitVec 768 :=
  (((0#192) ++ tag) ++ right) ++ left

def chainStepInput (prev : Digest) (tag : BitVec 64) : BitVec 768 :=
  (((0#192) ++ tag) ++ (0#256)) ++ prev

theorem ternaryInput_d0 (d0 d1 d2 : Digest) : (ternaryInput d0 d1 d2).extractLsb' 0 256 = d0 :=
  BitVec.extractLsb'_append_eq_right

theorem ternaryInput_d1 (d0 d1 d2 : Digest) : (ternaryInput d0 d1 d2).extractLsb' 256 256 = d1 := by
  unfold ternaryInput
  rw [BitVec.extractLsb'_append_eq_of_le (by decide : 256 ≤ 256)]
  exact BitVec.extractLsb'_append_eq_right

theorem ternaryInput_d2 (d0 d1 d2 : Digest) : (ternaryInput d0 d1 d2).extractLsb' 512 256 = d2 := by
  unfold ternaryInput
  rw [BitVec.extractLsb'_append_eq_of_le (by decide : 256 ≤ 512)]
  rw [BitVec.extractLsb'_append_eq_of_le (by decide : 256 ≤ 512 - 256)]
  simpa using BitVec.extractLsb'_eq_self (x := d2)

theorem binaryInput_left (l r : Digest) : (binaryInput l r).extractLsb' 0 256 = l :=
  BitVec.extractLsb'_append_eq_right

theorem binaryInput_right (l r : Digest) : (binaryInput l r).extractLsb' 256 256 = r := by
  unfold binaryInput
  rw [BitVec.extractLsb'_append_eq_of_le (by decide : 256 ≤ 256)]
  exact BitVec.extractLsb'_append_eq_right

theorem binaryInput_tag (l r : Digest) : (binaryInput l r).extractLsb' 512 64 = 0#64 := by
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  unfold binaryInput
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hb, decide_true, Bool.true_and,
    show ¬ (512 + b < 256) by omega, show ¬ (512 + b - 256 < 256) by omega, ite_false,
    BitVec.getLsbD_zero]

theorem binaryTaggedInput_left (l r : Digest) (tag : BitVec 64) :
    (binaryTaggedInput l r tag).extractLsb' 0 256 = l :=
  BitVec.extractLsb'_append_eq_right

theorem binaryTaggedInput_right (l r : Digest) (tag : BitVec 64) :
    (binaryTaggedInput l r tag).extractLsb' 256 256 = r := by
  unfold binaryTaggedInput
  rw [BitVec.extractLsb'_append_eq_of_le (by decide : 256 ≤ 256)]
  exact BitVec.extractLsb'_append_eq_right

theorem binaryTaggedInput_tag (l r : Digest) (tag : BitVec 64) :
    (binaryTaggedInput l r tag).extractLsb' 512 64 = tag := by
  unfold binaryTaggedInput
  rw [BitVec.extractLsb'_append_eq_of_le (by decide : 256 ≤ 512)]
  rw [BitVec.extractLsb'_append_eq_of_le (by decide : 256 ≤ 512 - 256)]
  exact BitVec.extractLsb'_append_eq_right

theorem binaryTaggedInput_hi (l r : Digest) (tag : BitVec 64) :
    (binaryTaggedInput l r tag).extractLsb' 576 192 = 0#192 := by
  unfold binaryTaggedInput
  rw [BitVec.extractLsb'_append_eq_of_le (by decide : 256 ≤ 576)]
  rw [BitVec.extractLsb'_append_eq_of_le (by decide : 256 ≤ 576 - 256)]
  rw [BitVec.extractLsb'_append_eq_of_le (by decide : 64 ≤ 576 - 256 - 256)]
  simpa using BitVec.extractLsb'_eq_self (x := (0#192))

theorem chainStepInput_prev (p : Digest) (tag : BitVec 64) :
    (chainStepInput p tag).extractLsb' 0 256 = p :=
  BitVec.extractLsb'_append_eq_right

theorem chainStepInput_mid (p : Digest) (tag : BitVec 64) :
    (chainStepInput p tag).extractLsb' 256 256 = 0#256 := by
  unfold chainStepInput
  rw [BitVec.extractLsb'_append_eq_of_le (by decide : 256 ≤ 256)]
  exact BitVec.extractLsb'_append_eq_right

theorem chainStepInput_tag (p : Digest) (tag : BitVec 64) :
    (chainStepInput p tag).extractLsb' 512 64 = tag := by
  unfold chainStepInput
  rw [BitVec.extractLsb'_append_eq_of_le (by decide : 256 ≤ 512)]
  rw [BitVec.extractLsb'_append_eq_of_le (by decide : 256 ≤ 512 - 256)]
  exact BitVec.extractLsb'_append_eq_right

theorem chainStepInput_hi (p : Digest) (tag : BitVec 64) :
    (chainStepInput p tag).extractLsb' 576 192 = 0#192 := by
  unfold chainStepInput
  rw [BitVec.extractLsb'_append_eq_of_le (by decide : 256 ≤ 576)]
  rw [BitVec.extractLsb'_append_eq_of_le (by decide : 256 ≤ 576 - 256)]
  rw [BitVec.extractLsb'_append_eq_of_le (by decide : 64 ≤ 576 - 256 - 256)]
  simpa using BitVec.extractLsb'_eq_self (x := (0#192))

/-- Iterate stages `2 .. k+1` of a level-`l` domain-separated hash chain starting from stage-1 output `d`. -/
def chainIter (c : Comp96) (l : Nat) : Nat → Digest → Digest
  | 0, d => d
  | k + 1, d => c (chainStepInput (chainIter c l k d) (levelTag l (k + 2)))

/-- Unmasked output of the level-`l` binary (or `levelChain l`-stage chained) hash on `(left, right)`. -/
def chainEval (c : Comp96) (l : Nat) (left right : Digest) : Digest :=
  if levelChain l ≤ 1 then c (binaryInput left right)
  else chainIter c l (levelChain l - 1) (c (binaryTaggedInput left right (levelTag l 1)))

/-- Masked output of level `l`'s hash on `(left, right)`. -/
def chainHash (c : Comp96) (l : Nat) (left right : Digest) : Digest :=
  maskLevel l (chainEval c l left right)

/-- List of all compression inputs queried during `chainEval c l left right` (in execution order). -/
def chainIterInputs (c : Comp96) (l : Nat) : Nat → Digest → List (BitVec 768)
  | 0, _ => []
  | k + 1, d =>
      chainIterInputs c l k d ++ [chainStepInput (chainIter c l k d) (levelTag l (k + 2))]

def chainInputs (c : Comp96) (l : Nat) (left right : Digest) : List (BitVec 768) :=
  if levelChain l ≤ 1 then [binaryInput left right]
  else
    let x1 := binaryTaggedInput left right (levelTag l 1)
    x1 :: chainIterInputs c l (levelChain l - 1) (c x1)

theorem chainHash_unchained (c : Comp96) (l : Nat) (hl : levelChain l ≤ 1) (left right : Digest) :
    chainHash c l left right = maskLevel l (c (binaryInput left right)) := by
  simp [chainHash, chainEval, hl]

/-- Tree node values built from an arbitrary leaf-digest vector. -/
def nodeValFromLeaves (c : Comp96) (leaves : Index → Digest) : Nat → Nat → Digest
  | 0, idx => if h : idx < LENGTH then leaves ⟨idx, h⟩ else 0
  | 1, idx =>
      if idx < FULL_TRIPLETS then
        c (ternaryInput
          (nodeValFromLeaves c leaves 0 (3 * idx))
          (nodeValFromLeaves c leaves 0 (3 * idx + 1))
          (nodeValFromLeaves c leaves 0 (3 * idx + 2)))
      else if idx = FULL_TRIPLETS then
        nodeValFromLeaves c leaves 0 (3 * FULL_TRIPLETS)
      else 0
  | l + 2, idx =>
      let prev := l + 1
      if 2 * idx + 1 < levelSize prev then
        chainHash c (l + 2)
          (nodeValFromLeaves c leaves prev (2 * idx))
          (nodeValFromLeaves c leaves prev (2 * idx + 1))
      else if 2 * idx < levelSize prev then
        if l + 2 < 9 then
          nodeValFromLeaves c leaves prev (2 * idx)
        else
          chainHash c (l + 2) (nodeValFromLeaves c leaves prev (2 * idx)) 0
      else 0

def nodeVal (c : Comp96) (msg : Message) (salts : Index → Salt192) : Nat → Nat → Digest :=
  nodeValFromLeaves c (fun i => leafDigest c i (salts i) (msg i))

def rootVal (c : Comp96) (msg : Message) (salts : Index → Salt192) : Digest :=
  nodeVal c msg salts 24 0

/-- Every node on level `l ∈ [0..24]` is clean under `maskLevel l`. -/
theorem nodeValFromLeaves_maskedLevel (c : Comp96) (leaves : Index → Digest)
    (l idx : Nat) (hl : l ≤ 24) (hidx : idx < levelSize l) :
    maskLevel l (nodeValFromLeaves c leaves l idx) = nodeValFromLeaves c leaves l idx := by
  induction l generalizing idx with
  | zero => exact maskWidth_256 _
  | succ k ih =>
    cases k with
    | zero => exact maskWidth_256 _
    | succ m =>
      simp only [nodeValFromLeaves]
      split
      · exact maskLevel_idempotent (m + 2) _
      · split
        · rename_i hnot hlt
          split
          · rename_i hlt9
            have heqW : levelWidth (m + 2) = levelWidth (m + 1) := by
              have hm : m < 7 := by omega
              interval_cases m
              · change ¬ (2 * idx + 1 < 5592406) at hnot; change 2 * idx < 5592406 at hlt; omega
              · decide
              · change ¬ (2 * idx + 1 < 1398102) at hnot; change 2 * idx < 1398102 at hlt; omega
              · decide
              · change ¬ (2 * idx + 1 < 349526) at hnot; change 2 * idx < 349526 at hlt; omega
              · decide
              · change ¬ (2 * idx + 1 < 87382) at hnot; change 2 * idx < 87382 at hlt; omega
            unfold maskLevel
            rw [heqW]
            exact ih (2 * idx) (by omega) hlt
          · exact maskLevel_idempotent (m + 2) _
        · apply BitVec.eq_of_getLsbD_eq; intro i _; simp [maskLevel, maskWidth_getLsbD]

theorem nodeValFromLeaves_masked240 (c : Comp96) (leaves : Index → Digest)
    (l idx : Nat) (hl1 : 2 ≤ l) (hl2 : l ≤ 5) (hidx : idx < levelSize l) :
    mask240 (nodeValFromLeaves c leaves l idx) = nodeValFromLeaves c leaves l idx := by
  rw [← maskLevel_eq_mask240 l hl1 hl2]
  exact nodeValFromLeaves_maskedLevel c leaves l idx (by omega) hidx

theorem nodeValFromLeaves_masked238 (c : Comp96) (leaves : Index → Digest)
    (l idx : Nat) (hl1 : 6 ≤ l) (hl2 : l ≤ 8) (hidx : idx < levelSize l) :
    mask238 (nodeValFromLeaves c leaves l idx) = nodeValFromLeaves c leaves l idx := by
  rw [← maskLevel_eq_mask238_lo l hl1 hl2]
  exact nodeValFromLeaves_maskedLevel c leaves l idx (by omega) hidx

/-! ### Cap Marking (`C = 14`, `L14 = 683` cap leaves) and Exact `68,904`-Bit Bound -/

def capLeafOf (i : Index) : Nat := (i.val / 3) >>> 13

theorem capLeafOf_lt (i : Index) : capLeafOf i < 683 := by
  unfold capLeafOf
  have hi : i.val < 16777216 := i.isLt
  rw [Nat.shiftRight_eq_div_pow]
  omega

def capMark (positions : Positions) : Nat → Nat → Bool
  | 0, _ => false
  | n + 1, idx =>
      if n + 1 < 14 then false
      else if n + 1 = 14 then decide (∃ i ∈ positions, capLeafOf i = idx)
      else if 2 * idx + 1 < levelSize n then
        capMark positions n (2 * idx) || capMark positions n (2 * idx + 1)
      else if 2 * idx < levelSize n then
        capMark positions n (2 * idx)
      else false

theorem capMark_14 (positions : Positions) (idx : Nat) :
    capMark positions 14 idx = decide (∃ i ∈ positions, capLeafOf i = idx) := by
  rfl

theorem capMark_succ (positions : Positions) (l idx : Nat) (hl : 14 ≤ l) :
    capMark positions (l + 1) idx =
      if 2 * idx + 1 < levelSize l then
        capMark positions l (2 * idx) || capMark positions l (2 * idx + 1)
      else if 2 * idx < levelSize l then
        capMark positions l (2 * idx)
      else false := by
  have h1 : ¬ (l + 1 < 14) := by omega
  have h2 : ¬ (l + 1 = 14) := by omega
  simp only [capMark, h1, h2, ite_false]

theorem capMark_24_eq_true (positions : Positions) (hne : positions.Nonempty) :
    capMark positions 24 0 = true := by
  obtain ⟨i, hi⟩ := hne
  have h14 : capMark positions 14 (capLeafOf i) = true := by
    rw [capMark_14, decide_eq_true_eq]
    exact ⟨i, hi, rfl⟩
  have hstep : ∀ l idx, 14 ≤ l → idx < levelSize l →
      capMark positions l idx = true → capMark positions (l + 1) (idx / 2) = true := by
    intro l idx hl hidx hm
    rw [capMark_succ positions l (idx / 2) hl]
    by_cases hpair : 2 * (idx / 2) + 1 < levelSize l
    · rw [if_pos hpair]
      rcases Nat.even_or_odd' idx with ⟨q, rfl | rfl⟩
      · have hq : 2 * q / 2 = q := by omega
        simp [hq, hm]
      · have hq : (2 * q + 1) / 2 = q := by omega
        simp [hq, hm]
    · rw [if_neg hpair]
      have hlt : 2 * (idx / 2) < levelSize l := by omega
      rw [if_pos hlt]
      have heq : 2 * (idx / 2) = idx := by omega
      rwa [heq]
  have h15 := hstep 14 _ (by omega) (by rw [levelSize_14]; exact capLeafOf_lt i) h14
  have h16 := hstep 15 _ (by omega) (by have := capLeafOf_lt i; change _ < 342; omega) h15
  have h17 := hstep 16 _ (by omega) (by have := capLeafOf_lt i; change _ < 171; omega) h16
  have h18 := hstep 17 _ (by omega) (by have := capLeafOf_lt i; change _ < 86; omega) h17
  have h19 := hstep 18 _ (by omega) (by have := capLeafOf_lt i; change _ < 43; omega) h18
  have h20 := hstep 19 _ (by omega) (by have := capLeafOf_lt i; change _ < 22; omega) h19
  have h21 := hstep 20 _ (by omega) (by have := capLeafOf_lt i; change _ < 11; omega) h20
  have h22 := hstep 21 _ (by omega) (by have := capLeafOf_lt i; change _ < 6; omega) h21
  have h23 := hstep 22 _ (by omega) (by have := capLeafOf_lt i; change _ < 3; omega) h22
  have h24 := hstep 23 _ (by omega) (by have := capLeafOf_lt i; change _ < 2; omega) h23
  have hz : capLeafOf i / 2 / 2 / 2 / 2 / 2 / 2 / 2 / 2 / 2 / 2 = 0 := by
    have := capLeafOf_lt i; omega
  rwa [hz] at h24

def levelFrontierCount (positions : Positions) (l : Nat) : Nat :=
  ((Finset.range (levelSize l / 2)).filter
    (fun q => capMark positions l (2 * q) != capMark positions l (2 * q + 1))).card

def capFrontierCount (positions : Positions) : Nat :=
  ∑ step ∈ Finset.range 10, levelFrontierCount positions (14 + step)

def capFrontierBits (positions : Positions) : Nat :=
  ∑ step ∈ Finset.range 10, levelWidth (14 + step) * levelFrontierCount positions (14 + step)

def levelUnmarkedCount (positions : Positions) (l : Nat) : Nat :=
  ((Finset.range (levelSize l)).filter (fun idx => !capMark positions l idx)).card

def levelMarkedCount (positions : Positions) (l : Nat) : Nat :=
  ((Finset.range (levelSize l)).filter (fun idx => capMark positions l idx)).card

private theorem sum_range_pairs (f : Nat → Nat) (p : Nat) :
    ∑ i ∈ Finset.range (2 * p), f i = ∑ q ∈ Finset.range p, (f (2 * q) + f (2 * q + 1)) := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [show 2 * (p + 1) = 2 * p + 1 + 1 by omega, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ]
    omega

private theorem card_filter_eq_sum (n : Nat) (p : Nat → Bool) :
    ((Finset.range n).filter (fun i => p i = true)).card =
      ∑ i ∈ Finset.range n, if p i = true then 1 else 0 := by
  rw [Finset.card_filter]

theorem levelMarked_add_unmarked (positions : Positions) (l : Nat) :
    levelMarkedCount positions l + levelUnmarkedCount positions l = levelSize l := by
  unfold levelMarkedCount levelUnmarkedCount
  rw [card_filter_eq_sum, card_filter_eq_sum, ← Finset.sum_add_distrib]
  calc
    ∑ i ∈ Finset.range (levelSize l),
        ((if capMark positions l i = true then 1 else 0) +
         (if (!capMark positions l i) = true then 1 else 0))
      = ∑ _i ∈ Finset.range (levelSize l), 1 := by
          apply Finset.sum_congr rfl; intro i _
          cases capMark positions l i <;> decide
    _ = levelSize l := by simp

theorem frontier_add_unmarked_succ (positions : Positions) (l : Nat) (hl : 14 ≤ l) :
    levelFrontierCount positions l + levelUnmarkedCount positions (l + 1) ≤
      levelUnmarkedCount positions l := by
  unfold levelFrontierCount levelUnmarkedCount
  have hstep : levelSize (l + 1) = (levelSize l + 1) / 2 := levelSize_step l (by omega)
  rw [hstep, card_filter_eq_sum, card_filter_eq_sum, card_filter_eq_sum]
  set p := levelSize l / 2
  rcases Nat.even_or_odd' (levelSize l) with ⟨k, hk | hk⟩
  · have hp : p = k := by omega
    have hnext : (levelSize l + 1) / 2 = k := by omega
    rw [hp, hnext, ← Finset.sum_add_distrib, hk, sum_range_pairs]
    apply Finset.sum_le_sum
    intro q hq
    have hq' : q < k := Finset.mem_range.mp hq
    have hpair : 2 * q + 1 < levelSize l := by omega
    rw [capMark_succ positions l q hl, if_pos hpair]
    cases capMark positions l (2 * q) <;> cases capMark positions l (2 * q + 1) <;> decide
  · have hp : p = k := by omega
    have hnext : (levelSize l + 1) / 2 = k + 1 := by omega
    rw [hp, hnext, Finset.sum_range_succ, hk, Finset.sum_range_succ, sum_range_pairs]
    have hpairSum :
        ∑ q ∈ Finset.range k,
          ((if (capMark positions l (2 * q) != capMark positions l (2 * q + 1)) = true then 1 else 0) +
           (if (!capMark positions (l + 1) q) = true then 1 else 0)) ≤
        ∑ q ∈ Finset.range k,
          ((if (!capMark positions l (2 * q)) = true then 1 else 0) +
           (if (!capMark positions l (2 * q + 1)) = true then 1 else 0)) := by
      apply Finset.sum_le_sum
      intro q hq
      have hq' : q < k := Finset.mem_range.mp hq
      have hpair : 2 * q + 1 < levelSize l := by omega
      rw [capMark_succ positions l q hl, if_pos hpair]
      cases capMark positions l (2 * q) <;> cases capMark positions l (2 * q + 1) <;> decide
    have hprom : capMark positions (l + 1) k = capMark positions l (2 * k) := by
      rw [capMark_succ positions l k hl, if_neg (by omega), if_pos (by omega)]
    rw [Finset.sum_add_distrib] at hpairSum
    rw [hprom]
    omega

/-- Exact pair identity for every cap level `l >= 14`:
- even `levelSize l`: `f_l + m_l = 2 * m_{l+1}`
- odd `levelSize l`: `f_l + m_l + p_l = 2 * m_{l+1}` and `m_{l+1} ≤ levelSize l / 2 + p_l`. -/
theorem frontier_add_marked_even (positions : Positions) (l : Nat) (hl : 14 ≤ l)
    (heven : levelSize l % 2 = 0) :
    levelFrontierCount positions l + levelMarkedCount positions l =
      2 * levelMarkedCount positions (l + 1) := by
  unfold levelFrontierCount levelMarkedCount
  have hstep : levelSize (l + 1) = (levelSize l + 1) / 2 := levelSize_step l (by omega)
  set k := levelSize l / 2
  have hk : levelSize l = 2 * k := by omega
  have hnext : levelSize (l + 1) = k := by rw [hstep]; omega
  rw [hnext, card_filter_eq_sum, card_filter_eq_sum, card_filter_eq_sum,
    Finset.mul_sum, hk, sum_range_pairs, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  have hq' : q < k := Finset.mem_range.mp hq
  have hpair : 2 * q + 1 < levelSize l := by omega
  rw [capMark_succ positions l q hl, if_pos hpair]
  cases capMark positions l (2 * q) <;> cases capMark positions l (2 * q + 1) <;> decide

theorem frontier_add_marked_odd (positions : Positions) (l : Nat) (hl : 14 ≤ l)
    (hodd : levelSize l % 2 = 1) :
    let p := if capMark positions l (levelSize l - 1) = true then 1 else 0
    levelFrontierCount positions l + levelMarkedCount positions l + p =
      2 * levelMarkedCount positions (l + 1) ∧
    levelMarkedCount positions (l + 1) ≤ levelSize l / 2 + p := by
  dsimp only
  unfold levelFrontierCount levelMarkedCount
  have hstep : levelSize (l + 1) = (levelSize l + 1) / 2 := levelSize_step l (by omega)
  set k := levelSize l / 2
  have hk : levelSize l = 2 * k + 1 := by omega
  have hsub : levelSize l - 1 = 2 * k := by omega
  have hnext : levelSize (l + 1) = k + 1 := by rw [hstep]; omega
  rw [hnext, hsub, card_filter_eq_sum, card_filter_eq_sum, card_filter_eq_sum,
    Finset.sum_range_succ, hk, Finset.sum_range_succ, sum_range_pairs]
  have hprom : capMark positions (l + 1) k = capMark positions l (2 * k) := by
    rw [capMark_succ positions l k hl, if_neg (by omega), if_pos (by omega)]
  have hpairs :
      ∑ q ∈ Finset.range k,
        (if (capMark positions l (2 * q) != capMark positions l (2 * q + 1)) = true then 1 else 0) +
      ∑ q ∈ Finset.range k,
        ((if capMark positions l (2 * q) = true then 1 else 0) +
         (if capMark positions l (2 * q + 1) = true then 1 else 0)) =
      2 * ∑ q ∈ Finset.range k, if capMark positions (l + 1) q = true then 1 else 0 := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    have hq' : q < k := Finset.mem_range.mp hq
    have hpair : 2 * q + 1 < levelSize l := by omega
    rw [capMark_succ positions l q hl, if_pos hpair]
    cases capMark positions l (2 * q) <;> cases capMark positions l (2 * q + 1) <;> decide
  have hle : (∑ q ∈ Finset.range k, if capMark positions (l + 1) q = true then 1 else 0) ≤ k := by
    calc
      ∑ q ∈ Finset.range k, (if capMark positions (l + 1) q = true then 1 else 0)
        ≤ ∑ _q ∈ Finset.range k, 1 := Finset.sum_le_sum fun _ _ => by split_ifs <;> omega
      _ = k := by simp
  rw [hprom]
  omega

/-- Universal cap frontier bound: at most 342 frontier digests for every subset of positions. -/
theorem cap_frontier_le_342 (positions : Positions) :
    capFrontierCount positions ≤ 342 := by
  have h14 : levelFrontierCount positions 14 + levelUnmarkedCount positions 15 ≤ 342 := by
    unfold levelFrontierCount levelUnmarkedCount
    have h14s : levelSize 14 / 2 = 341 := by decide
    have h15s : levelSize 15 = 342 := by decide
    rw [h14s, h15s, card_filter_eq_sum, card_filter_eq_sum]
    conv_lhs => rhs; rw [show (342 : Nat) = 341 + 1 from rfl, Finset.sum_range_succ]
    rw [← Nat.add_assoc, ← Finset.sum_add_distrib]
    have hp : ∑ q ∈ Finset.range 341,
        ((if (capMark positions 14 (2 * q) != capMark positions 14 (2 * q + 1)) = true then 1 else 0) +
         (if (!capMark positions 15 q) = true then 1 else 0)) ≤ 341 := by
      calc
        _ ≤ ∑ _q ∈ Finset.range 341, 1 := by
            apply Finset.sum_le_sum; intro q hq
            have hq' : q < 341 := Finset.mem_range.mp hq
            have h15q : capMark positions 15 q =
                (capMark positions 14 (2 * q) || capMark positions 14 (2 * q + 1)) := by
              rw [capMark_succ positions 14 q (by omega)]
              simp [levelSize_14, show 2 * q + 1 < 683 by omega]
            rw [h15q]
            cases capMark positions 14 (2 * q) <;> cases capMark positions 14 (2 * q + 1) <;> decide
        _ = 341 := by simp
    have hlast : (if (!capMark positions 15 341) = true then 1 else 0) ≤ 1 := by split_ifs <;> omega
    omega
  have h15 := frontier_add_unmarked_succ positions 15 (by omega)
  have h16 := frontier_add_unmarked_succ positions 16 (by omega)
  have h17 := frontier_add_unmarked_succ positions 17 (by omega)
  have h18 := frontier_add_unmarked_succ positions 18 (by omega)
  have h19 := frontier_add_unmarked_succ positions 19 (by omega)
  have h20 := frontier_add_unmarked_succ positions 20 (by omega)
  have h21 := frontier_add_unmarked_succ positions 21 (by omega)
  have h22 := frontier_add_unmarked_succ positions 22 (by omega)
  have h23 := frontier_add_unmarked_succ positions 23 (by omega)
  simp only [Nat.reduceAdd] at h15 h16 h17 h18 h19 h20 h21 h22 h23
  have hsum : capFrontierCount positions =
      levelFrontierCount positions 14 + levelFrontierCount positions 15 +
      levelFrontierCount positions 16 + levelFrontierCount positions 17 +
      levelFrontierCount positions 18 + levelFrontierCount positions 19 +
      levelFrontierCount positions 20 + levelFrontierCount positions 21 +
      levelFrontierCount positions 22 + levelFrontierCount positions 23 := by
    unfold capFrontierCount
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.zero_add, Nat.reduceAdd]
  omega

/-- Marked nodes never increase going up the cap tree. -/
theorem levelMarked_succ_le (positions : Positions) (l : Nat) (hl : 14 ≤ l) :
    levelMarkedCount positions (l + 1) ≤ levelMarkedCount positions l := by
  unfold levelMarkedCount
  have hstep : levelSize (l + 1) = (levelSize l + 1) / 2 := levelSize_step l (by omega)
  rw [hstep, card_filter_eq_sum, card_filter_eq_sum]
  rcases Nat.even_or_odd' (levelSize l) with ⟨k, hk | hk⟩
  · have hnext : (levelSize l + 1) / 2 = k := by omega
    rw [hnext, hk, sum_range_pairs]
    apply Finset.sum_le_sum
    intro q hq
    have hq' : q < k := Finset.mem_range.mp hq
    have hpair : 2 * q + 1 < levelSize l := by omega
    rw [capMark_succ positions l q hl, if_pos hpair]
    cases capMark positions l (2 * q) <;> cases capMark positions l (2 * q + 1) <;> decide
  · have hnext : (levelSize l + 1) / 2 = k + 1 := by omega
    rw [hnext, Finset.sum_range_succ, hk, Finset.sum_range_succ, sum_range_pairs]
    have hpairSum :
        ∑ q ∈ Finset.range k, (if capMark positions (l + 1) q = true then 1 else 0) ≤
        ∑ q ∈ Finset.range k,
          ((if capMark positions l (2 * q) = true then 1 else 0) +
           (if capMark positions l (2 * q + 1) = true then 1 else 0)) := by
      apply Finset.sum_le_sum
      intro q hq
      have hq' : q < k := Finset.mem_range.mp hq
      have hpair : 2 * q + 1 < levelSize l := by omega
      rw [capMark_succ positions l q hl, if_pos hpair]
      cases capMark positions l (2 * q) <;> cases capMark positions l (2 * q + 1) <;> decide
    have hprom : capMark positions (l + 1) k = capMark positions l (2 * k) := by
      rw [capMark_succ positions l k hl, if_neg (by omega), if_pos (by omega)]
    rw [hprom]
    omega

theorem levelMarked_14_le_card (positions : Positions) :
    levelMarkedCount positions 14 ≤ positions.card := by
  unfold levelMarkedCount
  have hsub : (Finset.range (levelSize 14)).filter (fun idx => capMark positions 14 idx = true) ⊆
      positions.image capLeafOf := by
    intro idx hidx
    simp only [Finset.mem_filter, capMark_14, decide_eq_true_eq] at hidx
    obtain ⟨_, i, hi, rfl⟩ := hidx
    exact Finset.mem_image_of_mem capLeafOf hi
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

theorem levelMarked_le_card (positions : Positions) (l : Nat) (hl : 14 ≤ l) :
    levelMarkedCount positions l ≤ positions.card := by
  obtain ⟨d, rfl⟩ : ∃ d, l = 14 + d := ⟨l - 14, by omega⟩
  clear hl
  induction d with
  | zero => exact levelMarked_14_le_card positions
  | succ d ih =>
    exact (levelMarked_succ_le positions (14 + d) (by omega)).trans ih

/-- Exact tight C=14 cap frontier bit bound for `positions.card = 128`: `capFrontierBits ≤ 68,904`! -/
theorem capFrontierBits_128_le (positions : Positions) (hcard : positions.card = BATCH) :
    capFrontierBits positions ≤ 68904 := by
  have hm15_le_14 := levelMarked_succ_le positions 14 (by omega)
  have hm16_le : levelMarkedCount positions 16 ≤ 128 := by
    have := levelMarked_le_card positions 16 (by omega); rw [hcard] at this; exact this
  have ⟨h14_eq, _⟩ := frontier_add_marked_odd positions 14 (by omega) (by decide)
  have h15_eq := frontier_add_marked_even positions 15 (by omega) (by decide)
  have ⟨h16_eq, hm17_le⟩ := frontier_add_marked_odd positions 16 (by omega) (by decide)
  have h16_div : levelSize 16 / 2 = 85 := by decide
  rw [h16_div] at hm17_le
  have h17 := frontier_add_unmarked_succ positions 17 (by omega)
  have h18 := frontier_add_unmarked_succ positions 18 (by omega)
  have h19 := frontier_add_unmarked_succ positions 19 (by omega)
  have h20 := frontier_add_unmarked_succ positions 20 (by omega)
  have h21 := frontier_add_unmarked_succ positions 21 (by omega)
  have h22 := frontier_add_unmarked_succ positions 22 (by omega)
  have h23 := frontier_add_unmarked_succ positions 23 (by omega)
  simp only [Nat.reduceAdd] at hm15_le_14 h14_eq h15_eq h16_eq hm17_le h17 h18 h19 h20 h21 h22 h23
  have hmu17 : levelMarkedCount positions 17 + levelUnmarkedCount positions 17 = 86 := by
    simpa [levelSize_17] using levelMarked_add_unmarked positions 17
  have hsum : capFrontierBits positions =
      230 * levelFrontierCount positions 14 +
      230 * levelFrontierCount positions 15 +
      233 * levelFrontierCount positions 16 +
      238 * (levelFrontierCount positions 17 + levelFrontierCount positions 18 +
             levelFrontierCount positions 19 + levelFrontierCount positions 20 +
             levelFrontierCount positions 21 + levelFrontierCount positions 22 +
             levelFrontierCount positions 23) := by
    unfold capFrontierBits
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.zero_add, Nat.reduceAdd, levelWidth]
    omega
  omega

theorem capFrontierBits_universal_le (positions : Positions) :
    capFrontierBits positions ≤ 238 * 342 := by
  have hle : capFrontierBits positions ≤ 238 * capFrontierCount positions := by
    unfold capFrontierBits capFrontierCount
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro step hstep
    have hs : step < 10 := Finset.mem_range.mp hstep
    have hw : levelWidth (14 + step) ≤ 238 := by interval_cases step <;> decide
    exact Nat.mul_le_mul_right _ hw
  exact hle.trans (Nat.mul_le_mul_left 238 (cap_frontier_le_342 positions))

/-! ### Exact Two-End Variable-Bit Tail Stream Proof Serialization and Size Bounds -/

def bitsToBytes {w : Nat} (v : BitVec w) (n : Nat) : List Byte :=
  (List.range n).map fun j => v.extractLsb' (8 * j) 8

theorem bitsToBytes_length {w : Nat} (v : BitVec w) (n : Nat) :
    (bitsToBytes v n).length = n := by
  simp [bitsToBytes]

/-- Variable-width tail chunk `(bits, val)` with `bits < 8` and `val < 2 ^ bits`. -/
abbrev TailChunk := Nat × Nat

def tailChunkOf (l : Nat) (d : Digest) : TailChunk :=
  (levelTailBits l, (d.extractLsb' (8 * levelBodyBytes l) (levelTailBits l)).toNat)

theorem tailChunkOf_valid (l : Nat) (d : Digest) :
    (tailChunkOf l d).1 < 8 ∧ (tailChunkOf l d).2 < 2 ^ (tailChunkOf l d).1 :=
  ⟨levelTailBits_lt_8 l, (d.extractLsb' (8 * levelBodyBytes l) (levelTailBits l)).isLt⟩

def totalTailBits (chunks : List TailChunk) : Nat :=
  (chunks.map Prod.fst).sum

/-- Little-endian integer encoding of a list of variable-width tail chunks. -/
def bitsOfVar (chunks : List TailChunk) : Nat :=
  chunks.foldr (fun c acc => c.2 + 2 ^ c.1 * acc) 0

/-- Little-endian integer encoding of a list of bytes (`8 * bs.length` bits). -/
def bytesToNat (bs : List Byte) : Nat :=
  bs.foldr (fun b acc => b.toNat + 256 * acc) 0

theorem totalTailBits_nil : totalTailBits [] = 0 := rfl
theorem totalTailBits_cons (c : TailChunk) (cs : List TailChunk) :
    totalTailBits (c :: cs) = c.1 + totalTailBits cs := rfl
theorem totalTailBits_append (a b : List TailChunk) :
    totalTailBits (a ++ b) = totalTailBits a + totalTailBits b := by
  simp [totalTailBits]

theorem bitsOfVar_nil : bitsOfVar [] = 0 := rfl
theorem bitsOfVar_cons (c : TailChunk) (cs : List TailChunk) :
    bitsOfVar (c :: cs) = c.2 + 2 ^ c.1 * bitsOfVar cs := rfl

theorem bitsOfVar_append_singleton (cs : List TailChunk) (c : TailChunk) :
    bitsOfVar (cs ++ [c]) = bitsOfVar cs + c.2 * 2 ^ totalTailBits cs := by
  induction cs with
  | nil => simp [bitsOfVar, totalTailBits]
  | cons a rest ih =>
    simp only [List.cons_append, bitsOfVar_cons, ih, totalTailBits_cons, Nat.pow_add]
    ring

theorem bytesToNat_nil : bytesToNat [] = 0 := rfl
theorem bytesToNat_cons (b : Byte) (bs : List Byte) :
    bytesToNat (b :: bs) = b.toNat + 256 * bytesToNat bs := rfl

theorem bytesToNat_append_singleton (bs : List Byte) (b : Byte) :
    bytesToNat (bs ++ [b]) = bytesToNat bs + b.toNat * 2 ^ (8 * bs.length) := by
  induction bs with
  | nil => simp [bytesToNat]
  | cons a rest ih =>
    simp only [List.cons_append, bytesToNat_cons, ih, List.length_cons]
    have hpow : 256 * 2 ^ (8 * rest.length) = 2 ^ (8 * (rest.length + 1)) := by
      rw [show 8 * (rest.length + 1) = 8 + 8 * rest.length by omega, Nat.pow_add]
    calc
      a.toNat + 256 * (bytesToNat rest + b.toNat * 2 ^ (8 * rest.length))
        = (a.toNat + 256 * bytesToNat rest) + b.toNat * (256 * 2 ^ (8 * rest.length)) := by ring
      _ = (a.toNat + 256 * bytesToNat rest) + b.toNat * 2 ^ (8 * (rest.length + 1)) := by rw [hpow]

/-- Exact streaming variable-bit (`bits < 8`) LSB-first packer state `(emittedBytes, bitBuf, bitCnt)`. -/
def packVarStep (st : List Byte × Nat × Nat) (c : TailChunk) : List Byte × Nat × Nat :=
  let (acc, buf, cnt) := st
  if c.1 = 0 then (acc, buf, cnt)
  else
    let buf' := buf + c.2 * 2 ^ cnt
    let cnt' := cnt + c.1
    if 8 ≤ cnt' then
      (acc ++ [BitVec.ofNat 8 buf'], buf' / 256, cnt' - 8)
    else
      (acc, buf', cnt')

def packVarFinish (st : List Byte × Nat × Nat) : List Byte :=
  let (acc, buf, cnt) := st
  if 0 < cnt then acc ++ [BitVec.ofNat 8 buf] else acc

def packVarBits (chunks : List TailChunk) : List Byte :=
  packVarFinish (chunks.foldl packVarStep ([], 0, 0))

/-- Reversed packed variable-bit tail stream appended to the end of the proof for backward reading. -/
def packVarBitsRev (chunks : List TailChunk) : List Byte :=
  (packVarBits chunks).reverse

private theorem packVarStep_inv (acc : List Byte) (buf cnt tot v : Nat) (c : TailChunk)
    (hc1 : c.1 < 8) (hc2 : c.2 < 2 ^ c.1)
    (hcnt : cnt < 8) (hbuf : buf < 2 ^ cnt)
    (hbits : 8 * acc.length + cnt = tot)
    (hval : bytesToNat acc + 2 ^ (8 * acc.length) * buf = v) :
    let (acc', buf', cnt') := packVarStep (acc, buf, cnt) c
    cnt' < 8 ∧ buf' < 2 ^ cnt' ∧
    8 * acc'.length + cnt' = tot + c.1 ∧
    bytesToNat acc' + 2 ^ (8 * acc'.length) * buf' = v + c.2 * 2 ^ tot := by
  unfold packVarStep
  dsimp only
  split_ifs with hzero hge
  · have hc2z : c.2 = 0 := by rw [hzero] at hc2; simpa using hc2
    rw [hzero, hc2z]; simpa using And.intro hcnt (And.intro hbuf (And.intro hbits hval))
  · dsimp only
    have hbuf' : buf + c.2 * 2 ^ cnt < 2 ^ (cnt + c.1) := by
      rw [Nat.pow_add]
      have hle : c.2 ≤ 2 ^ c.1 - 1 := by omega
      have hpos : 1 ≤ 2 ^ c.1 := Nat.one_le_two_pow
      calc
        buf + c.2 * 2 ^ cnt < 2 ^ cnt + (2 ^ c.1 - 1) * 2 ^ cnt := by
          have hm := Nat.mul_le_mul_right (2 ^ cnt) hle; omega
        _ = (1 + (2 ^ c.1 - 1)) * 2 ^ cnt := by ring
        _ = 2 ^ c.1 * 2 ^ cnt := by rw [Nat.add_sub_of_le hpos]
        _ = 2 ^ cnt * 2 ^ c.1 := by ring
    have hterm : 2 ^ (8 * acc.length) * (buf + c.2 * 2 ^ cnt) =
        2 ^ (8 * acc.length) * buf + c.2 * 2 ^ tot := by
      rw [Nat.mul_add, ← hbits, Nat.pow_add]; ring
    refine ⟨by omega, ?_, ?_, ?_⟩
    · rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 256)]
      rw [show 2 ^ (cnt + c.1 - 8) * 256 = 2 ^ (cnt + c.1) by
        rw [show 256 = 2 ^ 8 by decide, ← Nat.pow_add, show cnt + c.1 - 8 + 8 = cnt + c.1 by omega]]
      exact hbuf'
    · simp only [List.length_append, List.length_singleton]; omega
    · rw [bytesToNat_append_singleton, List.length_append, List.length_singleton]
      have hof : (BitVec.ofNat 8 (buf + c.2 * 2 ^ cnt)).toNat = (buf + c.2 * 2 ^ cnt) % 256 := by
        simp [BitVec.toNat_ofNat]
      rw [hof]
      have hpow : 2 ^ (8 * (acc.length + 1)) = 2 ^ (8 * acc.length) * 256 := by
        rw [show 8 * (acc.length + 1) = 8 * acc.length + 8 by omega, Nat.pow_add]
      rw [hpow]
      have hdm : (buf + c.2 * 2 ^ cnt) % 256 + 256 * ((buf + c.2 * 2 ^ cnt) / 256) =
          buf + c.2 * 2 ^ cnt := by omega
      calc
        bytesToNat acc + (buf + c.2 * 2 ^ cnt) % 256 * 2 ^ (8 * acc.length) +
            2 ^ (8 * acc.length) * 256 * ((buf + c.2 * 2 ^ cnt) / 256)
          = bytesToNat acc + 2 ^ (8 * acc.length) *
              ((buf + c.2 * 2 ^ cnt) % 256 + 256 * ((buf + c.2 * 2 ^ cnt) / 256)) := by ring
        _ = bytesToNat acc + 2 ^ (8 * acc.length) * (buf + c.2 * 2 ^ cnt) := by rw [hdm]
        _ = bytesToNat acc + 2 ^ (8 * acc.length) * buf + c.2 * 2 ^ tot := by rw [hterm, Nat.add_assoc]
        _ = v + c.2 * 2 ^ tot := by rw [hval]
  · dsimp only
    have hbuf' : buf + c.2 * 2 ^ cnt < 2 ^ (cnt + c.1) := by
      rw [Nat.pow_add]
      have hle : c.2 ≤ 2 ^ c.1 - 1 := by omega
      have hpos : 1 ≤ 2 ^ c.1 := Nat.one_le_two_pow
      calc
        buf + c.2 * 2 ^ cnt < 2 ^ cnt + (2 ^ c.1 - 1) * 2 ^ cnt := by
          have hm := Nat.mul_le_mul_right (2 ^ cnt) hle; omega
        _ = (1 + (2 ^ c.1 - 1)) * 2 ^ cnt := by ring
        _ = 2 ^ c.1 * 2 ^ cnt := by rw [Nat.add_sub_of_le hpos]
        _ = 2 ^ cnt * 2 ^ c.1 := by ring
    have hterm : 2 ^ (8 * acc.length) * (buf + c.2 * 2 ^ cnt) =
        2 ^ (8 * acc.length) * buf + c.2 * 2 ^ tot := by
      rw [Nat.mul_add, ← hbits, Nat.pow_add]; ring
    refine ⟨by omega, hbuf', by omega, ?_⟩
    rw [hterm, ← Nat.add_assoc, hval]

private theorem packVar_foldl_inv (chunks : List TailChunk)
    (hvalid : ∀ c ∈ chunks, c.1 < 8 ∧ c.2 < 2 ^ c.1) :
    ∀ acc buf cnt prev,
      cnt < 8 → buf < 2 ^ cnt →
      8 * acc.length + cnt = totalTailBits prev →
      bytesToNat acc + 2 ^ (8 * acc.length) * buf = bitsOfVar prev →
      let (acc', buf', cnt') := chunks.foldl packVarStep (acc, buf, cnt)
      cnt' < 8 ∧ buf' < 2 ^ cnt' ∧
      8 * acc'.length + cnt' = totalTailBits (prev ++ chunks) ∧
      bytesToNat acc' + 2 ^ (8 * acc'.length) * buf' = bitsOfVar (prev ++ chunks) := by
  induction chunks with
  | nil =>
    intro acc buf cnt prev hcnt hbuf hbits hval
    simpa using And.intro hcnt (And.intro hbuf (And.intro hbits hval))
  | cons c rest ih =>
    intro acc buf cnt prev hcnt hbuf hbits hval
    simp only [List.foldl_cons]
    have hc := hvalid c (by simp)
    have hstep := packVarStep_inv acc buf cnt (totalTailBits prev) (bitsOfVar prev) c
      hc.1 hc.2 hcnt hbuf hbits hval
    rcases hst : packVarStep (acc, buf, cnt) c with ⟨acc1, buf1, cnt1⟩
    rw [hst] at hstep
    rcases hstep with ⟨hcnt1, hbuf1, hbits1, hval1⟩
    have htot1 : totalTailBits (prev ++ [c]) = totalTailBits prev + c.1 := by
      simp [totalTailBits]
    have hbits1' : 8 * acc1.length + cnt1 = totalTailBits (prev ++ [c]) := by rw [htot1]; exact hbits1
    have hval1' : bytesToNat acc1 + 2 ^ (8 * acc1.length) * buf1 = bitsOfVar (prev ++ [c]) := by
      rw [bitsOfVar_append_singleton]; exact hval1
    have hres := ih (fun x hx => hvalid x (by simp [hx])) acc1 buf1 cnt1 (prev ++ [c]) hcnt1 hbuf1 hbits1' hval1'
    simpa only [List.append_assoc, List.singleton_append] using hres

theorem packVarBits_spec (chunks : List TailChunk)
    (hvalid : ∀ c ∈ chunks, c.1 < 8 ∧ c.2 < 2 ^ c.1) :
    (packVarBits chunks).length = (totalTailBits chunks + 7) / 8 ∧
    bytesToNat (packVarBits chunks) = bitsOfVar chunks := by
  have h := packVar_foldl_inv chunks hvalid [] 0 0 [] (by omega) (by decide)
    (by simp [totalTailBits]) (by simp [bytesToNat, bitsOfVar])
  unfold packVarBits packVarFinish
  rcases hfold : chunks.foldl packVarStep ([], 0, 0) with ⟨acc, buf, cnt⟩
  rw [hfold] at h
  simp only [List.nil_append] at h
  rcases h with ⟨hcnt, hbuf, hbits, hval⟩
  dsimp only
  split_ifs with hpos
  · constructor
    · simp only [List.length_append, List.length_singleton]; omega
    · rw [bytesToNat_append_singleton]
      have hbuf256 : buf < 256 := by
        have hle : 2 ^ cnt ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
        have : 2 ^ 7 = 128 := by decide
        omega
      have hof : (BitVec.ofNat 8 buf).toNat = buf := by
        simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbuf256]
      rw [hof, Nat.mul_comm buf]
      exact hval
  · have hcnt0 : cnt = 0 := by omega
    subst hcnt0
    have hbuf0 : buf = 0 := by omega
    subst hbuf0
    constructor
    · omega
    · simpa using hval

theorem packVarBitsRev_length (chunks : List TailChunk)
    (hvalid : ∀ c ∈ chunks, c.1 < 8 ∧ c.2 < 2 ^ c.1) :
    (packVarBitsRev chunks).length = (totalTailBits chunks + 7) / 8 := by
  unfold packVarBitsRev
  rw [List.length_reverse]
  exact (packVarBits_spec chunks hvalid).1

theorem packVarBits_bytesToNat (chunks : List TailChunk)
    (hvalid : ∀ c ∈ chunks, c.1 < 8 ∧ c.2 < 2 ^ c.1) :
    bytesToNat (packVarBits chunks) = bitsOfVar chunks :=
  (packVarBits_spec chunks hvalid).2

def l0SiblingsProof (nodes : Nat → Nat → Digest) (i : Index) : List Byte :=
  let g := i.val / 3
  let r := i.val % 3
  if g = FULL_TRIPLETS then []
  else if r = 0 then bitsToBytes (nodes 0 (3 * g + 1)) 32 ++ bitsToBytes (nodes 0 (3 * g + 2)) 32
  else if r = 1 then bitsToBytes (nodes 0 (3 * g)) 32 ++ bitsToBytes (nodes 0 (3 * g + 2)) 32
  else bitsToBytes (nodes 0 (3 * g)) 32 ++ bitsToBytes (nodes 0 (3 * g + 1)) 32

/-- Forward bytes of `L2..L13` siblings (`levelBodyBytes l` bytes each). -/
def binPathFwd (nodes : Nat → Nat → Digest) (g : Nat) : List Byte :=
  (List.range 12).flatMap fun step =>
    let l := 2 + step
    let idx := g >>> (step + 1)
    let sib := idx ^^^ 1
    if sib < levelSize l then bitsToBytes (nodes l sib) (levelBodyBytes l) else []

/-- Variable-width tail chunks of `L2..L13` siblings in canonical order. -/
def binPathTails (nodes : Nat → Nat → Digest) (g : Nat) : List TailChunk :=
  (List.range 12).flatMap fun step =>
    let l := 2 + step
    let idx := g >>> (step + 1)
    let sib := idx ^^^ 1
    if sib < levelSize l then [tailChunkOf l (nodes l sib)] else []

def recordFwd (nodes : Nat → Nat → Digest) (salts : Index → Salt192) (i : Index) : List Byte :=
  let g := i.val / 3
  bitsToBytes (salts i) 24 ++
  l0SiblingsProof nodes i ++
  bitsToBytes (nodes 1 (g ^^^ 1)) 32 ++
  binPathFwd nodes g

def recordTails (nodes : Nat → Nat → Digest) (i : Index) : List TailChunk :=
  binPathTails nodes (i.val / 3)

def capLevelFrontierFwd (nodes : Nat → Nat → Digest) (positions : Positions) (l : Nat) : List Byte :=
  (List.range (levelSize l / 2)).flatMap fun q =>
    let mL := capMark positions l (2 * q)
    let mR := capMark positions l (2 * q + 1)
    if mL = mR then []
    else if !mL then bitsToBytes (nodes l (2 * q)) (levelBodyBytes l)
    else bitsToBytes (nodes l (2 * q + 1)) (levelBodyBytes l)

def capLevelFrontierTails (nodes : Nat → Nat → Digest) (positions : Positions) (l : Nat) : List TailChunk :=
  (List.range (levelSize l / 2)).flatMap fun q =>
    let mL := capMark positions l (2 * q)
    let mR := capMark positions l (2 * q + 1)
    if mL = mR then []
    else if !mL then [tailChunkOf l (nodes l (2 * q))]
    else [tailChunkOf l (nodes l (2 * q + 1))]

def capFrontierFwd (nodes : Nat → Nat → Digest) (positions : Positions) : List Byte :=
  (List.range 10).flatMap fun step => capLevelFrontierFwd nodes positions (14 + step)

def capFrontierTails (nodes : Nat → Nat → Digest) (positions : Positions) : List TailChunk :=
  (List.range 10).flatMap fun step => capLevelFrontierTails nodes positions (14 + step)

def referenceProofFwd (nodes : Nat → Nat → Digest) (salts : Index → Salt192)
    (positions : Positions) : List Byte :=
  (positions.sort (· ≤ ·)).flatMap (recordFwd nodes salts) ++
  capFrontierFwd nodes positions

def referenceProofTails (nodes : Nat → Nat → Digest) (positions : Positions) : List TailChunk :=
  (positions.sort (· ≤ ·)).flatMap (recordTails nodes) ++
  capFrontierTails nodes positions

def referenceProof (nodes : Nat → Nat → Digest) (salts : Index → Salt192)
    (positions : Positions) : Proof :=
  if positions.card = 0 then []
  else
    referenceProofFwd nodes salts positions ++
    packVarBitsRev (referenceProofTails nodes positions)

theorem referenceProofTails_valid (nodes : Nat → Nat → Digest) (positions : Positions) :
    ∀ c ∈ referenceProofTails nodes positions, c.1 < 8 ∧ c.2 < 2 ^ c.1 := by
  intro c hc
  unfold referenceProofTails at hc
  rcases List.mem_append.mp hc with h1 | h2
  · rw [List.mem_flatMap] at h1
    obtain ⟨i, _, hi⟩ := h1
    unfold recordTails binPathTails at hi
    rw [List.mem_flatMap] at hi
    obtain ⟨step, _, hstep⟩ := hi
    dsimp only at hstep
    split_ifs at hstep
    · simp only [List.mem_singleton] at hstep; subst hstep; exact tailChunkOf_valid _ _
    · simp at hstep
  · unfold capFrontierTails at h2
    rw [List.mem_flatMap] at h2
    obtain ⟨step, _, hstep⟩ := h2
    unfold capLevelFrontierTails at hstep
    rw [List.mem_flatMap] at hstep
    obtain ⟨q, _, hq⟩ := hstep
    dsimp only at hq
    split_ifs at hq
    · simp at hq
    · simp only [List.mem_singleton] at hq; subst hq; exact tailChunkOf_valid _ _
    · simp only [List.mem_singleton] at hq; subst hq; exact tailChunkOf_valid _ _

private theorem list_map_sum_le {α : Type} (l : List α) (f g : α → Nat)
    (h : ∀ x ∈ l, f x ≤ g x) : (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    simp only [List.map_cons, List.sum_cons]
    have ha := h a (by simp)
    have hrest := ih (fun x hx => h x (by simp [hx]))
    omega

private theorem list_sum_range (n : Nat) (f : Nat → Nat) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
      ih, Finset.sum_range_succ]

private theorem totalTailBits_flatMap {α : Type} (l : List α) (f : α → List TailChunk) :
    totalTailBits (l.flatMap f) = (l.map (fun x => totalTailBits (f x))).sum := by
  induction l with
  | nil => simp [totalTailBits]
  | cons a rest ih =>
    simp only [List.flatMap_cons, totalTailBits_append, ih, List.map_cons, List.sum_cons]

theorem l0SiblingsProof_length_le (nodes : Nat → Nat → Digest) (i : Index) :
    (l0SiblingsProof nodes i).length ≤ 64 := by
  unfold l0SiblingsProof; dsimp only; split_ifs <;> simp [bitsToBytes]

theorem binPath_bits_le (nodes : Nat → Nat → Digest) (g : Nat) :
    8 * (binPathFwd nodes g).length + totalTailBits (binPathTails nodes g) ≤ 2837 := by
  unfold binPathFwd binPathTails
  rw [List.length_flatMap, totalTailBits_flatMap]
  dsimp only
  have h1 : (List.map (fun step => (if ((g >>> (step + 1)) ^^^ 1) < levelSize (2 + step)
      then bitsToBytes (nodes (2 + step) ((g >>> (step + 1)) ^^^ 1)) (levelBodyBytes (2 + step)) else []).length)
      (List.range 12)).sum ≤
      ((List.range 12).map (fun step => levelBodyBytes (2 + step))).sum :=
    list_map_sum_le _ _ _ (fun step _ => by split <;> simp [bitsToBytes])
  have h2 : (List.map (fun step => totalTailBits (if ((g >>> (step + 1)) ^^^ 1) < levelSize (2 + step)
      then [tailChunkOf (2 + step) (nodes (2 + step) ((g >>> (step + 1)) ^^^ 1))] else []))
      (List.range 12)).sum ≤
      ((List.range 12).map (fun step => levelTailBits (2 + step))).sum :=
    list_map_sum_le _ _ _ (fun step _ => by split <;> simp [totalTailBits, tailChunkOf])
  have hc1 : ((List.range 12).map (fun step => levelBodyBytes (2 + step))).sum = 350 := by decide
  have hc2 : ((List.range 12).map (fun step => levelTailBits (2 + step))).sum = 37 := by decide
  omega

theorem record_bits_le (nodes : Nat → Nat → Digest) (salts : Index → Salt192) (i : Index) :
    8 * (recordFwd nodes salts i).length + totalTailBits (recordTails nodes i) ≤ 3797 := by
  unfold recordFwd recordTails
  simp only [List.length_append, bitsToBytes_length]
  have h0 := l0SiblingsProof_length_le nodes i
  have h1 := binPath_bits_le nodes (i.val / 3)
  omega

theorem capLevelFrontierFwd_length (nodes : Nat → Nat → Digest) (positions : Positions) (l : Nat) :
    (capLevelFrontierFwd nodes positions l).length = levelBodyBytes l * levelFrontierCount positions l := by
  unfold capLevelFrontierFwd levelFrontierCount
  rw [List.length_flatMap, card_filter_eq_sum, Finset.mul_sum, list_sum_range]
  apply Finset.sum_congr rfl
  intro q _
  dsimp only
  cases capMark positions l (2 * q) <;> cases capMark positions l (2 * q + 1) <;> simp [bitsToBytes]

theorem capLevelFrontierTails_bits (nodes : Nat → Nat → Digest) (positions : Positions) (l : Nat) :
    totalTailBits (capLevelFrontierTails nodes positions l) = levelTailBits l * levelFrontierCount positions l := by
  unfold capLevelFrontierTails levelFrontierCount
  rw [totalTailBits_flatMap, card_filter_eq_sum, Finset.mul_sum, list_sum_range]
  apply Finset.sum_congr rfl
  intro q _
  dsimp only
  cases capMark positions l (2 * q) <;> cases capMark positions l (2 * q + 1) <;> simp [totalTailBits, tailChunkOf]

theorem capFrontier_total_bits (nodes : Nat → Nat → Digest) (positions : Positions) :
    8 * (capFrontierFwd nodes positions).length + totalTailBits (capFrontierTails nodes positions) =
      capFrontierBits positions := by
  unfold capFrontierFwd capFrontierTails capFrontierBits
  rw [List.length_flatMap, totalTailBits_flatMap, list_sum_range, list_sum_range,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro step _
  rw [capLevelFrontierFwd_length, capLevelFrontierTails_bits]
  have hw := levelBodyBytes_mul_add_tail (14 + step)
  calc
    8 * (levelBodyBytes (14 + step) * levelFrontierCount positions (14 + step)) +
        levelTailBits (14 + step) * levelFrontierCount positions (14 + step)
      = (8 * levelBodyBytes (14 + step) + levelTailBits (14 + step)) *
          levelFrontierCount positions (14 + step) := by ring
    _ = levelWidth (14 + step) * levelFrontierCount positions (14 + step) := by rw [hw]

theorem referenceProof_total_bits_le (nodes : Nat → Nat → Digest) (salts : Index → Salt192)
    (positions : Positions) :
    8 * (referenceProofFwd nodes salts positions).length +
      totalTailBits (referenceProofTails nodes positions) ≤
      3797 * positions.card + capFrontierBits positions := by
  unfold referenceProofFwd referenceProofTails
  rw [List.length_append, totalTailBits_append, List.length_flatMap, totalTailBits_flatMap,
    Nat.mul_add]
  have hcap := capFrontier_total_bits nodes positions
  have hrec : 8 * ((positions.sort (· ≤ ·)).map (fun i => (recordFwd nodes salts i).length)).sum +
      ((positions.sort (· ≤ ·)).map (fun i => totalTailBits (recordTails nodes i))).sum ≤
      3797 * positions.card := by
    have hcomb : ∀ l : List Index,
        8 * (l.map (fun i => (recordFwd nodes salts i).length)).sum +
        (l.map (fun i => totalTailBits (recordTails nodes i))).sum ≤ 3797 * l.length := by
      intro l; induction l with
      | nil => simp
      | cons a rest ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        have ha := record_bits_le nodes salts a
        omega
    simpa [Finset.length_sort] using hcomb (positions.sort (· ≤ ·))
  omega

theorem referenceProof_length_le_bits (nodes : Nat → Nat → Digest) (salts : Index → Salt192)
    (positions : Positions) :
    (referenceProof nodes salts positions).length ≤
      (3797 * positions.card + capFrontierBits positions + 7) / 8 := by
  unfold referenceProof
  split
  · simp
  · rw [List.length_append, packVarBitsRev_length _ (referenceProofTails_valid nodes positions)]
    have hb := referenceProof_total_bits_le nodes salts positions
    omega

theorem referenceProof_length_128_le (nodes : Nat → Nat → Digest) (salts : Index → Salt192)
    (positions : Positions) (hcard : positions.card = BATCH) :
    (referenceProof nodes salts positions).length ≤ 69365 := by
  have h := referenceProof_length_le_bits nodes salts positions
  have hcap := capFrontierBits_128_le positions hcard
  rw [hcard] at h
  change _ ≤ (3797 * 128 + capFrontierBits positions + 7) / 8 at h
  omega

theorem referenceProof_length_le_cap (nodes : Nat → Nat → Digest) (salts : Index → Salt192)
    (positions : Positions) :
    (referenceProof nodes salts positions).length ≤ proofCap := by
  have h := referenceProof_length_le_bits nodes salts positions
  have hcap := capFrontierBits_universal_le positions
  have hc : positions.card ≤ LENGTH := by
    simpa only [Index, Fintype.card_fin] using Finset.card_le_univ positions
  change positions.card ≤ 16777216 at hc
  change _ ≤ 8556390424
  omega

theorem xor_one_even (q : Nat) : (2 * q) ^^^ 1 = 2 * q + 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor]
  cases i with
  | zero => simp [Nat.testBit_zero]
  | succ j =>
    simp only [Nat.testBit_succ, show (1 : Nat) / 2 = 0 by decide, Nat.zero_testBit,
      Bool.xor_false, show 2 * q / 2 = q by omega, show (2 * q + 1) / 2 = q by omega]

theorem xor_one_odd (q : Nat) : (2 * q + 1) ^^^ 1 = 2 * q := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor]
  cases i with
  | zero => simp [Nat.testBit_zero]
  | succ j =>
    simp only [Nat.testBit_succ, show (1 : Nat) / 2 = 0 by decide, Nat.zero_testBit,
      Bool.xor_false, show 2 * q / 2 = q by omega, show (2 * q + 1) / 2 = q by omega]

theorem xor_one_lt_even {k m : Nat} (hk : k < 2 * m) : (k ^^^ 1) < 2 * m := by
  rcases Nat.even_or_odd' k with ⟨q, rfl | rfl⟩
  · rw [xor_one_even]; omega
  · rw [xor_one_odd]; omega

theorem referenceProof_congr_nodes (n1 n2 : Nat → Nat → Digest)
    (hagree : ∀ l ≤ 24, ∀ idx < levelSize l, n1 l idx = n2 l idx)
    (salts : Index → Salt192) (positions : Positions) :
    referenceProof n1 salts positions = referenceProof n2 salts positions := by
  unfold referenceProof
  split_ifs
  · rfl
  · refine congrArg₂ List.append ?_ (congrArg packVarBitsRev ?_)
    · unfold referenceProofFwd
      refine congrArg₂ List.append ?_ ?_
      · apply List.flatMap_congr; intro i _
        unfold recordFwd l0SiblingsProof binPathFwd
        dsimp only
        have h0 := hagree 0 (by omega)
        have h1 := hagree 1 (by omega)
        refine congrArg₂ List.append ?_ ?_
        · refine congrArg₂ List.append ?_ ?_
          · apply congrArg (bitsToBytes (salts i) 24 ++ ·)
            split_ifs
            · rfl
            · have hb1 : 3 * (i.val / 3) + 1 < levelSize 0 := by
                have := i.isLt; rw [levelSize_0, full_triplets_eq] at *; unfold LENGTH LOG_LENGTH at *; omega
              have hb2 : 3 * (i.val / 3) + 2 < levelSize 0 := by
                have := i.isLt; rw [levelSize_0, full_triplets_eq] at *; unfold LENGTH LOG_LENGTH at *; omega
              rw [h0 _ hb1, h0 _ hb2]
            · have hb0 : 3 * (i.val / 3) < levelSize 0 := by
                have := i.isLt; rw [levelSize_0, full_triplets_eq] at *; unfold LENGTH LOG_LENGTH at *; omega
              have hb2 : 3 * (i.val / 3) + 2 < levelSize 0 := by
                have := i.isLt; rw [levelSize_0, full_triplets_eq] at *; unfold LENGTH LOG_LENGTH at *; omega
              rw [h0 _ hb0, h0 _ hb2]
            · have hb0 : 3 * (i.val / 3) < levelSize 0 := by
                have := i.isLt; rw [levelSize_0, full_triplets_eq] at *; unfold LENGTH LOG_LENGTH at *; omega
              have hb1 : 3 * (i.val / 3) + 1 < levelSize 0 := by
                have := i.isLt; rw [levelSize_0, full_triplets_eq] at *; unfold LENGTH LOG_LENGTH at *; omega
              rw [h0 _ hb0, h0 _ hb1]
          · exact congrArg (fun d => bitsToBytes d 32) (h1 _ (by
              rw [levelSize_1]
              exact xor_one_lt_even (m := 2796203) (by
                have := i.isLt; unfold LENGTH LOG_LENGTH at this; omega)))
        · apply List.flatMap_congr; intro step hstep
          have hs : step < 12 := List.mem_range.mp hstep
          by_cases hlt : ((i.val / 3) >>> (step + 1) ^^^ 1) < levelSize (2 + step)
          · simp only [hlt, ite_true, hagree (2 + step) (by omega) _ hlt]
          · simp only [hlt, ite_false]
      · unfold capFrontierFwd capLevelFrontierFwd
        apply List.flatMap_congr; intro step hstep
        have hs : step < 10 := List.mem_range.mp hstep
        apply List.flatMap_congr; intro q hq
        have hq' : q < levelSize (14 + step) / 2 := List.mem_range.mp hq
        dsimp only
        split_ifs
        · rfl
        · rw [hagree (14 + step) (by omega) (2 * q) (by omega)]
        · rw [hagree (14 + step) (by omega) (2 * q + 1) (by omega)]
    · unfold referenceProofTails
      refine congrArg₂ List.append ?_ ?_
      · apply List.flatMap_congr; intro i _
        unfold recordTails binPathTails
        apply List.flatMap_congr; intro step hstep
        have hs : step < 12 := List.mem_range.mp hstep
        dsimp only
        split_ifs with hlt
        · rw [hagree (2 + step) (by omega) _ hlt]
        · rfl
      · unfold capFrontierTails capLevelFrontierTails
        apply List.flatMap_congr; intro step hstep
        have hs : step < 10 := List.mem_range.mp hstep
        apply List.flatMap_congr; intro q hq
        have hq' : q < levelSize (14 + step) / 2 := List.mem_range.mp hq
        dsimp only
        split_ifs
        · rfl
        · rw [hagree (14 + step) (by omega) (2 * q) (by omega)]
        · rw [hagree (14 + step) (by omega) (2 * q + 1) (by omega)]

end CommitGolfCandidate
