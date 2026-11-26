import CommitGolf.Parameters
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! Mathematical model of the r=2 3-ary-bottom, left-aligned binary, cap c=9 (456 cap leaves)
vector commitment tree with paired 192-bit late salts (shared-midpoint 40-byte pair rows),
256b/240b/238b digests (`L0..L4` 256b, `L5..L8` 240b, `L9..L22` 238b, `L23` root 256b),
and two-end 6-bit tail stream proofs.
Parameterized over any 768->256 compression function. -/
namespace CommitGolfCandidate
open CommitGolf

abbrev Salt192 := BitVec 192
abbrev PairRand := BitVec 320
abbrev Digest := BitVec 256
abbrev Comp96 := BitVec 768 → Digest

/-! ### 240-bit truncation (top 16 bits zeroed) -/

def low240 (d : Digest) : BitVec 240 := d.extractLsb' 0 240

def mask240 (d : Digest) : Digest := (0#16) ++ low240 d

theorem low240_mask240 (d : Digest) : low240 (mask240 d) = low240 d := by
  unfold low240 mask240
  exact BitVec.extractLsb'_append_eq_right

theorem mask240_idempotent (d : Digest) : mask240 (mask240 d) = mask240 d := by
  change (0#16) ++ low240 (mask240 d) = mask240 d
  rw [low240_mask240]
  rfl

theorem mask240_eq_iff (a b : Digest) : mask240 a = mask240 b ↔ low240 a = low240 b := by
  constructor
  · intro h
    have := congrArg low240 h
    simpa only [low240_mask240] using this
  · intro h
    simp only [mask240, h]

theorem mask240_getLsbD (d : Digest) (i : Nat) :
    (mask240 d).getLsbD i = (decide (i < 240) && d.getLsbD i) := by
  unfold mask240 low240
  rw [BitVec.getLsbD_append]
  by_cases hi : i < 240
  · simp [hi]
  · simp [hi]

theorem extractLsb'_192_mask240 (d : Digest) :
    (mask240 d).extractLsb' 0 192 = d.extractLsb' 0 192 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and, Nat.zero_add,
    mask240_getLsbD, show i < 240 by omega]

theorem mask240_byte_lt30 (d : Digest) (j : Nat) (hj : j < 30) :
    (mask240 d).extractLsb' (8 * j) 8 = d.extractLsb' (8 * j) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp only [BitVec.getLsbD_extractLsb', hb, decide_true, Bool.true_and, mask240_getLsbD,
    show 8 * j + b < 240 by omega]

theorem mask240_byte_ge30 (d : Digest) (j : Nat) (hj : 30 ≤ j) :
    (mask240 d).extractLsb' (8 * j) 8 = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  have hge : ¬ (8 * j + b < 240) := by omega
  simp [BitVec.getLsbD_extractLsb', hb, mask240_getLsbD, hge]

/-! ### 238-bit truncation (top 18 bits zeroed) and per-level masking (`L5..L8`: 240b, `L9..L22`: 238b) -/

def low238 (d : Digest) : BitVec 238 := d.extractLsb' 0 238

def mask238 (d : Digest) : Digest := (0#18) ++ low238 d

def tail6 (d : Digest) : BitVec 6 := d.extractLsb' 232 6

def maskLevel (l : Nat) (d : Digest) : Digest :=
  if l < 5 ∨ l = 23 then d else if l < 9 then mask240 d else mask238 d

theorem low238_mask238 (d : Digest) : low238 (mask238 d) = low238 d := by
  unfold low238 mask238
  exact BitVec.extractLsb'_append_eq_right

theorem mask238_idempotent (d : Digest) : mask238 (mask238 d) = mask238 d := by
  change (0#18) ++ low238 (mask238 d) = mask238 d
  rw [low238_mask238]
  rfl

theorem mask238_eq_iff (a b : Digest) : mask238 a = mask238 b ↔ low238 a = low238 b := by
  constructor
  · intro h
    have := congrArg low238 h
    simpa only [low238_mask238] using this
  · intro h
    simp only [mask238, h]

theorem mask238_getLsbD (d : Digest) (i : Nat) :
    (mask238 d).getLsbD i = (decide (i < 238) && d.getLsbD i) := by
  unfold mask238 low238
  rw [BitVec.getLsbD_append]
  by_cases hi : i < 238
  · simp [hi]
  · simp [hi]

theorem low238_mask240 (d : Digest) : low238 (mask240 d) = low238 d := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [low238, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and, Nat.zero_add,
    mask240_getLsbD, show i < 240 by omega]

theorem mask240_mask238 (d : Digest) : mask240 (mask238 d) = mask238 d := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [mask240_getLsbD, mask238_getLsbD]
  by_cases h238 : i < 238
  · simp [h238, show i < 240 by omega]
  · simp [h238]

theorem low238_maskLevel (l : Nat) (d : Digest) : low238 (maskLevel l d) = low238 d := by
  unfold maskLevel
  split_ifs
  · rfl
  · exact low238_mask240 d
  · exact low238_mask238 d

theorem extractLsb'_192_mask238 (d : Digest) :
    (mask238 d).extractLsb' 0 192 = d.extractLsb' 0 192 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and, Nat.zero_add,
    mask238_getLsbD, show i < 238 by omega]

theorem extractLsb'_192_maskLevel (l : Nat) (d : Digest) :
    (maskLevel l d).extractLsb' 0 192 = d.extractLsb' 0 192 := by
  unfold maskLevel
  split_ifs
  · rfl
  · exact extractLsb'_192_mask240 d
  · exact extractLsb'_192_mask238 d

theorem mask238_byte_lt29 (d : Digest) (j : Nat) (hj : j < 29) :
    (mask238 d).extractLsb' (8 * j) 8 = d.extractLsb' (8 * j) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp only [BitVec.getLsbD_extractLsb', hb, decide_true, Bool.true_and, mask238_getLsbD,
    show 8 * j + b < 238 by omega]

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
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  have hge : ¬ (8 * j + b < 238) := by omega
  simp [BitVec.getLsbD_extractLsb', hb, mask238_getLsbD, hge]

theorem tail6_mask238 (d : Digest) : tail6 (mask238 d) = tail6 d := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp only [tail6, BitVec.getLsbD_extractLsb', hb, decide_true, Bool.true_and, mask238_getLsbD,
    show 232 + b < 238 by omega]

theorem mask238_eq_of_bytes (d d' : Digest)
    (hlo : ∀ j < 29, d.extractLsb' (8 * j) 8 = d'.extractLsb' (8 * j) 8)
    (h29 : d.extractLsb' (8 * 29) 8 = (0#2) ++ tail6 d')
    (h30 : d.extractLsb' (8 * 30) 8 = 0)
    (h31 : d.extractLsb' (8 * 31) 8 = 0) :
    d = mask238 d' := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have hbyte : ∀ j < 32, d.extractLsb' (8 * j) 8 = (mask238 d').extractLsb' (8 * j) 8 := by
    intro j hj
    by_cases hlt : j < 29
    · rw [hlo j hlt, mask238_byte_lt29 d' j hlt]
    · by_cases h29' : j = 29
      · subst h29'; rw [h29, mask238_byte_29 d']
      · by_cases h30' : j = 30
        · subst h30'; rw [h30, mask238_byte_ge30 d' 30 (by omega)]
        · have h31' : j = 31 := by omega
          subst h31'; rw [h31, mask238_byte_ge30 d' 31 (by omega)]
  have hj : k / 8 < 32 := by omega
  have hb : k % 8 < 8 := Nat.mod_lt k (by decide)
  have h := congrArg (fun v : BitVec 8 => v.getLsbD (k % 8)) (hbyte (k / 8) hj)
  simpa only [BitVec.getLsbD_extractLsb', hb, decide_true, Bool.true_and,
    show 8 * (k / 8) + k % 8 = k by omega] using h

/-! ### Exact r=2 Tree Geometry and Paired Late-Salt Row Layout -/

def FULL_TRIPLETS_0 : Nat := LENGTH / 3
def FULL_TRIPLETS_1 : Nat := ((LENGTH + 2) / 3) / 3
def CAP_CUT_LVL : Nat := 14
def PAIR_STRIDE : Nat := 184
def PAIR_RAND_BYTES : Nat := 40

def levelSize : Nat → Nat
  | 0 => LENGTH
  | 1 => (LENGTH + 2) / 3
  | 2 => ((LENGTH + 2) / 3 + 2) / 3
  | n + 3 => (levelSize (n + 2) + 1) / 2

def levelBytes (l : Nat) : Nat :=
  if l < 2 then levelSize l * 32
  else if l < 23 then ((levelSize l + 1) / 2) * 96
  else 32

def levelBase : Nat → Nat
  | 0 => 0
  | n + 1 => levelBase n + levelBytes n

def treeBytes : Nat := levelBase 23 + levelBytes 23
def rowOff : Nat := treeBytes
def rowBytes : Nat := (LENGTH / 2) * PAIR_STRIDE
def trapdoorBytes : Nat := rowOff + rowBytes
def proofCap : Nat := 8669633152
def tailBufBase : Nat := 20000000000

def saltOff (i : Index) : Nat :=
  rowOff + PAIR_STRIDE * (i.val / 2) + if i.val % 2 = 0 then 72 else 88

def gapOffset (idx : Nat) : Nat := 32 * (idx + idx / 2)

def nodeOffset (l idx : Nat) : Nat :=
  if l < 2 then 32 * idx else gapOffset idx

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

theorem full_triplets_0_eq : FULL_TRIPLETS_0 = 5592405 := by decide
theorem full_triplets_1_eq : FULL_TRIPLETS_1 = 1864135 := by decide
theorem levelSize_0 : levelSize 0 = 16777216 := by decide
theorem levelSize_1 : levelSize 1 = 5592406 := by decide
theorem levelSize_2 : levelSize 2 = 1864136 := by decide
theorem levelSize_4 : levelSize 4 = 466034 := by decide
theorem levelSize_8 : levelSize 8 = 29128 := by decide
theorem levelSize_14 : levelSize 14 = 456 := by decide
theorem levelSize_22 : levelSize 22 = 2 := by decide
theorem levelSize_23 : levelSize 23 = 1 := by decide
theorem treeBytes_eq : treeBytes = 894785760 := by decide
theorem rowOff_eq : rowOff = 894785760 := by decide
theorem rowBytes_eq : rowBytes = 1543503872 := by decide
theorem trapdoorBytes_eq : trapdoorBytes = 2438289632 := by decide

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

theorem levelSize_step (l : Nat) (hl : 2 ≤ l) :
    levelSize (l + 1) = (levelSize l + 1) / 2 := by
  cases l with
  | zero => omega
  | succ k =>
    cases k with
    | zero => omega
    | succ m => rfl

theorem levelSize_pos (l : Nat) (hl : l ≤ 23) : 0 < levelSize l := by
  interval_cases l <;> decide

theorem levelSize_ge_two (l : Nat) (hl : l < 23) : 2 ≤ levelSize l := by
  interval_cases l <;> decide

theorem levelBase_bound (l : Nat) (hl : l ≤ 23) :
    levelBase l + levelBytes l ≤ treeBytes := by
  interval_cases l <;> decide

theorem capMarkOff_bound (l : Nat) (hl : 14 ≤ l) (hl2 : l ≤ 23) :
    capMarkOff l + levelSize l ≤ 1024 := by
  interval_cases l <;> decide

theorem capValOff_bound (l : Nat) (hl : 14 ≤ l) (hl2 : l ≤ 23) :
    capValOff l + levelBytes l ≤ 44000 := by
  interval_cases l <;> decide

theorem gapOffset_even (q : Nat) : gapOffset (2 * q) = 96 * q := by
  unfold gapOffset; omega

theorem gapOffset_odd (q : Nat) : gapOffset (2 * q + 1) = 96 * q + 32 := by
  unfold gapOffset; omega

theorem gapOffset_lt_levelBytes (l idx : Nat) (hl1 : 2 ≤ l) (hl2 : l < 23)
    (hidx : idx < levelSize l) :
    gapOffset idx + 32 ≤ levelBytes l := by
  unfold gapOffset levelBytes
  have hge2 : ¬ (l < 2) := by omega
  simp only [hge2, ite_false, hl2, ite_true]
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

/-! ### Late-Salt Leaf Compression Inputs and Tree Semantics -/

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

/-- Tree node values built from an arbitrary leaf-digest vector (`r = 2`). -/
def nodeValFromLeaves (c : Comp96) (leaves : Index → Digest) : Nat → Nat → Digest
  | 0, idx => if h : idx < LENGTH then leaves ⟨idx, h⟩ else 0
  | 1, idx =>
      if idx < FULL_TRIPLETS_0 then
        c (ternaryInput
          (nodeValFromLeaves c leaves 0 (3 * idx))
          (nodeValFromLeaves c leaves 0 (3 * idx + 1))
          (nodeValFromLeaves c leaves 0 (3 * idx + 2)))
      else if idx = FULL_TRIPLETS_0 then
        nodeValFromLeaves c leaves 0 (3 * FULL_TRIPLETS_0)
      else 0
  | 2, idx =>
      if idx < FULL_TRIPLETS_1 then
        c (ternaryInput
          (nodeValFromLeaves c leaves 1 (3 * idx))
          (nodeValFromLeaves c leaves 1 (3 * idx + 1))
          (nodeValFromLeaves c leaves 1 (3 * idx + 2)))
      else if idx = FULL_TRIPLETS_1 then
        nodeValFromLeaves c leaves 1 (3 * FULL_TRIPLETS_1)
      else 0
  | l + 3, idx =>
      let prev := l + 2
      if 2 * idx + 1 < levelSize prev then
        let raw := c (binaryInput
          (nodeValFromLeaves c leaves prev (2 * idx))
          (nodeValFromLeaves c leaves prev (2 * idx + 1)))
        maskLevel (l + 3) raw
      else if 2 * idx < levelSize prev then
        nodeValFromLeaves c leaves prev (2 * idx)
      else 0

def nodeVal (c : Comp96) (msg : Message) (salts : Index → Salt192) : Nat → Nat → Digest :=
  nodeValFromLeaves c (fun i => leafDigest c i (salts i) (msg i))

def rootVal (c : Comp96) (msg : Message) (salts : Index → Salt192) : Digest :=
  nodeVal c msg salts 23 0

/-- Every node on levels 5..22 (including promoted rightmost nodes) is 240-bit clean,
because level 4 has even size 466,034 so every level-5 node comes from a 240-bit masked binary call. -/
theorem nodeValFromLeaves_masked (c : Comp96) (leaves : Index → Digest)
    (l idx : Nat) (hl1 : 5 ≤ l) (hl2 : l ≤ 22) (hidx : idx < levelSize l) :
    mask240 (nodeValFromLeaves c leaves l idx) = nodeValFromLeaves c leaves l idx := by
  induction l generalizing idx with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero => omega
    | succ k' =>
      cases k' with
      | zero => omega
      | succ m =>
        have hne23 : m + 3 ≠ 23 := by omega
        have hge5 : ¬ (m + 3 < 5) := by omega
        simp only [nodeValFromLeaves]
        split
        · unfold maskLevel
          simp only [hge5, hne23, or_self, ite_false]
          split
          · exact mask240_idempotent _
          · exact mask240_mask238 _
        · split
          · rename_i hnot hlt
            by_cases hm : m = 2
            · subst hm
              change ¬ (2 * idx + 1 < 466034) at hnot
              change 2 * idx < 466034 at hlt
              omega
            · exact ih (2 * idx) (by omega) (by omega) hlt
          · unfold mask240 low240; decide

/-- Every node on levels 9..22 (including promoted rightmost nodes) is 238-bit clean,
because level 8 has even size 29,128 so every level-9 node comes from a 238-bit masked binary call. -/
theorem nodeValFromLeaves_masked238 (c : Comp96) (leaves : Index → Digest)
    (l idx : Nat) (hl1 : 9 ≤ l) (hl2 : l ≤ 22) (hidx : idx < levelSize l) :
    mask238 (nodeValFromLeaves c leaves l idx) = nodeValFromLeaves c leaves l idx := by
  induction l generalizing idx with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero => omega
    | succ k' =>
      cases k' with
      | zero => omega
      | succ m =>
        have hne23 : m + 3 ≠ 23 := by omega
        have hge5 : ¬ (m + 3 < 5) := by omega
        have hge9 : ¬ (m + 3 < 9) := by omega
        simp only [nodeValFromLeaves]
        split
        · unfold maskLevel
          simp only [hge5, hne23, or_self, ite_false, hge9]
          exact mask238_idempotent _
        · split
          · rename_i hnot hlt
            by_cases hm : m = 6
            · subst hm
              change ¬ (2 * idx + 1 < 29128) at hnot
              change 2 * idx < 29128 at hlt
              omega
            · exact ih (2 * idx) (by omega) (by omega) hlt
          · unfold mask238 low238; decide

/-! ### Cap Marking (c = 9, L14 = 456 cap leaves) and Exact Telescoping Bounds -/

def capLeafOf (i : Index) : Nat := ((i.val / 3) / 3) >>> 12

theorem capLeafOf_lt (i : Index) : capLeafOf i < 456 := by
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

theorem capMark_23_eq_true (positions : Positions) (hne : positions.Nonempty) :
    capMark positions 23 0 = true := by
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
  have h16 := hstep 15 _ (by omega) (by have := capLeafOf_lt i; change _ < 228; omega) h15
  have h17 := hstep 16 _ (by omega) (by have := capLeafOf_lt i; change _ < 114; omega) h16
  have h18 := hstep 17 _ (by omega) (by have := capLeafOf_lt i; change _ < 57; omega) h17
  have h19 := hstep 18 _ (by omega) (by have := capLeafOf_lt i; change _ < 29; omega) h18
  have h20 := hstep 19 _ (by omega) (by have := capLeafOf_lt i; change _ < 15; omega) h19
  have h21 := hstep 20 _ (by omega) (by have := capLeafOf_lt i; change _ < 8; omega) h20
  have h22 := hstep 21 _ (by omega) (by have := capLeafOf_lt i; change _ < 4; omega) h21
  have h23 := hstep 22 _ (by omega) (by have := capLeafOf_lt i; change _ < 2; omega) h22
  have hz : capLeafOf i / 2 / 2 / 2 / 2 / 2 / 2 / 2 / 2 / 2 = 0 := by
    have := capLeafOf_lt i; omega
  rwa [hz] at h23

def levelFrontierCount (positions : Positions) (l : Nat) : Nat :=
  ((Finset.range (levelSize l / 2)).filter
    (fun q => capMark positions l (2 * q) != capMark positions l (2 * q + 1))).card

def capFrontierCount (positions : Positions) : Nat :=
  ∑ step ∈ Finset.range 9, levelFrontierCount positions (14 + step)

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

/-- Base level L14 (456 nodes = 228 pairs): frontier_14 + unmarked_15 <= 228. -/
theorem frontier_14_add_unmarked_15 (positions : Positions) :
    levelFrontierCount positions 14 + levelUnmarkedCount positions 15 ≤ 228 := by
  unfold levelFrontierCount levelUnmarkedCount
  have h14 : levelSize 14 / 2 = 228 := by decide
  have h15 : levelSize 15 = 228 := by decide
  rw [h14, h15, card_filter_eq_sum, card_filter_eq_sum, ← Finset.sum_add_distrib]
  calc
    ∑ q ∈ Finset.range 228,
        ((if (capMark positions 14 (2 * q) != capMark positions 14 (2 * q + 1)) = true then 1 else 0) +
         (if (!capMark positions 15 q) = true then 1 else 0))
      ≤ ∑ _q ∈ Finset.range 228, 1 := by
        apply Finset.sum_le_sum
        intro q hq
        have hq' : q < 228 := Finset.mem_range.mp hq
        have hpair : 2 * q + 1 < levelSize 14 := by rw [levelSize_14]; omega
        rw [capMark_succ positions 14 q (by omega), if_pos hpair]
        cases capMark positions 14 (2 * q) <;> cases capMark positions 14 (2 * q + 1) <;> decide
    _ = 228 := by simp

/-- Telescoping step for every level l >= 14: frontier_l + unmarked_{l+1} <= unmarked_l. -/
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

/-- Universal cap frontier bound: at most 228 frontier digests for every subset of positions. -/
theorem cap_frontier_le_228 (positions : Positions) :
    capFrontierCount positions ≤ 228 := by
  have h14 : levelFrontierCount positions 14 + levelUnmarkedCount positions 15 ≤ 228 :=
    frontier_14_add_unmarked_15 positions
  have h15 : levelFrontierCount positions 15 + levelUnmarkedCount positions 16 ≤ levelUnmarkedCount positions 15 :=
    frontier_add_unmarked_succ positions 15 (by omega)
  have h16 : levelFrontierCount positions 16 + levelUnmarkedCount positions 17 ≤ levelUnmarkedCount positions 16 :=
    frontier_add_unmarked_succ positions 16 (by omega)
  have h17 : levelFrontierCount positions 17 + levelUnmarkedCount positions 18 ≤ levelUnmarkedCount positions 17 :=
    frontier_add_unmarked_succ positions 17 (by omega)
  have h18 : levelFrontierCount positions 18 + levelUnmarkedCount positions 19 ≤ levelUnmarkedCount positions 18 :=
    frontier_add_unmarked_succ positions 18 (by omega)
  have h19 : levelFrontierCount positions 19 + levelUnmarkedCount positions 20 ≤ levelUnmarkedCount positions 19 :=
    frontier_add_unmarked_succ positions 19 (by omega)
  have h20 : levelFrontierCount positions 20 + levelUnmarkedCount positions 21 ≤ levelUnmarkedCount positions 20 :=
    frontier_add_unmarked_succ positions 20 (by omega)
  have h21 : levelFrontierCount positions 21 + levelUnmarkedCount positions 22 ≤ levelUnmarkedCount positions 21 :=
    frontier_add_unmarked_succ positions 21 (by omega)
  have h22 : levelFrontierCount positions 22 + levelUnmarkedCount positions 23 ≤ levelUnmarkedCount positions 22 :=
    frontier_add_unmarked_succ positions 22 (by omega)
  have hsum : capFrontierCount positions =
      levelFrontierCount positions 14 + levelFrontierCount positions 15 +
      levelFrontierCount positions 16 + levelFrontierCount positions 17 +
      levelFrontierCount positions 18 + levelFrontierCount positions 19 +
      levelFrontierCount positions 20 + levelFrontierCount positions 21 +
      levelFrontierCount positions 22 := by
    unfold capFrontierCount
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.zero_add]
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

/-! ### Exact Two-End 6-Bit Tail Stream Proof Serialization and Size Bounds -/

def bitsToBytes {w : Nat} (v : BitVec w) (n : Nat) : List Byte :=
  (List.range n).map fun j => v.extractLsb' (8 * j) 8

theorem bitsToBytes_length {w : Nat} (v : BitVec w) (n : Nat) :
    (bitsToBytes v n).length = n := by
  simp [bitsToBytes]

/-- Little-endian integer encoding of a list of 6-bit tail chunks (`6 * tails.length` bits). -/
def bitsOf6 (tails : List (BitVec 6)) : Nat :=
  tails.foldr (fun t acc => t.toNat + 64 * acc) 0

/-- Little-endian integer encoding of a list of bytes (`8 * bs.length` bits). -/
def bytesToNat (bs : List Byte) : Nat :=
  bs.foldr (fun b acc => b.toNat + 256 * acc) 0

theorem bitsOf6_nil : bitsOf6 [] = 0 := rfl

theorem bitsOf6_cons (t : BitVec 6) (ts : List (BitVec 6)) :
    bitsOf6 (t :: ts) = t.toNat + 64 * bitsOf6 ts := rfl

theorem bitsOf6_append_singleton (ts : List (BitVec 6)) (t : BitVec 6) :
    bitsOf6 (ts ++ [t]) = bitsOf6 ts + t.toNat * 2 ^ (6 * ts.length) := by
  induction ts with
  | nil => simp [bitsOf6]
  | cons a rest ih =>
    simp only [List.cons_append, bitsOf6_cons, ih, List.length_cons]
    have hpow : 64 * 2 ^ (6 * rest.length) = 2 ^ (6 * (rest.length + 1)) := by
      rw [show 6 * (rest.length + 1) = 6 + 6 * rest.length by omega, Nat.pow_add]
    calc
      a.toNat + 64 * (bitsOf6 rest + t.toNat * 2 ^ (6 * rest.length))
        = (a.toNat + 64 * bitsOf6 rest) + t.toNat * (64 * 2 ^ (6 * rest.length)) := by ring
      _ = (a.toNat + 64 * bitsOf6 rest) + t.toNat * 2 ^ (6 * (rest.length + 1)) := by rw [hpow]

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

theorem bitsOf6_lt (tails : List (BitVec 6)) : bitsOf6 tails < 2 ^ (6 * tails.length) := by
  induction tails with
  | nil => simp [bitsOf6]
  | cons t rest ih =>
    simp only [bitsOf6_cons, List.length_cons]
    have ht : t.toNat < 64 := t.isLt
    have hpow : 2 ^ (6 * (rest.length + 1)) = 64 * 2 ^ (6 * rest.length) := by
      rw [show 6 * (rest.length + 1) = 6 + 6 * rest.length by omega, Nat.pow_add]
    rw [hpow]
    omega

/-- Exact streaming 6-bit LSB-first packer state `(emittedBytes, bitBuf, bitCnt)`. -/
def pack6Step (st : List Byte × Nat × Nat) (t : BitVec 6) : List Byte × Nat × Nat :=
  let (acc, buf, cnt) := st
  let buf' := buf + t.toNat * 2 ^ cnt
  let cnt' := cnt + 6
  if 8 ≤ cnt' then
    (acc ++ [BitVec.ofNat 8 buf'], buf' / 256, cnt' - 8)
  else
    (acc, buf', cnt')

def pack6Finish (st : List Byte × Nat × Nat) : List Byte :=
  let (acc, buf, cnt) := st
  if 0 < cnt then acc ++ [BitVec.ofNat 8 buf] else acc

def pack6Bits (tails : List (BitVec 6)) : List Byte :=
  pack6Finish (tails.foldl pack6Step ([], 0, 0))

/-- Reversed packed 6-bit tail stream appended to the end of the proof for backward reading. -/
def pack6BitsRev (tails : List (BitVec 6)) : List Byte :=
  (pack6Bits tails).reverse

private theorem pack6Step_inv (acc : List Byte) (buf cnt n v : Nat) (t : BitVec 6)
    (hcnt : cnt < 8) (hbuf : buf < 2 ^ cnt)
    (hbits : 8 * acc.length + cnt = 6 * n)
    (hval : bytesToNat acc + 2 ^ (8 * acc.length) * buf = v) :
    let (acc', buf', cnt') := pack6Step (acc, buf, cnt) t
    cnt' < 8 ∧ buf' < 2 ^ cnt' ∧
    8 * acc'.length + cnt' = 6 * (n + 1) ∧
    bytesToNat acc' + 2 ^ (8 * acc'.length) * buf' = v + t.toNat * 2 ^ (6 * n) := by
  unfold pack6Step
  dsimp only
  have ht : t.toNat < 64 := t.isLt
  have hbuf' : buf + t.toNat * 2 ^ cnt < 2 ^ (cnt + 6) := by
    rw [Nat.pow_add]
    have : 2 ^ 6 = 64 := by decide
    rw [this]
    have h1 : t.toNat ≤ 63 := by omega
    calc
      buf + t.toNat * 2 ^ cnt < 2 ^ cnt + 63 * 2 ^ cnt := by
        have hm := Nat.mul_le_mul_right (2 ^ cnt) h1; omega
      _ = 2 ^ cnt * 64 := by ring
  have hterm : 2 ^ (8 * acc.length) * (buf + t.toNat * 2 ^ cnt) =
      2 ^ (8 * acc.length) * buf + t.toNat * 2 ^ (6 * n) := by
    rw [Nat.mul_add, ← hbits, Nat.pow_add]
    ring
  split_ifs with hge
  · dsimp only
    refine ⟨by omega, ?_, ?_, ?_⟩
    · have hdiv : (buf + t.toNat * 2 ^ cnt) / 256 < 2 ^ (cnt + 6 - 8) := by
        rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 256)]
        rw [show 2 ^ (cnt + 6 - 8) * 256 = 2 ^ (cnt + 6) by
          rw [show 256 = 2 ^ 8 by decide, ← Nat.pow_add, show cnt + 6 - 8 + 8 = cnt + 6 by omega]]
        exact hbuf'
      exact hdiv
    · simp only [List.length_append, List.length_singleton]; omega
    · rw [bytesToNat_append_singleton, List.length_append, List.length_singleton]
      have hof : (BitVec.ofNat 8 (buf + t.toNat * 2 ^ cnt)).toNat = (buf + t.toNat * 2 ^ cnt) % 256 := by
        simp [BitVec.toNat_ofNat]
      rw [hof]
      have hpow : 2 ^ (8 * (acc.length + 1)) = 2 ^ (8 * acc.length) * 256 := by
        rw [show 8 * (acc.length + 1) = 8 * acc.length + 8 by omega, Nat.pow_add]
      rw [hpow]
      have hdm : (buf + t.toNat * 2 ^ cnt) % 256 + 256 * ((buf + t.toNat * 2 ^ cnt) / 256) =
          buf + t.toNat * 2 ^ cnt := by
        omega
      calc
        bytesToNat acc + (buf + t.toNat * 2 ^ cnt) % 256 * 2 ^ (8 * acc.length) +
            2 ^ (8 * acc.length) * 256 * ((buf + t.toNat * 2 ^ cnt) / 256)
          = bytesToNat acc + 2 ^ (8 * acc.length) *
              ((buf + t.toNat * 2 ^ cnt) % 256 + 256 * ((buf + t.toNat * 2 ^ cnt) / 256)) := by ring
        _ = bytesToNat acc + 2 ^ (8 * acc.length) * (buf + t.toNat * 2 ^ cnt) := by rw [hdm]
        _ = bytesToNat acc + 2 ^ (8 * acc.length) * buf + t.toNat * 2 ^ (6 * n) := by rw [hterm, Nat.add_assoc]
        _ = v + t.toNat * 2 ^ (6 * n) := by rw [hval]
  · dsimp only
    refine ⟨by omega, hbuf', by omega, ?_⟩
    rw [hterm, ← Nat.add_assoc, hval]

private theorem pack6_foldl_inv (tails : List (BitVec 6)) :
    ∀ acc buf cnt prev,
      cnt < 8 → buf < 2 ^ cnt →
      8 * acc.length + cnt = 6 * prev.length →
      bytesToNat acc + 2 ^ (8 * acc.length) * buf = bitsOf6 prev →
      let (acc', buf', cnt') := tails.foldl pack6Step (acc, buf, cnt)
      cnt' < 8 ∧ buf' < 2 ^ cnt' ∧
      8 * acc'.length + cnt' = 6 * (prev ++ tails).length ∧
      bytesToNat acc' + 2 ^ (8 * acc'.length) * buf' = bitsOf6 (prev ++ tails) := by
  induction tails with
  | nil =>
    intro acc buf cnt prev hcnt hbuf hbits hval
    simpa using And.intro hcnt (And.intro hbuf (And.intro hbits hval))
  | cons t rest ih =>
    intro acc buf cnt prev hcnt hbuf hbits hval
    simp only [List.foldl_cons]
    have hstep := pack6Step_inv acc buf cnt prev.length (bitsOf6 prev) t hcnt hbuf hbits hval
    rcases hst : pack6Step (acc, buf, cnt) t with ⟨acc1, buf1, cnt1⟩
    rw [hst] at hstep
    rcases hstep with ⟨hcnt1, hbuf1, hbits1, hval1⟩
    have hlen1 : (prev ++ [t]).length = prev.length + 1 := by simp
    have hbits1' : 8 * acc1.length + cnt1 = 6 * (prev ++ [t]).length := by rw [hlen1]; exact hbits1
    have hval1' : bytesToNat acc1 + 2 ^ (8 * acc1.length) * buf1 = bitsOf6 (prev ++ [t]) := by
      rw [bitsOf6_append_singleton]; exact hval1
    have hres := ih acc1 buf1 cnt1 (prev ++ [t]) hcnt1 hbuf1 hbits1' hval1'
    simpa only [List.append_assoc, List.singleton_append] using hres

theorem pack6Bits_spec (tails : List (BitVec 6)) :
    (pack6Bits tails).length = (6 * tails.length + 7) / 8 ∧
    bytesToNat (pack6Bits tails) = bitsOf6 tails := by
  have h := pack6_foldl_inv tails [] 0 0 [] (by omega) (by decide) (by simp) (by simp [bytesToNat, bitsOf6])
  unfold pack6Bits pack6Finish
  rcases hfold : tails.foldl pack6Step ([], 0, 0) with ⟨acc, buf, cnt⟩
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

theorem pack6Bits_length (tails : List (BitVec 6)) :
    (pack6Bits tails).length = (6 * tails.length + 7) / 8 :=
  (pack6Bits_spec tails).1

theorem pack6BitsRev_length (tails : List (BitVec 6)) :
    (pack6BitsRev tails).length = (6 * tails.length + 7) / 8 := by
  unfold pack6BitsRev
  rw [List.length_reverse]
  exact pack6Bits_length tails

theorem pack6Bits_bytesToNat (tails : List (BitVec 6)) :
    bytesToNat (pack6Bits tails) = bitsOf6 tails :=
  (pack6Bits_spec tails).2

def l0SiblingsProof (nodes : Nat → Nat → Digest) (i : Index) : List Byte :=
  let g := i.val / 3
  let r := i.val % 3
  if g = FULL_TRIPLETS_0 then []
  else if r = 0 then bitsToBytes (nodes 0 (3 * g + 1)) 32 ++ bitsToBytes (nodes 0 (3 * g + 2)) 32
  else if r = 1 then bitsToBytes (nodes 0 (3 * g)) 32 ++ bitsToBytes (nodes 0 (3 * g + 2)) 32
  else bitsToBytes (nodes 0 (3 * g)) 32 ++ bitsToBytes (nodes 0 (3 * g + 1)) 32

def l1SiblingsProof (nodes : Nat → Nat → Digest) (i : Index) : List Byte :=
  let g0 := i.val / 3
  let g1 := g0 / 3
  let r1 := g0 % 3
  if g1 = FULL_TRIPLETS_1 then []
  else if r1 = 0 then bitsToBytes (nodes 1 (3 * g1 + 1)) 32 ++ bitsToBytes (nodes 1 (3 * g1 + 2)) 32
  else if r1 = 1 then bitsToBytes (nodes 1 (3 * g1)) 32 ++ bitsToBytes (nodes 1 (3 * g1 + 2)) 32
  else bitsToBytes (nodes 1 (3 * g1)) 32 ++ bitsToBytes (nodes 1 (3 * g1 + 1)) 32

/-- Forward bytes of `L2..L13` siblings (`L2..L4`: 32 B, `L5..L8`: 30 B, `L9..L13`: 29 B). -/
def binPathFwd (nodes : Nat → Nat → Digest) (g1 : Nat) : List Byte :=
  (List.range 12).flatMap fun step =>
    let l := 2 + step
    let idx := g1 >>> step
    let sib := idx ^^^ 1
    if sib < levelSize l then
      bitsToBytes (nodes l sib) (if l < 5 then 32 else if l < 9 then 30 else 29)
    else []

/-- 6-bit tails of `L9..L13` siblings in canonical order. -/
def binPathTails (nodes : Nat → Nat → Digest) (g1 : Nat) : List (BitVec 6) :=
  (List.range 5).flatMap fun step =>
    let l := 9 + step
    let idx := g1 >>> (step + 7)
    let sib := idx ^^^ 1
    if sib < levelSize l then [tail6 (nodes l sib)] else []

def recordFwd (nodes : Nat → Nat → Digest) (salts : Index → Salt192) (i : Index) : List Byte :=
  let g1 := (i.val / 3) / 3
  bitsToBytes (salts i) 24 ++
  l0SiblingsProof nodes i ++
  l1SiblingsProof nodes i ++
  binPathFwd nodes g1

def recordTails (nodes : Nat → Nat → Digest) (i : Index) : List (BitVec 6) :=
  binPathTails nodes ((i.val / 3) / 3)

def capLevelFrontierFwd (nodes : Nat → Nat → Digest) (positions : Positions) (l : Nat) : List Byte :=
  (List.range (levelSize l / 2)).flatMap fun q =>
    let mL := capMark positions l (2 * q)
    let mR := capMark positions l (2 * q + 1)
    if mL = mR then []
    else if !mL then bitsToBytes (nodes l (2 * q)) 29
    else bitsToBytes (nodes l (2 * q + 1)) 29

def capLevelFrontierTails (nodes : Nat → Nat → Digest) (positions : Positions) (l : Nat) : List (BitVec 6) :=
  (List.range (levelSize l / 2)).flatMap fun q =>
    let mL := capMark positions l (2 * q)
    let mR := capMark positions l (2 * q + 1)
    if mL = mR then []
    else if !mL then [tail6 (nodes l (2 * q))]
    else [tail6 (nodes l (2 * q + 1))]

def capFrontierFwd (nodes : Nat → Nat → Digest) (positions : Positions) : List Byte :=
  (List.range 9).flatMap fun step => capLevelFrontierFwd nodes positions (14 + step)

def capFrontierTails (nodes : Nat → Nat → Digest) (positions : Positions) : List (BitVec 6) :=
  (List.range 9).flatMap fun step => capLevelFrontierTails nodes positions (14 + step)

def referenceProofFwd (nodes : Nat → Nat → Digest) (salts : Index → Salt192)
    (positions : Positions) : List Byte :=
  (positions.sort (· ≤ ·)).flatMap (recordFwd nodes salts) ++
  capFrontierFwd nodes positions

def referenceProofTails (nodes : Nat → Nat → Digest) (positions : Positions) : List (BitVec 6) :=
  (positions.sort (· ≤ ·)).flatMap (recordTails nodes) ++
  capFrontierTails nodes positions

def referenceProof (nodes : Nat → Nat → Digest) (salts : Index → Salt192)
    (positions : Positions) : Proof :=
  if positions.card = 0 then []
  else
    referenceProofFwd nodes salts positions ++
    pack6BitsRev (referenceProofTails nodes positions)

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

theorem l0SiblingsProof_length_le (nodes : Nat → Nat → Digest) (i : Index) :
    (l0SiblingsProof nodes i).length ≤ 64 := by
  unfold l0SiblingsProof
  dsimp only
  split_ifs <;> simp [bitsToBytes]

theorem l1SiblingsProof_length_le (nodes : Nat → Nat → Digest) (i : Index) :
    (l1SiblingsProof nodes i).length ≤ 64 := by
  unfold l1SiblingsProof
  dsimp only
  split_ifs <;> simp [bitsToBytes]

theorem binPathFwd_length_le (nodes : Nat → Nat → Digest) (g1 : Nat) :
    (binPathFwd nodes g1).length ≤ 361 := by
  unfold binPathFwd
  rw [List.length_flatMap]
  dsimp only
  have hle : ∀ step ∈ List.range 12,
      (if ((g1 >>> step) ^^^ 1) < levelSize (2 + step)
       then bitsToBytes (nodes (2 + step) ((g1 >>> step) ^^^ 1))
         (if 2 + step < 5 then 32 else if 2 + step < 9 then 30 else 29)
       else []).length ≤ (if 2 + step < 5 then 32 else if 2 + step < 9 then 30 else 29) := by
    intro step _
    split <;> simp [bitsToBytes]
  have hsum := list_map_sum_le (List.range 12)
    (fun step => (if ((g1 >>> step) ^^^ 1) < levelSize (2 + step)
       then bitsToBytes (nodes (2 + step) ((g1 >>> step) ^^^ 1))
         (if 2 + step < 5 then 32 else if 2 + step < 9 then 30 else 29)
       else []).length)
    (fun step => if 2 + step < 5 then 32 else if 2 + step < 9 then 30 else 29) hle
  have hconst : ((List.range 12).map (fun step => if 2 + step < 5 then 32 else if 2 + step < 9 then 30 else 29)).sum = 361 := by
    decide
  exact hsum.trans (le_of_eq hconst)

theorem binPathTails_length_le (nodes : Nat → Nat → Digest) (g1 : Nat) :
    (binPathTails nodes g1).length ≤ 5 := by
  unfold binPathTails
  rw [List.length_flatMap]
  have hle : ∀ step ∈ List.range 5,
      (if ((g1 >>> (step + 7)) ^^^ 1) < levelSize (9 + step)
       then [tail6 (nodes (9 + step) ((g1 >>> (step + 7)) ^^^ 1))] else []).length ≤ 1 := by
    intro step _
    split <;> simp
  have hsum := list_map_sum_le (List.range 5)
    (fun step => (if ((g1 >>> (step + 7)) ^^^ 1) < levelSize (9 + step)
       then [tail6 (nodes (9 + step) ((g1 >>> (step + 7)) ^^^ 1))] else []).length)
    (fun _ => 1) hle
  simpa using hsum

theorem recordFwd_length_le_513 (nodes : Nat → Nat → Digest) (salts : Index → Salt192) (i : Index) :
    (recordFwd nodes salts i).length ≤ 513 := by
  unfold recordFwd
  simp only [List.length_append, bitsToBytes_length]
  have h0 := l0SiblingsProof_length_le nodes i
  have h1 := l1SiblingsProof_length_le nodes i
  have h2 := binPathFwd_length_le nodes ((i.val / 3) / 3)
  omega

theorem recordTails_length_le_5 (nodes : Nat → Nat → Digest) (i : Index) :
    (recordTails nodes i).length ≤ 5 :=
  binPathTails_length_le nodes ((i.val / 3) / 3)

theorem capLevelFrontierFwd_length (nodes : Nat → Nat → Digest) (positions : Positions) (l : Nat) :
    (capLevelFrontierFwd nodes positions l).length = 29 * levelFrontierCount positions l := by
  unfold capLevelFrontierFwd levelFrontierCount
  rw [List.length_flatMap, card_filter_eq_sum, Finset.mul_sum, list_sum_range]
  apply Finset.sum_congr rfl
  intro q _
  dsimp only
  cases capMark positions l (2 * q) <;> cases capMark positions l (2 * q + 1) <;> simp [bitsToBytes]

theorem capLevelFrontierTails_length (nodes : Nat → Nat → Digest) (positions : Positions) (l : Nat) :
    (capLevelFrontierTails nodes positions l).length = levelFrontierCount positions l := by
  unfold capLevelFrontierTails levelFrontierCount
  rw [List.length_flatMap, card_filter_eq_sum, list_sum_range]
  apply Finset.sum_congr rfl
  intro q _
  dsimp only
  cases capMark positions l (2 * q) <;> cases capMark positions l (2 * q + 1) <;> simp

theorem capFrontierFwd_length (nodes : Nat → Nat → Digest) (positions : Positions) :
    (capFrontierFwd nodes positions).length = 29 * capFrontierCount positions := by
  unfold capFrontierFwd capFrontierCount
  rw [List.length_flatMap, list_sum_range, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro step _
  exact capLevelFrontierFwd_length nodes positions (14 + step)

theorem capFrontierTails_length (nodes : Nat → Nat → Digest) (positions : Positions) :
    (capFrontierTails nodes positions).length = capFrontierCount positions := by
  unfold capFrontierTails capFrontierCount
  rw [List.length_flatMap, list_sum_range]
  apply Finset.sum_congr rfl
  intro step _
  exact capLevelFrontierTails_length nodes positions (14 + step)

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

theorem referenceProofTails_length_le (nodes : Nat → Nat → Digest) (positions : Positions) :
    (referenceProofTails nodes positions).length ≤ 5 * positions.card + 228 := by
  unfold referenceProofTails
  rw [List.length_append, List.length_flatMap, capFrontierTails_length]
  have hrec := list_map_sum_le (positions.sort (· ≤ ·))
    (fun i => (recordTails nodes i).length) (fun _ => 5)
    (fun i _ => recordTails_length_le_5 nodes i)
  have hrec2 : ((positions.sort (· ≤ ·)).map fun _ => 5).sum = 5 * positions.card := by
    simp [Nat.mul_comm]
  have hcap := cap_frontier_le_228 positions
  omega

theorem referenceProof_length_le (nodes : Nat → Nat → Digest) (salts : Index → Salt192)
    (positions : Positions) :
    (referenceProof nodes salts positions).length ≤
      513 * positions.card + 6612 + (6 * (5 * positions.card + 228) + 7) / 8 := by
  unfold referenceProof referenceProofFwd
  split
  · simp
  · rw [List.length_append, List.length_append, List.length_flatMap, capFrontierFwd_length,
      pack6BitsRev_length]
    have hrec := list_map_sum_le (positions.sort (· ≤ ·))
      (fun i => (recordFwd nodes salts i).length) (fun _ => 513)
      (fun i _ => recordFwd_length_le_513 nodes salts i)
    have hrec2 : ((positions.sort (· ≤ ·)).map fun _ => 513).sum = 513 * positions.card := by
      simp [Nat.mul_comm]
    have hcap := cap_frontier_le_228 positions
    have htails := referenceProofTails_length_le nodes positions
    have hdiv : (6 * (referenceProofTails nodes positions).length + 7) / 8 ≤
        (6 * (5 * positions.card + 228) + 7) / 8 :=
      Nat.div_le_div_right (by omega)
    omega

theorem referenceProof_congr_nodes (n1 n2 : Nat → Nat → Digest)
    (hagree : ∀ l ≤ 23, ∀ idx < levelSize l, n1 l idx = n2 l idx)
    (salts : Index → Salt192) (positions : Positions) :
    referenceProof n1 salts positions = referenceProof n2 salts positions := by
  unfold referenceProof
  split_ifs
  · rfl
  · refine congrArg₂ List.append ?_ (congrArg pack6BitsRev ?_)
    · unfold referenceProofFwd
      refine congrArg₂ List.append ?_ ?_
      · apply List.flatMap_congr; intro i _
        unfold recordFwd l0SiblingsProof l1SiblingsProof binPathFwd
        dsimp only
        have h0 := hagree 0 (by omega)
        have h1 := hagree 1 (by omega)
        refine congrArg₂ List.append ?_ ?_
        · refine congrArg₂ List.append ?_ ?_
          · apply congrArg (bitsToBytes (salts i) 24 ++ ·)
            split_ifs
            · rfl
            · have hb1 : 3 * (i.val / 3) + 1 < levelSize 0 := by
                have := i.isLt; rw [levelSize_0, full_triplets_0_eq] at *; unfold LENGTH LOG_LENGTH at *; omega
              have hb2 : 3 * (i.val / 3) + 2 < levelSize 0 := by
                have := i.isLt; rw [levelSize_0, full_triplets_0_eq] at *; unfold LENGTH LOG_LENGTH at *; omega
              rw [h0 _ hb1, h0 _ hb2]
            · have hb0 : 3 * (i.val / 3) < levelSize 0 := by
                have := i.isLt; rw [levelSize_0, full_triplets_0_eq] at *; unfold LENGTH LOG_LENGTH at *; omega
              have hb2 : 3 * (i.val / 3) + 2 < levelSize 0 := by
                have := i.isLt; rw [levelSize_0, full_triplets_0_eq] at *; unfold LENGTH LOG_LENGTH at *; omega
              rw [h0 _ hb0, h0 _ hb2]
            · have hb0 : 3 * (i.val / 3) < levelSize 0 := by
                have := i.isLt; rw [levelSize_0, full_triplets_0_eq] at *; unfold LENGTH LOG_LENGTH at *; omega
              have hb1 : 3 * (i.val / 3) + 1 < levelSize 0 := by
                have := i.isLt; rw [levelSize_0, full_triplets_0_eq] at *; unfold LENGTH LOG_LENGTH at *; omega
              rw [h0 _ hb0, h0 _ hb1]
          · split_ifs
            · rfl
            · have hb1 : 3 * (i.val / 3 / 3) + 1 < levelSize 1 := by
                have := i.isLt; rw [levelSize_1, full_triplets_1_eq] at *; unfold LENGTH LOG_LENGTH at *; omega
              have hb2 : 3 * (i.val / 3 / 3) + 2 < levelSize 1 := by
                have := i.isLt; rw [levelSize_1, full_triplets_1_eq] at *; unfold LENGTH LOG_LENGTH at *; omega
              rw [h1 _ hb1, h1 _ hb2]
            · have hb0 : 3 * (i.val / 3 / 3) < levelSize 1 := by
                have := i.isLt; rw [levelSize_1, full_triplets_1_eq] at *; unfold LENGTH LOG_LENGTH at *; omega
              have hb2 : 3 * (i.val / 3 / 3) + 2 < levelSize 1 := by
                have := i.isLt; rw [levelSize_1, full_triplets_1_eq] at *; unfold LENGTH LOG_LENGTH at *; omega
              rw [h1 _ hb0, h1 _ hb2]
            · have hb0 : 3 * (i.val / 3 / 3) < levelSize 1 := by
                have := i.isLt; rw [levelSize_1, full_triplets_1_eq] at *; unfold LENGTH LOG_LENGTH at *; omega
              have hb1 : 3 * (i.val / 3 / 3) + 1 < levelSize 1 := by
                have := i.isLt; rw [levelSize_1, full_triplets_1_eq] at *; unfold LENGTH LOG_LENGTH at *; omega
              rw [h1 _ hb0, h1 _ hb1]
        · apply List.flatMap_congr; intro step hstep
          have hs : step < 12 := List.mem_range.mp hstep
          by_cases hlt : ((i.val / 3 / 3) >>> step ^^^ 1) < levelSize (2 + step)
          · simp only [hlt, ite_true, hagree (2 + step) (by omega) _ hlt]
          · simp only [hlt, ite_false]
      · unfold capFrontierFwd capLevelFrontierFwd
        apply List.flatMap_congr; intro step hstep
        have hs : step < 9 := List.mem_range.mp hstep
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
        have hs : step < 5 := List.mem_range.mp hstep
        dsimp only
        split_ifs with hlt
        · rw [hagree (9 + step) (by omega) _ hlt]
        · rfl
      · unfold capFrontierTails capLevelFrontierTails
        apply List.flatMap_congr; intro step hstep
        have hs : step < 9 := List.mem_range.mp hstep
        apply List.flatMap_congr; intro q hq
        have hq' : q < levelSize (14 + step) / 2 := List.mem_range.mp hq
        dsimp only
        split_ifs
        · rfl
        · rw [hagree (14 + step) (by omega) (2 * q) (by omega)]
        · rw [hagree (14 + step) (by omega) (2 * q + 1) (by omega)]

theorem referenceProof_length_128_le (nodes : Nat → Nat → Digest) (salts : Index → Salt192)
    (positions : Positions) (hcard : positions.card = BATCH) :
    (referenceProof nodes salts positions).length ≤ 72927 := by
  have h := referenceProof_length_le nodes salts positions
  rw [hcard] at h
  change _ ≤ 513 * 128 + 6612 + (6 * (5 * 128 + 228) + 7) / 8 at h
  omega

theorem referenceProof_length_le_cap (nodes : Nat → Nat → Digest) (salts : Index → Salt192)
    (positions : Positions) :
    (referenceProof nodes salts positions).length ≤ proofCap := by
  have h := referenceProof_length_le nodes salts positions
  have hc : positions.card ≤ LENGTH := by
    simpa only [Index, Fintype.card_fin] using Finset.card_le_univ positions
  change positions.card ≤ 16777216 at hc
  change _ ≤ 8669633152
  omega

end CommitGolfCandidate
