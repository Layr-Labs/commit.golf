import CommitGolf.Parameters
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! Mathematical model of the r=1 3-ary-bottom, left-aligned binary, cap c=9 (342 cap leaves)
vector commitment tree with paired 192-bit late salts (shared-midpoint 40-byte pair rows)
and byte-aligned 256b/240b digests. Parameterized over any 768->256 compression function. -/
namespace CommitGolfCandidate.R4
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

/-! ### Exact r=1 Tree Geometry and Paired Late-Salt Row Layout -/

def FULL_TRIPLETS : Nat := LENGTH / 3
def CAP_CUT_LVL : Nat := 15
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
def rowOff : Nat := 1610612736
def rowBytes : Nat := (LENGTH / 2) * PAIR_STRIDE
def trapdoorBytes : Nat := rowOff + rowBytes
def proofCap : Nat := 8556390424

def saltOff (i : Index) : Nat :=
  rowOff + PAIR_STRIDE * (i.val / 2) + if i.val % 2 = 0 then 72 else 88

def gapOffset (idx : Nat) : Nat := 32 * (idx + idx / 2)

def nodeOffset (l idx : Nat) : Nat :=
  if l = 0 then 32 * idx else gapOffset idx

def capMarkOff : Nat → Nat
  | 0 => 0
  | n + 1 =>
    if n < 15 then 0
    else capMarkOff n + ((levelSize n + 7) / 8) * 8

def capValOff : Nat → Nat
  | 0 => 0
  | n + 1 =>
    if n < 15 then 0
    else capValOff n + ((levelSize n + 1) / 2) * 96

theorem full_triplets_eq : FULL_TRIPLETS = 5592405 := by decide
theorem levelSize_0 : levelSize 0 = 16777216 := by decide
theorem levelSize_1 : levelSize 1 = 5592406 := by decide
theorem levelSize_2 : levelSize 2 = 2796203 := by decide
theorem levelSize_15 : levelSize 15 = 342 := by decide
theorem levelSize_23 : levelSize 23 = 2 := by decide
theorem levelSize_24 : levelSize 24 = 1 := by decide
theorem treeBytes_eq : treeBytes = 1073742880 := by decide
theorem rowOff_eq : rowOff = 1610612736 := by decide
theorem rowBytes_eq : rowBytes = 1543503872 := by decide
theorem trapdoorBytes_eq : trapdoorBytes = 3154116608 := by decide

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

theorem capMarkOff_bound (l : Nat) (hl : 15 ≤ l) (hl2 : l ≤ 24) :
    capMarkOff l + levelSize l ≤ 800 := by
  interval_cases l <;> decide

theorem capValOff_bound (l : Nat) (hl : 15 ≤ l) (hl2 : l ≤ 24) :
    capValOff l + levelBytes l ≤ 33200 := by
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
        let raw := c (binaryInput
          (nodeValFromLeaves c leaves prev (2 * idx))
          (nodeValFromLeaves c leaves prev (2 * idx + 1)))
        if l + 2 = 24 then raw else mask240 raw
      else if 2 * idx < levelSize prev then
        nodeValFromLeaves c leaves prev (2 * idx)
      else 0

def nodeVal (c : Comp96) (msg : Message) (salts : Index → Salt192) : Nat → Nat → Digest :=
  nodeValFromLeaves c (fun i => leafDigest c i (salts i) (msg i))

def rootVal (c : Comp96) (msg : Message) (salts : Index → Salt192) : Digest :=
  nodeVal c msg salts 24 0

/-- Every node on levels 2..23 (including promoted rightmost nodes) is already 240-bit clean,
because level 1 has even size 5,592,406 so every level-2 node comes from a masked binary call. -/
theorem nodeValFromLeaves_masked (c : Comp96) (leaves : Index → Digest)
    (l idx : Nat) (hl1 : 2 ≤ l) (hl2 : l ≤ 23) (hidx : idx < levelSize l) :
    mask240 (nodeValFromLeaves c leaves l idx) = nodeValFromLeaves c leaves l idx := by
  induction l generalizing idx with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero => omega
    | succ m =>
      have hne24 : m + 2 ≠ 24 := by omega
      simp only [nodeValFromLeaves, hne24, ite_false]
      split
      · exact mask240_idempotent _
      · split
        · rename_i hnot hlt
          cases m with
          | zero =>
            change ¬ (2 * idx + 1 < 5592406) at hnot
            change 2 * idx < 5592406 at hlt
            omega
          | succ m' =>
            exact ih (2 * idx) (by omega) (by omega) hlt
        · unfold mask240 low240; decide

/-! ### Cap Marking (c = 9, L15 = 342 cap leaves) and Exact Telescoping Bounds -/

def capLeafOf (i : Index) : Nat := (i.val / 3) >>> 14

theorem capLeafOf_lt (i : Index) : capLeafOf i < 342 := by
  unfold capLeafOf
  have hi : i.val < 16777216 := i.isLt
  rw [Nat.shiftRight_eq_div_pow]
  omega

def capMark (positions : Positions) : Nat → Nat → Bool
  | 0, _ => false
  | n + 1, idx =>
      if n + 1 < 15 then false
      else if n + 1 = 15 then decide (∃ i ∈ positions, capLeafOf i = idx)
      else if 2 * idx + 1 < levelSize n then
        capMark positions n (2 * idx) || capMark positions n (2 * idx + 1)
      else if 2 * idx < levelSize n then
        capMark positions n (2 * idx)
      else false

theorem capMark_15 (positions : Positions) (idx : Nat) :
    capMark positions 15 idx = decide (∃ i ∈ positions, capLeafOf i = idx) := by
  rfl

theorem capMark_succ (positions : Positions) (l idx : Nat) (hl : 15 ≤ l) :
    capMark positions (l + 1) idx =
      if 2 * idx + 1 < levelSize l then
        capMark positions l (2 * idx) || capMark positions l (2 * idx + 1)
      else if 2 * idx < levelSize l then
        capMark positions l (2 * idx)
      else false := by
  have h1 : ¬ (l + 1 < 15) := by omega
  have h2 : ¬ (l + 1 = 15) := by omega
  simp only [capMark, h1, h2, ite_false]

theorem capMark_24_eq_true (positions : Positions) (hne : positions.Nonempty) :
    capMark positions 24 0 = true := by
  obtain ⟨i, hi⟩ := hne
  have h15 : capMark positions 15 (capLeafOf i) = true := by
    rw [capMark_15, decide_eq_true_eq]
    exact ⟨i, hi, rfl⟩
  have hstep : ∀ l idx, 15 ≤ l → idx < levelSize l →
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
  have h16 := hstep 15 _ (by omega) (by rw [levelSize_15]; exact capLeafOf_lt i) h15
  have h17 := hstep 16 _ (by omega) (by have := capLeafOf_lt i; change _ < 171; omega) h16
  have h18 := hstep 17 _ (by omega) (by have := capLeafOf_lt i; change _ < 86; omega) h17
  have h19 := hstep 18 _ (by omega) (by have := capLeafOf_lt i; change _ < 43; omega) h18
  have h20 := hstep 19 _ (by omega) (by have := capLeafOf_lt i; change _ < 22; omega) h19
  have h21 := hstep 20 _ (by omega) (by have := capLeafOf_lt i; change _ < 11; omega) h20
  have h22 := hstep 21 _ (by omega) (by have := capLeafOf_lt i; change _ < 6; omega) h21
  have h23 := hstep 22 _ (by omega) (by have := capLeafOf_lt i; change _ < 3; omega) h22
  have h24 := hstep 23 _ (by omega) (by have := capLeafOf_lt i; change _ < 2; omega) h23
  have hz : capLeafOf i / 2 / 2 / 2 / 2 / 2 / 2 / 2 / 2 / 2 = 0 := by
    have := capLeafOf_lt i; omega
  rwa [hz] at h24

def levelFrontierCount (positions : Positions) (l : Nat) : Nat :=
  ((Finset.range (levelSize l / 2)).filter
    (fun q => capMark positions l (2 * q) != capMark positions l (2 * q + 1))).card

def capFrontierCount (positions : Positions) : Nat :=
  ∑ step ∈ Finset.range 9, levelFrontierCount positions (15 + step)

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

/-- Base level L15 (342 nodes = 171 pairs): frontier_15 + unmarked_16 <= 171. -/
theorem frontier_15_add_unmarked_16 (positions : Positions) :
    levelFrontierCount positions 15 + levelUnmarkedCount positions 16 ≤ 171 := by
  unfold levelFrontierCount levelUnmarkedCount
  have h15 : levelSize 15 / 2 = 171 := by decide
  have h16 : levelSize 16 = 171 := by decide
  rw [h15, h16, card_filter_eq_sum, card_filter_eq_sum, ← Finset.sum_add_distrib]
  calc
    ∑ q ∈ Finset.range 171,
        ((if (capMark positions 15 (2 * q) != capMark positions 15 (2 * q + 1)) = true then 1 else 0) +
         (if (!capMark positions 16 q) = true then 1 else 0))
      ≤ ∑ _q ∈ Finset.range 171, 1 := by
        apply Finset.sum_le_sum
        intro q hq
        have hq' : q < 171 := Finset.mem_range.mp hq
        have hpair : 2 * q + 1 < levelSize 15 := by rw [levelSize_15]; omega
        rw [capMark_succ positions 15 q (by omega), if_pos hpair]
        cases capMark positions 15 (2 * q) <;> cases capMark positions 15 (2 * q + 1) <;> decide
    _ = 171 := by simp

/-- Telescoping step for every level l >= 15: frontier_l + unmarked_{l+1} <= unmarked_l. -/
theorem frontier_add_unmarked_succ (positions : Positions) (l : Nat) (hl : 15 ≤ l) :
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

/-- Universal cap frontier bound: at most 171 frontier digests for every subset of positions. -/
theorem cap_frontier_le_171 (positions : Positions) :
    capFrontierCount positions ≤ 171 := by
  have h15 : levelFrontierCount positions 15 + levelUnmarkedCount positions 16 ≤ 171 :=
    frontier_15_add_unmarked_16 positions
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
  have h23 : levelFrontierCount positions 23 + levelUnmarkedCount positions 24 ≤ levelUnmarkedCount positions 23 :=
    frontier_add_unmarked_succ positions 23 (by omega)
  have hsum : capFrontierCount positions =
      levelFrontierCount positions 15 + levelFrontierCount positions 16 +
      levelFrontierCount positions 17 + levelFrontierCount positions 18 +
      levelFrontierCount positions 19 + levelFrontierCount positions 20 +
      levelFrontierCount positions 21 + levelFrontierCount positions 22 +
      levelFrontierCount positions 23 := by
    unfold capFrontierCount
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.zero_add]
  omega

/-- Marked nodes never increase going up the cap tree. -/
theorem levelMarked_succ_le (positions : Positions) (l : Nat) (hl : 15 ≤ l) :
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

theorem levelMarked_15_le_card (positions : Positions) :
    levelMarkedCount positions 15 ≤ positions.card := by
  unfold levelMarkedCount
  have hsub : (Finset.range (levelSize 15)).filter (fun idx => capMark positions 15 idx = true) ⊆
      positions.image capLeafOf := by
    intro idx hidx
    simp only [Finset.mem_filter, capMark_15, decide_eq_true_eq] at hidx
    obtain ⟨_, i, hi, rfl⟩ := hidx
    exact Finset.mem_image_of_mem capLeafOf hi
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

theorem levelMarked_le_card (positions : Positions) (l : Nat) (hl : 15 ≤ l) :
    levelMarkedCount positions l ≤ positions.card := by
  obtain ⟨d, rfl⟩ : ∃ d, l = 15 + d := ⟨l - 15, by omega⟩
  clear hl
  induction d with
  | zero => exact levelMarked_15_le_card positions
  | succ d ih =>
    exact (levelMarked_succ_le positions (15 + d) (by omega)).trans ih

/-! ### Exact Byte-Aligned Proof Serialization and Size Bounds -/

def bitsToBytes {w : Nat} (v : BitVec w) (n : Nat) : List Byte :=
  (List.range n).map fun j => v.extractLsb' (8 * j) 8

theorem bitsToBytes_length {w : Nat} (v : BitVec w) (n : Nat) :
    (bitsToBytes v n).length = n := by
  simp [bitsToBytes]

def l0SiblingsProof (nodes : Nat → Nat → Digest) (i : Index) : List Byte :=
  let g := i.val / 3
  let r := i.val % 3
  if g = FULL_TRIPLETS then []
  else if r = 0 then bitsToBytes (nodes 0 (3 * g + 1)) 32 ++ bitsToBytes (nodes 0 (3 * g + 2)) 32
  else if r = 1 then bitsToBytes (nodes 0 (3 * g)) 32 ++ bitsToBytes (nodes 0 (3 * g + 2)) 32
  else bitsToBytes (nodes 0 (3 * g)) 32 ++ bitsToBytes (nodes 0 (3 * g + 1)) 32

def binPathProof (nodes : Nat → Nat → Digest) (g : Nat) : List Byte :=
  (List.range 13).flatMap fun step =>
    let l := 2 + step
    let idx := g >>> (step + 1)
    let sib := idx ^^^ 1
    if sib < levelSize l then bitsToBytes (nodes l sib) 30 else []

def recordProof (nodes : Nat → Nat → Digest) (salts : Index → Salt192) (i : Index) : List Byte :=
  let g := i.val / 3
  bitsToBytes (salts i) 24 ++
  l0SiblingsProof nodes i ++
  bitsToBytes (nodes 1 (g ^^^ 1)) 32 ++
  binPathProof nodes g

def capLevelFrontierProof (nodes : Nat → Nat → Digest) (positions : Positions) (l : Nat) : List Byte :=
  (List.range (levelSize l / 2)).flatMap fun q =>
    let mL := capMark positions l (2 * q)
    let mR := capMark positions l (2 * q + 1)
    if mL = mR then []
    else if !mL then bitsToBytes (nodes l (2 * q)) 30
    else bitsToBytes (nodes l (2 * q + 1)) 30

def capFrontierProof (nodes : Nat → Nat → Digest) (positions : Positions) : List Byte :=
  (List.range 9).flatMap fun step => capLevelFrontierProof nodes positions (15 + step)

def referenceProof (nodes : Nat → Nat → Digest) (salts : Index → Salt192)
    (positions : Positions) : Proof :=
  if positions.card = 0 then []
  else
    (positions.sort (· ≤ ·)).flatMap (recordProof nodes salts) ++
    capFrontierProof nodes positions

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

theorem binPathProof_length_le (nodes : Nat → Nat → Digest) (g : Nat) :
    (binPathProof nodes g).length ≤ 390 := by
  unfold binPathProof
  have hle : ∀ step ∈ List.range 13,
      (if ((g >>> (step + 1)) ^^^ 1) < levelSize (2 + step)
       then bitsToBytes (nodes (2 + step) ((g >>> (step + 1)) ^^^ 1)) 30 else []).length ≤ 30 := by
    intro step _
    split <;> simp [bitsToBytes]
  have hsum := list_map_sum_le (List.range 13)
    (fun step => (if ((g >>> (step + 1)) ^^^ 1) < levelSize (2 + step)
       then bitsToBytes (nodes (2 + step) ((g >>> (step + 1)) ^^^ 1)) 30 else []).length)
    (fun _ => 30) hle
  rw [List.length_flatMap]
  simpa using hsum

theorem recordProof_length_le_510 (nodes : Nat → Nat → Digest) (salts : Index → Salt192) (i : Index) :
    (recordProof nodes salts i).length ≤ 510 := by
  unfold recordProof
  simp only [List.length_append, bitsToBytes_length]
  have h0 := l0SiblingsProof_length_le nodes i
  have h1 := binPathProof_length_le nodes (i.val / 3)
  omega

theorem capLevelFrontierProof_length (nodes : Nat → Nat → Digest) (positions : Positions) (l : Nat) :
    (capLevelFrontierProof nodes positions l).length = 30 * levelFrontierCount positions l := by
  unfold capLevelFrontierProof levelFrontierCount
  rw [List.length_flatMap, card_filter_eq_sum, Finset.mul_sum, list_sum_range]
  apply Finset.sum_congr rfl
  intro q _
  dsimp only
  cases capMark positions l (2 * q) <;> cases capMark positions l (2 * q + 1) <;> simp [bitsToBytes]

theorem capFrontierProof_length (nodes : Nat → Nat → Digest) (positions : Positions) :
    (capFrontierProof nodes positions).length = 30 * capFrontierCount positions := by
  unfold capFrontierProof capFrontierCount
  rw [List.length_flatMap, list_sum_range, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro step _
  exact capLevelFrontierProof_length nodes positions (15 + step)

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

theorem referenceProof_length_le (nodes : Nat → Nat → Digest) (salts : Index → Salt192)
    (positions : Positions) :
    (referenceProof nodes salts positions).length ≤ 510 * positions.card + 5130 := by
  unfold referenceProof
  split
  · simp
  · rw [List.length_append, List.length_flatMap, capFrontierProof_length]
    have hrec := list_map_sum_le (positions.sort (· ≤ ·))
      (fun i => (recordProof nodes salts i).length) (fun _ => 510)
      (fun i _ => recordProof_length_le_510 nodes salts i)
    have hrec2 : ((positions.sort (· ≤ ·)).map fun _ => 510).sum = 510 * positions.card := by
      simp [Nat.mul_comm]
    have hcap := cap_frontier_le_171 positions
    omega

theorem referenceProof_congr_nodes (n1 n2 : Nat → Nat → Digest)
    (hagree : ∀ l ≤ 24, ∀ idx < levelSize l, n1 l idx = n2 l idx)
    (salts : Index → Salt192) (positions : Positions) :
    referenceProof n1 salts positions = referenceProof n2 salts positions := by
  unfold referenceProof
  split_ifs
  · rfl
  · refine congrArg₂ List.append ?_ ?_
    · apply List.flatMap_congr; intro i _
      unfold recordProof l0SiblingsProof binPathProof
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
        have hs : step < 13 := List.mem_range.mp hstep
        split_ifs with hlt
        · rw [hagree (2 + step) (by omega) _ hlt]
        · rfl
    · unfold capFrontierProof capLevelFrontierProof
      apply List.flatMap_congr; intro step hstep
      have hs : step < 9 := List.mem_range.mp hstep
      apply List.flatMap_congr; intro q hq
      have hq' : q < levelSize (15 + step) / 2 := List.mem_range.mp hq
      dsimp only
      split_ifs
      · rfl
      · rw [hagree (15 + step) (by omega) (2 * q) (by omega)]
      · rw [hagree (15 + step) (by omega) (2 * q + 1) (by omega)]

theorem referenceProof_length_128_le (nodes : Nat → Nat → Digest) (salts : Index → Salt192)
    (positions : Positions) (hcard : positions.card = BATCH) :
    (referenceProof nodes salts positions).length ≤ 70410 := by
  have h := referenceProof_length_le nodes salts positions
  rw [hcard] at h
  change _ ≤ 510 * 128 + 5130 at h
  omega

theorem referenceProof_length_le_cap (nodes : Nat → Nat → Digest) (salts : Index → Salt192)
    (positions : Positions) :
    (referenceProof nodes salts positions).length ≤ proofCap := by
  have h := referenceProof_length_le nodes salts positions
  have hc : positions.card ≤ LENGTH := by
    simpa only [Index, Fintype.card_fin] using Finset.card_le_univ positions
  change positions.card ≤ 16777216 at hc
  change _ ≤ 8556390424
  omega

end CommitGolfCandidate.R4
