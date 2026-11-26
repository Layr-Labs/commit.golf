import CommitGolf.Parameters
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! Mathematical model of the pure 3-ary FIFO queue vector commitment tree with
paired 192-bit late salts (shared-midpoint 40-byte pair rows), full 256-bit digests,
and a self-similar `M = 143` deduplicated cap (`286` cap leaves, `142` 3-ary internal
cap nodes, and `1` 2-ary root node). Parameterized over any 768->256 compression function. -/
namespace CommitGolfCandidate
open CommitGolf

abbrev Salt192 := BitVec 192
abbrev PairRand := BitVec 320
abbrev Digest := BitVec 256
abbrev Comp96 := BitVec 768 → Digest

/-! ### Exact Pure 3-ary FIFO Queue Geometry and Paired Late-Salt Row Layout -/

def QUEUE_CALLS : Nat := LENGTH / 2
def TREE_NODES : Nat := LENGTH + QUEUE_CALLS
def ROOT_NODE : Nat := TREE_NODES - 1

def CAP_CALLS : Nat := 143
def CAP_START : Nat := TREE_NODES - CAP_CALLS
def CAP_LEAVES : Nat := 2 * CAP_CALLS
def CAP_LEAF_LO : Nat := CAP_START - CAP_LEAVES
def CAP_NODES : Nat := CAP_LEAVES + CAP_CALLS
def CAP_BOTTOM_TRIPLETS : Nat := 95

def PAIR_STRIDE : Nat := 184
def PAIR_RAND_BYTES : Nat := 40

def treeBytes : Nat := TREE_NODES * 32
def rowOff : Nat := treeBytes
def rowBytes : Nat := (LENGTH / 2) * PAIR_STRIDE
def trapdoorBytes : Nat := rowOff + rowBytes
def proofCap : Nat := 11140077536

def saltOff (i : Index) : Nat :=
  rowOff + PAIR_STRIDE * (i.val / 2) + if i.val % 2 = 0 then 72 else 88

theorem queueCalls_eq : QUEUE_CALLS = 8388608 := by decide
theorem treeNodes_eq : TREE_NODES = 25165824 := by decide
theorem rootNode_eq : ROOT_NODE = 25165823 := by decide
theorem capStart_eq : CAP_START = 25165681 := by decide
theorem capLeaves_eq : CAP_LEAVES = 286 := by decide
theorem capLeafLo_eq : CAP_LEAF_LO = 25165395 := by decide
theorem capNodes_eq : CAP_NODES = 429 := by decide
theorem treeBytes_eq : treeBytes = 805306368 := by decide
theorem rowOff_eq : rowOff = 805306368 := by decide
theorem rowBytes_eq : rowBytes = 1543503872 := by decide
theorem trapdoorBytes_eq : trapdoorBytes = 2348810240 := by decide

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

/-! ### Late-Salt Leaf Compression Inputs and 3-ary Queue Tree Semantics -/

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

theorem ternaryInput_inj {a0 a1 a2 b0 b1 b2 : Digest}
    (h : ternaryInput a0 a1 a2 = ternaryInput b0 b1 b2) :
    a0 = b0 ∧ a1 = b1 ∧ a2 = b2 := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [ternaryInput_d0] using congrArg (fun v => v.extractLsb' 0 256) h
  · simpa [ternaryInput_d1] using congrArg (fun v => v.extractLsb' 256 256) h
  · simpa [ternaryInput_d2] using congrArg (fun v => v.extractLsb' 512 256) h

/-- Pure 3-ary FIFO queue tree node values built from an arbitrary leaf-digest vector.
Nodes `0 .. 2^24 - 1` are leaves; nodes `2^24 + j` (`0 ≤ j < 2^23 - 1`) hash `(3j, 3j+1, 3j+2)`;
the root `25,165,823` hashes `(25165821, 25165822, 0)`. -/
def nodeValFromLeaves (c : Comp96) (leaves : Index → Digest) (v : Nat) : Digest :=
  if h0 : v < LENGTH then
    leaves ⟨v, h0⟩
  else if h1 : v < ROOT_NODE then
    let j := v - LENGTH
    c (ternaryInput
      (nodeValFromLeaves c leaves (3 * j))
      (nodeValFromLeaves c leaves (3 * j + 1))
      (nodeValFromLeaves c leaves (3 * j + 2)))
  else if v = ROOT_NODE then
    c (ternaryInput
      (nodeValFromLeaves c leaves 25165821)
      (nodeValFromLeaves c leaves 25165822)
      0)
  else 0
termination_by v
decreasing_by
  all_goals (unfold ROOT_NODE TREE_NODES QUEUE_CALLS LENGTH LOG_LENGTH at *; omega)

theorem nodeValFromLeaves_leaf (c : Comp96) (leaves : Index → Digest) (v : Nat) (hv : v < LENGTH) :
    nodeValFromLeaves c leaves v = leaves ⟨v, hv⟩ := by
  rw [nodeValFromLeaves, dif_pos hv]

theorem nodeValFromLeaves_internal (c : Comp96) (leaves : Index → Digest) (j : Nat)
    (hj : j < QUEUE_CALLS - 1) :
    nodeValFromLeaves c leaves (LENGTH + j) =
      c (ternaryInput
        (nodeValFromLeaves c leaves (3 * j))
        (nodeValFromLeaves c leaves (3 * j + 1))
        (nodeValFromLeaves c leaves (3 * j + 2))) := by
  have hge : ¬ (LENGTH + j < LENGTH) := by omega
  have hlt : LENGTH + j < ROOT_NODE := by
    unfold ROOT_NODE TREE_NODES QUEUE_CALLS LENGTH LOG_LENGTH at *; omega
  rw [nodeValFromLeaves, dif_neg hge, dif_pos hlt]
  simp only [Nat.add_sub_cancel_left]

theorem nodeValFromLeaves_root (c : Comp96) (leaves : Index → Digest) :
    nodeValFromLeaves c leaves ROOT_NODE =
      c (ternaryInput
        (nodeValFromLeaves c leaves 25165821)
        (nodeValFromLeaves c leaves 25165822)
        0) := by
  have hge : ¬ (ROOT_NODE < LENGTH) := by decide
  have hnot : ¬ (ROOT_NODE < ROOT_NODE) := by omega
  rw [nodeValFromLeaves, dif_neg hge, dif_neg hnot, if_pos rfl]

theorem nodeValFromLeaves_capInternal (c : Comp96) (leaves : Index → Digest) (j : Nat)
    (hj : j < 142) :
    nodeValFromLeaves c leaves (CAP_START + j) =
      c (ternaryInput
        (nodeValFromLeaves c leaves (CAP_LEAF_LO + 3 * j))
        (nodeValFromLeaves c leaves (CAP_LEAF_LO + 3 * j + 1))
        (nodeValFromLeaves c leaves (CAP_LEAF_LO + 3 * j + 2))) := by
  have h1 := capStart_eq
  have h2 := capLeafLo_eq
  have h3 := queueCalls_eq
  have h4 : CAP_CALLS = 143 := rfl
  have h5 : LENGTH = 16777216 := by decide
  have hidx : CAP_START + j = LENGTH + (QUEUE_CALLS - CAP_CALLS + j) := by omega
  have hlt : QUEUE_CALLS - CAP_CALLS + j < QUEUE_CALLS - 1 := by omega
  have hc0 : 3 * (QUEUE_CALLS - CAP_CALLS + j) = CAP_LEAF_LO + 3 * j := by omega
  rw [hidx, nodeValFromLeaves_internal c leaves _ hlt, hc0]

def nodeVal (c : Comp96) (msg : Message) (salts : Index → Salt192) (v : Nat) : Digest :=
  nodeValFromLeaves c (fun i => leafDigest c i (salts i) (msg i)) v

def rootVal (c : Comp96) (msg : Message) (salts : Index → Salt192) : Digest :=
  nodeVal c msg salts ROOT_NODE

/-! ### Queue Tree Climbing and Exact Depth Bounds (`9 ≤ climbSteps ≤ 10`) -/

def parentNode (v : Nat) : Nat := LENGTH + v / 3

def climbIter (v : Nat) : Nat → Nat
  | 0 => v
  | n + 1 => climbIter (parentNode v) n

theorem parentNode_mono {a b : Nat} (h : a ≤ b) : parentNode a ≤ parentNode b := by
  unfold parentNode
  exact Nat.add_le_add_left (Nat.div_le_div_right h) LENGTH

theorem climbIter_mono {a b : Nat} (n : Nat) (h : a ≤ b) : climbIter a n ≤ climbIter b n := by
  induction n generalizing a b with
  | zero => exact h
  | succ n ih => exact ih (parentNode_mono h)

theorem climbIter_zero_10 : CAP_LEAF_LO ≤ climbIter 0 10 := by decide

/-- Number of 3-ary climb steps from node `v` until reaching `[CAP_LEAF_LO, CAP_START)`. -/
def climbStepsFrom (v : Nat) : Nat :=
  if h : v < CAP_LEAF_LO then 1 + climbStepsFrom (parentNode v) else 0
termination_by CAP_LEAF_LO - v
decreasing_by
  unfold parentNode CAP_LEAF_LO CAP_START TREE_NODES QUEUE_CALLS CAP_CALLS CAP_LEAVES LENGTH LOG_LENGTH at *
  omega

/-- Cap leaf node index (`∈ [CAP_LEAF_LO, CAP_START)`) reached by climbing from `v`. -/
def climbEndFrom (v : Nat) : Nat :=
  if h : v < CAP_LEAF_LO then climbEndFrom (parentNode v) else v
termination_by CAP_LEAF_LO - v
decreasing_by
  unfold parentNode CAP_LEAF_LO CAP_START TREE_NODES QUEUE_CALLS CAP_CALLS CAP_LEAVES LENGTH LOG_LENGTH at *
  omega

theorem climbStepsFrom_of_lt {v : Nat} (h : v < CAP_LEAF_LO) :
    climbStepsFrom v = 1 + climbStepsFrom (parentNode v) := by
  rw [climbStepsFrom, dif_pos h]

theorem climbStepsFrom_of_ge {v : Nat} (h : CAP_LEAF_LO ≤ v) :
    climbStepsFrom v = 0 := by
  rw [climbStepsFrom, dif_neg (by omega)]

theorem climbEndFrom_of_lt {v : Nat} (h : v < CAP_LEAF_LO) :
    climbEndFrom v = climbEndFrom (parentNode v) := by
  rw [climbEndFrom, dif_pos h]

theorem climbEndFrom_of_ge {v : Nat} (h : CAP_LEAF_LO ≤ v) :
    climbEndFrom v = v := by
  rw [climbEndFrom, dif_neg (by omega)]

theorem climbStepsFrom_le_of_iter {v n : Nat} (h : CAP_LEAF_LO ≤ climbIter v n) :
    climbStepsFrom v ≤ n := by
  induction n generalizing v with
  | zero =>
    change CAP_LEAF_LO ≤ v at h
    rw [climbStepsFrom_of_ge h]
  | succ n ih =>
    by_cases hv : v < CAP_LEAF_LO
    · rw [climbStepsFrom_of_lt hv]
      have hsub := ih (v := parentNode v) h
      omega
    · rw [climbStepsFrom_of_ge (by omega)]
      omega

theorem climbStepsFrom_le_10 (v : Nat) : climbStepsFrom v ≤ 10 :=
  climbStepsFrom_le_of_iter (climbIter_zero_10.trans (climbIter_mono 10 (Nat.zero_le v)))

theorem climbStepsFrom_pos (i : Index) : 0 < climbStepsFrom i.val := by
  have hi : i.val < CAP_LEAF_LO := by
    have := i.isLt
    have h1 := capLeafLo_eq
    have h2 : LENGTH = 16777216 := by decide
    omega
  rw [climbStepsFrom_of_lt hi]
  omega

theorem climbEndFrom_bounds {v : Nat} (hv : v < CAP_START) :
    CAP_LEAF_LO ≤ climbEndFrom v ∧ climbEndFrom v < CAP_START := by
  by_cases hlt : v < CAP_LEAF_LO
  · rw [climbEndFrom_of_lt hlt]
    have hpar : parentNode v < CAP_START := by
      unfold parentNode
      have h1 := capLeafLo_eq
      have h2 := capStart_eq
      have h3 : LENGTH = 16777216 := by decide
      omega
    exact climbEndFrom_bounds hpar
  · rw [climbEndFrom_of_ge (by omega)]
    exact ⟨by omega, hv⟩
termination_by CAP_LEAF_LO - v
decreasing_by
  unfold parentNode
  have h1 := capLeafLo_eq
  have h2 : LENGTH = 16777216 := by decide
  omega

/-- Cap leaf index `∈ [0, 286)` reached by climbing from message leaf `i`. -/
def capLeafOf (i : Index) : Nat := climbEndFrom i.val - CAP_LEAF_LO

theorem capLeafOf_lt (i : Index) : capLeafOf i < CAP_LEAVES := by
  unfold capLeafOf
  have hi : i.val < CAP_START := by
    have := i.isLt
    have h1 := capStart_eq
    have h2 : LENGTH = 16777216 := by decide
    omega
  have hb := climbEndFrom_bounds hi
  have h1 := capLeafLo_eq
  have h2 := capStart_eq
  have h3 := capLeaves_eq
  omega

theorem climbEndFrom_eq_capLeafOf (i : Index) :
    climbEndFrom i.val = CAP_LEAF_LO + capLeafOf i := by
  unfold capLeafOf
  have hi : i.val < CAP_START := by
    have := i.isLt
    have h1 := capStart_eq
    have h2 : LENGTH = 16777216 := by decide
    omega
  have hb := climbEndFrom_bounds hi
  omega

/-! ### Self-Similar `M = 143` Cap Marking, `E ≤ 191`, and `I_m ≤ 6 * k` -/

/-- Boolean marking of all `429` cap nodes (`0..285` cap leaves, `286..427` 3-ary internal nodes,
`428` 2-ary root node). -/
def capMark (positions : Positions) (u : Nat) : Bool :=
  if u < CAP_LEAVES then
    decide (∃ i ∈ positions, capLeafOf i = u)
  else if u < 428 then
    let j := u - CAP_LEAVES
    capMark positions (3 * j) || capMark positions (3 * j + 1) || capMark positions (3 * j + 2)
  else if u = 428 then
    capMark positions 426 || capMark positions 427
  else false
termination_by u
decreasing_by
  all_goals (have := capLeaves_eq; omega)

theorem capMark_leaf (positions : Positions) (c : Nat) (hc : c < 286) :
    capMark positions c = decide (∃ i ∈ positions, capLeafOf i = c) := by
  rw [capMark]
  have hlt : c < CAP_LEAVES := by rw [capLeaves_eq]; exact hc
  simp only [hlt, ite_true]

theorem capMark_internal (positions : Positions) (j : Nat) (hj : j < 142) :
    capMark positions (286 + j) =
      (capMark positions (3 * j) || capMark positions (3 * j + 1) || capMark positions (3 * j + 2)) := by
  have h1 : ¬ (286 + j < 286) := by omega
  have h2 : 286 + j < 428 := by omega
  rw [capMark]
  simp only [capLeaves_eq, h1, ite_false, h2, ite_true, Nat.add_sub_cancel_left]

theorem capMark_root (positions : Positions) :
    capMark positions 428 = (capMark positions 426 || capMark positions 427) := by
  have h1 : ¬ (428 < CAP_LEAVES) := by rw [capLeaves_eq]; omega
  have h2 : ¬ (428 < 428) := by omega
  rw [capMark]
  simp only [h1, h2, ite_false, ite_true]

/-- Parent of cap node `u ∈ [0, 429)` inside the cap (fixed point at root `428`). -/
def capParent (u : Nat) : Nat := 286 + u / 3

theorem capMark_parent_true (positions : Positions) {u : Nat} (hu : u < 429)
    (hm : capMark positions u = true) :
    capMark positions (capParent u) = true := by
  unfold capParent
  by_cases h428 : u = 428
  · subst h428; simpa using hm
  · by_cases h426 : u < 426
    · have hj : u / 3 < 142 := by omega
      rw [capMark_internal positions (u / 3) hj]
      have hrem : u = 3 * (u / 3) ∨ u = 3 * (u / 3) + 1 ∨ u = 3 * (u / 3) + 2 := by omega
      rcases hrem with h | h | h <;> rw [← h, hm] <;> simp
    · have hdiv : u / 3 = 142 := by omega
      rw [hdiv, show 286 + 142 = 428 from rfl, capMark_root]
      have hcases : u = 426 ∨ u = 427 := by omega
      rcases hcases with rfl | rfl <;> simp [hm]

private theorem capParent6_eq_428 (c : Nat) (hc : c < 286) :
    capParent (capParent (capParent (capParent (capParent (capParent c))))) = 428 := by
  unfold capParent; omega

private theorem capParent_lt_429 {u : Nat} (hu : u < 429) : capParent u < 429 := by
  unfold capParent; omega

theorem capMark_428_eq_true (positions : Positions) (hne : positions.Nonempty) :
    capMark positions 428 = true := by
  obtain ⟨i, hi⟩ := hne
  have hc : capLeafOf i < 286 := by rw [← capLeaves_eq]; exact capLeafOf_lt i
  have h0 : capMark positions (capLeafOf i) = true := by
    rw [capMark_leaf positions _ hc, decide_eq_true_eq]
    exact ⟨i, hi, rfl⟩
  have h1 := capMark_parent_true positions (by omega) h0
  have h2 := capMark_parent_true positions (capParent_lt_429 (by omega)) h1
  have h3 := capMark_parent_true positions (capParent_lt_429 (capParent_lt_429 (by omega))) h2
  have h4 := capMark_parent_true positions (capParent_lt_429 (capParent_lt_429 (capParent_lt_429 (by omega)))) h3
  have h5 := capMark_parent_true positions (capParent_lt_429 (capParent_lt_429 (capParent_lt_429 (capParent_lt_429 (by omega))))) h4
  have h6 := capMark_parent_true positions (capParent_lt_429 (capParent_lt_429 (capParent_lt_429 (capParent_lt_429 (capParent_lt_429 (by omega)))))) h5
  rwa [capParent6_eq_428 _ hc] at h6

/-- Number of unmarked sibling frontier digests emitted for cap internal node `j ∈ [0, 143)`. -/
def capNodeFrontierCount (positions : Positions) (j : Nat) : Nat :=
  if j < 142 then
    if capMark positions (286 + j) then
      (if !capMark positions (3 * j) then 1 else 0) +
      (if !capMark positions (3 * j + 1) then 1 else 0) +
      (if !capMark positions (3 * j + 2) then 1 else 0)
    else 0
  else if j = 142 then
    if capMark positions 428 then
      (if !capMark positions 426 then 1 else 0) +
      (if !capMark positions 427 then 1 else 0)
    else 0
  else 0

def capFrontierCount (positions : Positions) : Nat :=
  ∑ j ∈ Finset.range 143, capNodeFrontierCount positions j

def capMarkedLeafCount (positions : Positions) : Nat :=
  ∑ c ∈ Finset.range 286, if capMark positions c then 1 else 0

def capMarkedInternalCount (positions : Positions) : Nat :=
  ∑ j ∈ Finset.range 143, if capMark positions (286 + j) then 1 else 0

private theorem sum_range_triples (f : Nat → Nat) (n : Nat) :
    ∑ i ∈ Finset.range (3 * n), f i =
      ∑ j ∈ Finset.range n, (f (3 * j) + f (3 * j + 1) + f (3 * j + 2)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 3 * (n + 1) = 3 * n + 1 + 1 + 1 by omega,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ]
    omega

/-- Exact identity for EVERY subset of positions (empty or nonempty):
`capFrontierCount + capMarkedLeafCount = 2 * capMarkedInternalCount`. -/
theorem capFrontier_add_leaves_eq (positions : Positions) :
    capFrontierCount positions + capMarkedLeafCount positions =
      2 * capMarkedInternalCount positions := by
  let b : Nat → Nat := fun u => if capMark positions u then 1 else 0
  have hstep : ∀ j < 142,
      capNodeFrontierCount positions j + (b (3 * j) + b (3 * j + 1) + b (3 * j + 2)) =
        3 * b (286 + j) := by
    intro j hj
    simp only [capNodeFrontierCount, hj, ite_true, b, capMark_internal positions j hj]
    cases capMark positions (3 * j) <;>
      cases capMark positions (3 * j + 1) <;>
      cases capMark positions (3 * j + 2) <;> decide
  have hroot :
      capNodeFrontierCount positions 142 + (b 426 + b 427) = 2 * b 428 := by
    simp only [capNodeFrontierCount, show ¬ (142 < 142) by omega, ite_false, ite_true, b,
      capMark_root positions]
    cases capMark positions 426 <;> cases capMark positions 427 <;> decide
  have hsum142 :
      (∑ j ∈ Finset.range 142, capNodeFrontierCount positions j) +
      (∑ j ∈ Finset.range 142, (b (3 * j) + b (3 * j + 1) + b (3 * j + 2))) =
      3 * (∑ j ∈ Finset.range 142, b (286 + j)) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    exact hstep j (Finset.mem_range.mp hj)
  have htriples :
      ∑ j ∈ Finset.range 142, (b (3 * j) + b (3 * j + 1) + b (3 * j + 2)) =
      ∑ u ∈ Finset.range 426, b u := by
    simpa [show 3 * 142 = 426 from rfl] using (sum_range_triples b 142).symm
  have hall428 :
      (∑ u ∈ Finset.range 426, b u) + (b 426 + b 427) =
      (∑ c ∈ Finset.range 286, b c) + (∑ j ∈ Finset.range 142, b (286 + j)) := by
    have h1 : (∑ u ∈ Finset.range 426, b u) + (b 426 + b 427) = ∑ u ∈ Finset.range 428, b u := by
      rw [show (428 : Nat) = 427 + 1 from rfl, Finset.sum_range_succ (f := b) 427,
        Finset.sum_range_succ (f := b) 426]
      omega
    have h2 : ∑ u ∈ Finset.range 428, b u =
        (∑ c ∈ Finset.range 286, b c) + (∑ j ∈ Finset.range 142, b (286 + j)) := by
      rw [show (428 : Nat) = 286 + 142 from rfl, Finset.sum_range_add]
    exact h1.trans h2
  have hf_split : capFrontierCount positions =
      (∑ j ∈ Finset.range 142, capNodeFrontierCount positions j) +
      capNodeFrontierCount positions 142 := by
    unfold capFrontierCount
    exact Finset.sum_range_succ _ 142
  have hi_split : capMarkedInternalCount positions =
      (∑ j ∈ Finset.range 142, b (286 + j)) + b 428 := by
    unfold capMarkedInternalCount
    exact Finset.sum_range_succ (fun j => b (286 + j)) 142
  have hl_eq : capMarkedLeafCount positions = ∑ c ∈ Finset.range 286, b c := rfl
  rw [hf_split, hi_split, hl_eq]
  rw [htriples] at hsum142
  omega

/-- Universal cap frontier bound: at most `191` frontier digests for EVERY subset of positions. -/
theorem capFrontierCount_le_191 (positions : Positions) :
    capFrontierCount positions ≤ 191 := by
  let b : Nat → Nat := fun u => if capMark positions u then 1 else 0
  have hid := capFrontier_add_leaves_eq positions
  have hsplit : capMarkedInternalCount positions =
      (∑ j ∈ Finset.range 95, b (286 + j)) + (∑ j ∈ Finset.range 48, b (286 + (95 + j))) := by
    unfold capMarkedInternalCount
    change ∑ j ∈ Finset.range (95 + 48), b (286 + j) = _
    rw [Finset.sum_range_add]
  have hbot_le_95 : ∑ j ∈ Finset.range 95, b (286 + j) ≤ 95 := by
    calc ∑ j ∈ Finset.range 95, b (286 + j)
      _ ≤ ∑ _j ∈ Finset.range 95, 1 := Finset.sum_le_sum (fun j _ => by simp only [b]; split_ifs <;> omega)
      _ = 95 := by simp
  have htop_le_48 : ∑ j ∈ Finset.range 48, b (286 + (95 + j)) ≤ 48 := by
    calc ∑ j ∈ Finset.range 48, b (286 + (95 + j))
      _ ≤ ∑ _j ∈ Finset.range 48, 1 := Finset.sum_le_sum (fun j _ => by simp only [b]; split_ifs <;> omega)
      _ = 48 := by simp
  have hbot_le_leaves : ∑ j ∈ Finset.range 95, b (286 + j) ≤ capMarkedLeafCount positions := by
    have hstep : ∑ j ∈ Finset.range 95, b (286 + j) ≤
        ∑ j ∈ Finset.range 95, (b (3 * j) + b (3 * j + 1) + b (3 * j + 2)) := by
      apply Finset.sum_le_sum
      intro j hj
      have hj' : j < 95 := Finset.mem_range.mp hj
      simp only [b, capMark_internal positions j (by omega)]
      cases capMark positions (3 * j) <;>
        cases capMark positions (3 * j + 1) <;>
        cases capMark positions (3 * j + 2) <;> decide
    have h285 : ∑ j ∈ Finset.range 95, (b (3 * j) + b (3 * j + 1) + b (3 * j + 2)) =
        ∑ c ∈ Finset.range 285, b c := by
      simpa [show 3 * 95 = 285 from rfl] using (sum_range_triples b 95).symm
    have h286 : ∑ c ∈ Finset.range 285, b c ≤ capMarkedLeafCount positions := by
      change ∑ c ∈ Finset.range 285, b c ≤ ∑ c ∈ Finset.range 286, b c
      rw [Finset.sum_range_succ (f := b) 285]
      omega
    exact hstep.trans (le_of_eq_of_le h285 h286)
  omega

/-- The set of all `≤ 6` internal cap ancestors (`∈ [286, 429)`) of cap leaf `c < 286`. -/
def capAncs (c : Nat) : Finset Nat :=
  let p1 := capParent c
  let p2 := capParent p1
  let p3 := capParent p2
  let p4 := capParent p3
  let p5 := capParent p4
  let p6 := capParent p5
  {p1, p2, p3, p4, p5, p6}

theorem capAncs_card_le_6 (c : Nat) : (capAncs c).card ≤ 6 := by
  unfold capAncs
  dsimp only
  have h1 := Finset.card_insert_le (capParent c)
    {capParent (capParent c), capParent (capParent (capParent c)),
     capParent (capParent (capParent (capParent c))),
     capParent (capParent (capParent (capParent (capParent c)))),
     capParent (capParent (capParent (capParent (capParent (capParent c)))))}
  have h2 := Finset.card_insert_le (capParent (capParent c))
    {capParent (capParent (capParent c)),
     capParent (capParent (capParent (capParent c))),
     capParent (capParent (capParent (capParent (capParent c)))),
     capParent (capParent (capParent (capParent (capParent (capParent c)))))}
  have h3 := Finset.card_insert_le (capParent (capParent (capParent c)))
    {capParent (capParent (capParent (capParent c))),
     capParent (capParent (capParent (capParent (capParent c)))),
     capParent (capParent (capParent (capParent (capParent (capParent c)))))}
  have h4 := Finset.card_insert_le (capParent (capParent (capParent (capParent c))))
    {capParent (capParent (capParent (capParent (capParent c)))),
     capParent (capParent (capParent (capParent (capParent (capParent c)))))}
  have h5 := Finset.card_insert_le (capParent (capParent (capParent (capParent (capParent c)))))
    {capParent (capParent (capParent (capParent (capParent (capParent c)))))}
  have h6 : ({capParent (capParent (capParent (capParent (capParent (capParent c)))))} : Finset Nat).card = 1 :=
    Finset.card_singleton _
  omega

private theorem mem_capAncs_of_parent {c u : Nat} (hc : c < 286) (hu : u ∈ capAncs c) :
    capParent u ∈ capAncs c := by
  unfold capAncs at hu ⊢
  dsimp only at hu ⊢
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu ⊢
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
  · right; left; rfl
  · right; right; left; rfl
  · right; right; right; left; rfl
  · right; right; right; right; left; rfl
  · right; right; right; right; right; rfl
  · right; right; right; right; right
    rw [capParent6_eq_428 c hc]
    unfold capParent; omega

theorem exists_leaf_of_capMark (positions : Positions) (u : Nat) :
    u < 429 → capMark positions u = true →
    ∃ i ∈ positions, (u < 286 ∧ capLeafOf i = u) ∨ u ∈ capAncs (capLeafOf i) := by
  induction u using Nat.strong_induction_on with
  | h u ih =>
    intro hu hm
    by_cases hleaf : u < 286
    · rw [capMark_leaf positions u hleaf, decide_eq_true_eq] at hm
      obtain ⟨i, hi, heq⟩ := hm
      exact ⟨i, hi, Or.inl ⟨hleaf, heq⟩⟩
    · have hchild : ∃ v < u, capParent v = u ∧ capMark positions v = true := by
        by_cases h428 : u < 428
        · let j := u - 286
          have hj : j < 142 := by omega
          have hu_eq : u = 286 + j := by omega
          rw [hu_eq, capMark_internal positions j hj] at hm
          simp only [Bool.or_eq_true] at hm
          rcases hm with (h0 | h1) | h2
          · exact ⟨3 * j, by omega, by unfold capParent; omega, h0⟩
          · exact ⟨3 * j + 1, by omega, by unfold capParent; omega, h1⟩
          · exact ⟨3 * j + 2, by omega, by unfold capParent; omega, h2⟩
        · have hu428 : u = 428 := by omega
          subst hu428
          rw [capMark_root] at hm
          simp only [Bool.or_eq_true] at hm
          rcases hm with h0 | h1
          · exact ⟨426, by omega, by unfold capParent; omega, h0⟩
          · exact ⟨427, by omega, by unfold capParent; omega, h1⟩
      obtain ⟨v, hvlt, hpar, hmv⟩ := hchild
      obtain ⟨i, hi, hcase⟩ := ih v hvlt (by omega) hmv
      refine ⟨i, hi, Or.inr ?_⟩
      rcases hcase with ⟨_, heq⟩ | hanc
      · rw [← hpar, ← heq]
        unfold capAncs
        simp
      · rw [← hpar]
        have hic : capLeafOf i < 286 := by rw [← capLeaves_eq]; exact capLeafOf_lt i
        exact mem_capAncs_of_parent hic hanc

/-- Marked internal cap nodes are bounded by `6 * positions.card` (guaranteeing `checkCalls ≤ 20 * k`). -/
theorem capMarkedInternalCount_le_6_mul_card (positions : Positions) :
    capMarkedInternalCount positions ≤ 6 * positions.card := by
  unfold capMarkedInternalCount
  rw [← Finset.card_filter]
  let S := ((Finset.range 143).filter (fun j => capMark positions (286 + j) = true)).image (286 + ·)
  have hcard_eq : ((Finset.range 143).filter (fun j => capMark positions (286 + j) = true)).card = S.card := by
    symm
    exact Finset.card_image_of_injective _ (fun a b h => by omega)
  have hsub : S ⊆ positions.biUnion (fun i => capAncs (capLeafOf i)) := by
    intro u hu
    simp only [S, Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hu
    obtain ⟨j, ⟨hj, hmj⟩, rfl⟩ := hu
    obtain ⟨i, hi, hcase⟩ := exists_leaf_of_capMark positions (286 + j) (by omega) hmj
    rcases hcase with ⟨hlt, _⟩ | hanc
    · omega
    · exact Finset.mem_biUnion.mpr ⟨i, hi, hanc⟩
  calc ((Finset.range 143).filter (fun j => capMark positions (286 + j) = true)).card
    _ = S.card := hcard_eq
    _ ≤ (positions.biUnion (fun i => capAncs (capLeafOf i))).card := Finset.card_le_card hsub
    _ ≤ ∑ i ∈ positions, (capAncs (capLeafOf i)).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ positions, 6 := Finset.sum_le_sum (fun i _ => capAncs_card_le_6 (capLeafOf i))
    _ = 6 * positions.card := by simp [Nat.mul_comm]

/-! ### Exact Proof Serialization and Size Bounds (`≤ 91,104 B` at `k = 128`) -/

def bitsToBytes {w : Nat} (v : BitVec w) (n : Nat) : List Byte :=
  (List.range n).map fun j => v.extractLsb' (8 * j) 8

theorem bitsToBytes_length {w : Nat} (v : BitVec w) (n : Nat) :
    (bitsToBytes v n).length = n := by
  simp [bitsToBytes]

def stepSiblingsProof (nodes : Nat → Digest) (v : Nat) : List Byte :=
  let t := 3 * (v / 3)
  let r := v % 3
  if r = 0 then bitsToBytes (nodes (t + 1)) 32 ++ bitsToBytes (nodes (t + 2)) 32
  else if r = 1 then bitsToBytes (nodes t) 32 ++ bitsToBytes (nodes (t + 2)) 32
  else bitsToBytes (nodes t) 32 ++ bitsToBytes (nodes (t + 1)) 32

theorem stepSiblingsProof_length (nodes : Nat → Digest) (v : Nat) :
    (stepSiblingsProof nodes v).length = 64 := by
  unfold stepSiblingsProof
  dsimp only
  split_ifs <;> simp [bitsToBytes]

def climbProofFrom (nodes : Nat → Digest) (v : Nat) : List Byte :=
  if v < CAP_LEAF_LO then
    stepSiblingsProof nodes v ++ climbProofFrom nodes (parentNode v)
  else []
termination_by CAP_LEAF_LO - v
decreasing_by
  unfold parentNode CAP_LEAF_LO CAP_START TREE_NODES QUEUE_CALLS CAP_CALLS CAP_LEAVES LENGTH LOG_LENGTH at *
  omega

theorem climbProofFrom_of_lt (nodes : Nat → Digest) {v : Nat} (h : v < CAP_LEAF_LO) :
    climbProofFrom nodes v = stepSiblingsProof nodes v ++ climbProofFrom nodes (parentNode v) := by
  rw [climbProofFrom]; simp only [h, ite_true]

theorem climbProofFrom_of_ge (nodes : Nat → Digest) {v : Nat} (h : CAP_LEAF_LO ≤ v) :
    climbProofFrom nodes v = [] := by
  rw [climbProofFrom]; simp only [show ¬ (v < CAP_LEAF_LO) by omega, ite_false]

theorem climbProofFrom_length (nodes : Nat → Digest) (v : Nat) :
    (climbProofFrom nodes v).length = 64 * climbStepsFrom v := by
  by_cases h : v < CAP_LEAF_LO
  · rw [climbProofFrom_of_lt nodes h, climbStepsFrom_of_lt h, List.length_append,
      stepSiblingsProof_length, climbProofFrom_length nodes (parentNode v)]
    omega
  · rw [climbProofFrom_of_ge nodes (by omega), climbStepsFrom_of_ge (by omega)]
    simp
termination_by CAP_LEAF_LO - v
decreasing_by
  unfold parentNode CAP_LEAF_LO CAP_START TREE_NODES QUEUE_CALLS CAP_CALLS CAP_LEAVES LENGTH LOG_LENGTH at *
  omega

def recordProof (nodes : Nat → Digest) (salts : Index → Salt192) (i : Index) : List Byte :=
  bitsToBytes (salts i) 24 ++ climbProofFrom nodes i.val

theorem recordProof_length_le_664 (nodes : Nat → Digest) (salts : Index → Salt192) (i : Index) :
    (recordProof nodes salts i).length ≤ 664 := by
  unfold recordProof
  rw [List.length_append, bitsToBytes_length, climbProofFrom_length]
  have hs := climbStepsFrom_le_10 i.val
  omega

def capNodeFrontierProof (nodes : Nat → Digest) (positions : Positions) (j : Nat) : List Byte :=
  if j < 142 then
    if capMark positions (286 + j) then
      (if !capMark positions (3 * j) then bitsToBytes (nodes (CAP_LEAF_LO + 3 * j)) 32 else []) ++
      (if !capMark positions (3 * j + 1) then bitsToBytes (nodes (CAP_LEAF_LO + 3 * j + 1)) 32 else []) ++
      (if !capMark positions (3 * j + 2) then bitsToBytes (nodes (CAP_LEAF_LO + 3 * j + 2)) 32 else [])
    else []
  else if j = 142 then
    if capMark positions 428 then
      (if !capMark positions 426 then bitsToBytes (nodes (CAP_LEAF_LO + 426)) 32 else []) ++
      (if !capMark positions 427 then bitsToBytes (nodes (CAP_LEAF_LO + 427)) 32 else [])
    else []
  else []

theorem capNodeFrontierProof_length (nodes : Nat → Digest) (positions : Positions) (j : Nat) :
    (capNodeFrontierProof nodes positions j).length = 32 * capNodeFrontierCount positions j := by
  unfold capNodeFrontierProof capNodeFrontierCount
  split_ifs <;> simp [bitsToBytes]

def capFrontierProof (nodes : Nat → Digest) (positions : Positions) : List Byte :=
  (List.range 143).flatMap (capNodeFrontierProof nodes positions)

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

theorem capFrontierProof_length (nodes : Nat → Digest) (positions : Positions) :
    (capFrontierProof nodes positions).length = 32 * capFrontierCount positions := by
  unfold capFrontierProof capFrontierCount
  rw [List.length_flatMap, list_sum_range, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact capNodeFrontierProof_length nodes positions j

def referenceProof (nodes : Nat → Digest) (salts : Index → Salt192)
    (positions : Positions) : Proof :=
  if positions.card = 0 then []
  else
    (positions.sort (· ≤ ·)).flatMap (recordProof nodes salts) ++
    capFrontierProof nodes positions

theorem referenceProof_length_le (nodes : Nat → Digest) (salts : Index → Salt192)
    (positions : Positions) :
    (referenceProof nodes salts positions).length ≤ 664 * positions.card + 6112 := by
  unfold referenceProof
  split
  · simp
  · rw [List.length_append, List.length_flatMap, capFrontierProof_length]
    have hrec := list_map_sum_le (positions.sort (· ≤ ·))
      (fun i => (recordProof nodes salts i).length) (fun _ => 664)
      (fun i _ => recordProof_length_le_664 nodes salts i)
    have hrec2 : ((positions.sort (· ≤ ·)).map fun _ => 664).sum = 664 * positions.card := by
      simp [Nat.mul_comm]
    have hcap := capFrontierCount_le_191 positions
    omega

theorem referenceProof_length_128_le (nodes : Nat → Digest) (salts : Index → Salt192)
    (positions : Positions) (hcard : positions.card = BATCH) :
    (referenceProof nodes salts positions).length ≤ 91104 := by
  have h := referenceProof_length_le nodes salts positions
  rw [hcard] at h
  change _ ≤ 664 * 128 + 6112 at h
  omega

theorem referenceProof_length_le_cap (nodes : Nat → Digest) (salts : Index → Salt192)
    (positions : Positions) :
    (referenceProof nodes salts positions).length ≤ proofCap := by
  have h := referenceProof_length_le nodes salts positions
  have hc : positions.card ≤ LENGTH := by
    simpa only [Index, Fintype.card_fin] using Finset.card_le_univ positions
  change positions.card ≤ 16777216 at hc
  change _ ≤ 11140077536
  omega

private theorem climbProofFrom_congr (n1 n2 : Nat → Digest)
    (hagree : ∀ v < ROOT_NODE, n1 v = n2 v) (v : Nat) :
    climbProofFrom n1 v = climbProofFrom n2 v := by
  by_cases h : v < CAP_LEAF_LO
  · rw [climbProofFrom_of_lt n1 h, climbProofFrom_of_lt n2 h]
    have hcap : CAP_LEAF_LO = 25165395 := capLeafLo_eq
    have hroot : ROOT_NODE = 25165823 := rootNode_eq
    have ht0 : 3 * (v / 3) < ROOT_NODE := by omega
    have ht1 : 3 * (v / 3) + 1 < ROOT_NODE := by omega
    have ht2 : 3 * (v / 3) + 2 < ROOT_NODE := by omega
    have hsib : stepSiblingsProof n1 v = stepSiblingsProof n2 v := by
      unfold stepSiblingsProof
      dsimp only
      rw [hagree _ ht0, hagree _ ht1, hagree _ ht2]
    rw [hsib, climbProofFrom_congr n1 n2 hagree (parentNode v)]
  · rw [climbProofFrom_of_ge n1 (by omega), climbProofFrom_of_ge n2 (by omega)]
termination_by CAP_LEAF_LO - v
decreasing_by
  unfold parentNode CAP_LEAF_LO CAP_START TREE_NODES QUEUE_CALLS CAP_CALLS CAP_LEAVES LENGTH LOG_LENGTH at *
  omega

/-- `referenceProof` depends only on non-root node digests (`v < ROOT_NODE`). -/
theorem referenceProof_congr_nodes (n1 n2 : Nat → Digest)
    (hagree : ∀ v < ROOT_NODE, n1 v = n2 v)
    (salts : Index → Salt192) (positions : Positions) :
    referenceProof n1 salts positions = referenceProof n2 salts positions := by
  unfold referenceProof
  split_ifs
  · rfl
  · refine congrArg₂ List.append ?_ ?_
    · apply List.flatMap_congr; intro i _
      unfold recordProof
      rw [climbProofFrom_congr n1 n2 hagree i.val]
    · unfold capFrontierProof
      apply List.flatMap_congr; intro j hj
      have hjlt : j < 143 := List.mem_range.mp hj
      have hcap : CAP_LEAF_LO = 25165395 := capLeafLo_eq
      have hroot : ROOT_NODE = 25165823 := rootNode_eq
      unfold capNodeFrontierProof
      by_cases h142 : j < 142
      · simp only [h142, ite_true]
        rw [hagree (CAP_LEAF_LO + 3 * j) (by omega),
            hagree (CAP_LEAF_LO + 3 * j + 1) (by omega),
            hagree (CAP_LEAF_LO + 3 * j + 2) (by omega)]
      · simp only [h142, ite_false]
        by_cases heq : j = 142
        · simp only [heq, ite_true]
          rw [hagree (CAP_LEAF_LO + 426) (by omega),
              hagree (CAP_LEAF_LO + 427) (by omega)]
        · simp only [heq, ite_false]

end CommitGolfCandidate
