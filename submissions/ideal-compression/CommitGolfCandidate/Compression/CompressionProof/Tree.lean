import CommitGolfCandidate.Compression.Compression
import CommitGolfCandidate.Compression.CompressionProof.Eval
import Mathlib.Data.Nat.Bitwise

/-! # Merkle trees for a fixed compression function

For a fixed `π`, every Merkle computation is deterministic. This file gives each one a pure
counterpart (`C`, `pParent`, `pLayers`, `pClimb`), proves that `π.eval` computes it with the
expected number of calls, and proves the two facts about paths that the certificate needs:

- an honest copath climbs back to the root (completeness);
- two paths from different leaves that reach the same root contain a collision of `C`
  (binding). -/

namespace CommitGolf.CompressionBaseline

-- The proofs mention numbers such as `2 ^ 256`; let Lean evaluate them without a warning.
set_option exponentiation.threshold 2000
open OracleComp OracleSpec

/-! ### The compression function, unfolded -/

/-- The state `compress L R` queries: the concatenation `L ‖ R`. -/
def cin (left right : Digest) : Input := (left ++ right).setWidth (DIGEST_BITS + DIGEST_BITS)

/-- The complete 256-bit compression output. -/
def trunc (y : Digest) : Digest := y

/-- A well-sized compression input; every 512-bit input satisfies this predicate. -/
def ZeroCap (x : Input) : Prop := x.toNat < 2 ^ (2 * DIGEST_BITS)

variable (π : Hash)

/-- `C(L, R)` for the fixed compression function `π`. -/
def C (left right : Digest) : Digest := trunc (π (cin left right))

theorem cin_injective {l r l' r' : Digest} (h : cin l r = cin l' r') : l = l' ∧ r = r' := by
  unfold cin at h
  have h2 : l ++ r = l' ++ r' := by
    have := congrArg (fun x : Input => x.setWidth (DIGEST_BITS + DIGEST_BITS)) h
    simpa [BitVec.setWidth_setWidth_of_le, DIGEST_BITS, DIGEST_BYTES] using this
  refine ⟨?_, ?_⟩
  · have := congrArg (fun x => BitVec.extractLsb' DIGEST_BITS DIGEST_BITS x) h2
    simpa [BitVec.extractLsb'_append_eq_left] using this
  · have := congrArg (fun x => BitVec.extractLsb' 0 DIGEST_BITS x) h2
    simpa [BitVec.extractLsb'_append_eq_right] using this

theorem zeroCap_cin (l r : Digest) : ZeroCap (cin l r) := by
  unfold ZeroCap cin
  rw [BitVec.toNat_setWidth, two_mul]
  calc (l ++ r).toNat % 2 ^ (DIGEST_BITS + DIGEST_BITS) ≤ (l ++ r).toNat := Nat.mod_le _ _
    _ < 2 ^ (DIGEST_BITS + DIGEST_BITS) := (l ++ r).isLt

theorem eval_compress (l r : Digest) : π.eval (compress l r) = (C π l r, 1) := by
  have : compress l r = Hash.fwd (cin l r) >>= fun y => pure (trunc y) := rfl
  rw [this, Hash.eval_fwd_bind]
  simp [C]

/-! ### Building the tree -/

/-- `parentLayer` for the fixed `π`. -/
def pParent : List Digest → List Digest
  | l :: r :: rest => C π l r :: pParent rest
  | _ => []

/-- `layers` for the fixed `π`. -/
def pLayers : Nat → List Digest → List (List Digest)
  | 0, leaves => [leaves]
  | d + 1, leaves => leaves :: pLayers d (pParent π leaves)

theorem eval_parentLayer (ds : List Digest) :
    π.eval (parentLayer ds) = (pParent π ds, ds.length / 2) := by
  induction ds using parentLayer.induct with
  | case1 l r rest ih =>
    simp only [parentLayer, Hash.eval_bind, eval_compress, ih, Hash.eval_pure, pParent]
    simp only [List.length_cons]; congr 1; omega
  | case2 ds h =>
    rw [parentLayer.eq_2 _ h, Hash.eval_pure]
    match ds, h with
    | [], _ => simp [pParent]
    | [_], _ => simp [pParent]
    | l :: r :: rest, h => exact (h l r rest rfl).elim

theorem length_pParent (ds : List Digest) : (pParent π ds).length = ds.length / 2 := by
  induction ds using parentLayer.induct with
  | case1 l r rest ih => simp only [pParent, List.length_cons, ih]; omega
  | case2 ds h =>
    match ds, h with
    | [], _ => simp [pParent]
    | [_], _ => simp [pParent]
    | l :: r :: rest, h => exact (h l r rest rfl).elim

/-- The `j`-th parent hashes the leaves `2j` and `2j + 1`. -/
theorem getD_pParent (ds : List Digest) (j : Nat) (hj : j < ds.length / 2) :
    (pParent π ds).getD j 0 = C π (ds.getD (2 * j) 0) (ds.getD (2 * j + 1) 0) := by
  induction ds using parentLayer.induct generalizing j with
  | case1 l r rest ih =>
    cases j with
    | zero => simp [pParent]
    | succ j =>
      simp only [pParent, List.getD_cons_succ]
      have h1 : 2 * (j + 1) = 2 * j + 2 := by ring
      rw [h1, ih j (by simp at hj; omega)]
      simp
  | case2 ds h =>
    match ds, h with
    | [], _ => simp at hj
    | [_], _ => simp at hj
    | l :: r :: rest, h => exact (h l r rest rfl).elim

theorem eval_layers (d : Nat) (leaves : List Digest) :
    (π.eval (layers d leaves)).1 = pLayers π d leaves ∧
      (π.eval (layers d leaves)).2 ≤ leaves.length := by
  induction d generalizing leaves with
  | zero => simp [layers, pLayers]
  | succ d ih =>
    simp only [layers, Hash.eval_bind, eval_parentLayer, Hash.eval_pure, pLayers]
    obtain ⟨h1, h2⟩ := ih (pParent π leaves)
    rw [length_pParent] at h2
    refine ⟨by rw [h1], by simp only [add_zero]; omega⟩

/-! ### Climbing a path -/

/-- The two children of the node on the path at the current level, in order: the current node
is a left child when the lowest bit of `index` is `0`. -/
def children (index : Nat) (node sibling : Digest) : Digest × Digest :=
  if index % 2 = 0 then (node, sibling) else (sibling, node)

/-- `climb` for the fixed `π`, one level per sibling; `index` is shifted right at each level. -/
def pClimb : Nat → Digest → List Digest → Digest
  | _, node, [] => node
  | index, node, sibling :: rest =>
      pClimb (index >>> 1) (C π (children index node sibling).1 (children index node sibling).2)
        rest

/-- The states `climb` queries, one per level, in order. -/
def climbInputs : Nat → Digest → List Digest → List Input
  | _, _, [] => []
  | index, node, sibling :: rest =>
      cin (children index node sibling).1 (children index node sibling).2 ::
        climbInputs (index >>> 1)
          (C π (children index node sibling).1 (children index node sibling).2) rest

/-- `climb`'s fold, started at level `n`. -/
theorem eval_climb_aux (index : Nat) (siblings : List Digest) (n : Nat) (node : Digest) :
    π.eval ((siblings.zipIdx n).foldlM (fun node (sibling, level) =>
      if (index >>> level) % 2 = 0 then compress node sibling else compress sibling node) node) =
      (pClimb π (index >>> n) node siblings, siblings.length) := by
  induction siblings generalizing n node with
  | nil => simp [pClimb]
  | cons s rest ih =>
    simp only [List.zipIdx_cons, List.foldlM_cons, Hash.eval_bind]
    have hstep : (if (index >>> n) % 2 = 0 then compress node s else compress s node) =
        compress (children (index >>> n) node s).1 (children (index >>> n) node s).2 := by
      unfold children; split <;> rfl
    rw [hstep, eval_compress, ih]
    simp [pClimb, Nat.shiftRight_add]
    omega

theorem eval_climb (index : Nat) (leaf : Digest) (siblings : List Digest) :
    π.eval (climb index leaf siblings) = (pClimb π index leaf siblings, siblings.length) := by
  simpa [climb] using eval_climb_aux π index siblings 0 leaf

theorem pLayers_ne_nil (d : Nat) (leaves : List Digest) : pLayers π d leaves ≠ [] := by
  cases d <;> simp [pLayers]

/-- Copaths peel off one layer at a time. -/
theorem copath_cons (leaves : List Digest) (tree : List (List Digest)) (d index : Nat) :
    copath (leaves :: tree) (d + 1) index =
      leaves.getD (index ^^^ 1) 0 :: copath tree d (index >>> 1) := by
  simp only [copath, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  apply List.map_congr_left
  intro level _
  rw [← Nat.shiftRight_add, Nat.add_comm]
  rfl

/-- **Honest paths reach the root.** -/
theorem pClimb_copath (d : Nat) (leaves : List Digest) (hlen : leaves.length = 2 ^ d)
    (index : Nat) (hindex : index < 2 ^ d) :
    pClimb π index (leaves.getD index 0) (copath (pLayers π d leaves) d index) =
      rootOf (pLayers π d leaves) := by
  induction d generalizing leaves index with
  | zero =>
    obtain ⟨a, rfl⟩ : ∃ a, leaves = [a] := List.length_eq_one_iff.mp (by simpa using hlen)
    have : index = 0 := by simpa using hindex
    subst this
    simp [copath, pClimb, pLayers, rootOf]
  | succ d ih =>
    have hP : (pParent π leaves).length = 2 ^ d := by
      rw [length_pParent, hlen, pow_succ]; simp
    have hj : index >>> 1 < 2 ^ d := by
      rw [Nat.shiftRight_eq_div_pow]; rw [pow_succ] at hindex; omega
    have hroot : rootOf (leaves :: pLayers π d (pParent π leaves)) =
        rootOf (pLayers π d (pParent π leaves)) := by
      simp [rootOf, List.getLast?_cons]
      cases h : (pLayers π d (pParent π leaves)).getLast? with
      | none => simp [List.getLast?_eq_none_iff, pLayers_ne_nil] at h
      | some l => simp
    simp only [pLayers, copath_cons, pClimb, hroot]
    rw [← ih (pParent π leaves) hP (index >>> 1) hj]
    congr 1
    have hj' : index >>> 1 < leaves.length / 2 := by rw [hlen, pow_succ]; simpa using hj
    rw [getD_pParent π leaves _ hj', Nat.shiftRight_eq_div_pow, pow_one]
    unfold children
    split
    · rename_i h
      rw [Nat.xor_one_of_even (Nat.even_iff.mpr h)]
      have e : 2 * (index / 2) = index := by omega
      rw [e]
    · rename_i h
      rw [Nat.xor_one_of_odd (Nat.odd_iff.mpr (by omega))]
      have e : 2 * (index / 2) = index - 1 := by omega
      have e' : index - 1 + 1 = index := by omega
      rw [e, e']

/-- **Two paths to one root collide.** If paths of equal length from different leaves at the same
index climb to the same node, two different queried states have the same truncated image. -/
theorem collision_of_pClimb_eq (index : Nat) (a a' : Digest) (s s' : List Digest)
    (hlen : s.length = s'.length) (hne : a ≠ a')
    (heq : pClimb π index a s = pClimb π index a' s') :
    ∃ x ∈ climbInputs π index a s, ∃ x' ∈ climbInputs π index a' s',
      x ≠ x' ∧ ZeroCap x ∧ ZeroCap x' ∧ trunc (π x) = trunc (π x') := by
  induction s generalizing s' index a a' with
  | nil =>
    cases s' with
    | nil => exact absurd heq hne
    | cons _ _ => simp at hlen
  | cons b rest ih =>
    cases s' with
    | nil => simp at hlen
    | cons b' rest' =>
      simp only [pClimb] at heq
      by_cases hC : C π (children index a b).1 (children index a b).2 =
          C π (children index a' b').1 (children index a' b').2
      · refine ⟨_, List.mem_cons_self .., _, List.mem_cons_self .., ?_, zeroCap_cin _ _,
          zeroCap_cin _ _, hC⟩
        intro hx
        obtain ⟨h1, h2⟩ := cin_injective hx
        unfold children at h1 h2
        split at h1 <;> simp_all
      · obtain ⟨x, hx, x', hx', h⟩ :=
          ih (index >>> 1) _ _ rest' (by simpa using hlen) hC heq
        exact ⟨x, List.mem_cons_of_mem _ hx, x', List.mem_cons_of_mem _ hx', h⟩

/-! ### Encoding -/

/-- Little-endian digits: reading back the base-256 digits of `x` gives `x mod 256 ^ m`. -/
private theorem foldr_bytes (m x : Nat) :
    (List.ofFn fun k : Fin m => x / 256 ^ (k : Nat) % 256).foldr (fun b acc => 256 * acc + b) 0 =
      x % 256 ^ m := by
  induction m generalizing x with
  | zero => simp [Nat.mod_one]
  | succ m ih =>
    rw [List.ofFn_succ, List.foldr_cons]
    have : (fun k : Fin m => x / 256 ^ ((k.succ : Fin (m+1)) : Nat) % 256) =
        fun k : Fin m => (x / 256) / 256 ^ (k : Nat) % 256 := by
      funext k; simp [Fin.val_succ, pow_succ, Nat.div_div_eq_div_mul, mul_comm]
    rw [this, ih, pow_succ', Nat.mod_mul]
    simp only [Fin.val_zero, pow_zero, Nat.div_one]
    ring

theorem Digest.ofBytes_toBytes (d : Digest) : Digest.ofBytes (Digest.toBytes d) = d := by
  unfold Digest.ofBytes Digest.toBytes
  have h : (List.ofFn fun k : Fin DIGEST_BYTES => d.extractLsb' (8 * k) 8).foldr
      (fun (byte : Byte) acc => 256 * acc + byte.toNat) 0 =
      (List.ofFn fun k : Fin DIGEST_BYTES => d.toNat / 256 ^ (k : Nat) % 256).foldr
      (fun b acc => 256 * acc + b) 0 := by
    rw [← List.foldr_map (f := fun b : Byte => b.toNat) (g := fun b acc => 256 * acc + b),
      List.map_ofFn]
    congr 2
    funext k
    simp [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, pow_mul]
  rw [h, foldr_bytes]
  apply BitVec.eq_of_toNat_eq
  simp [DIGEST_BYTES, DIGEST_BITS]
  exact lt_of_lt_of_le d.isLt (by norm_num [DIGEST_BITS, DIGEST_BYTES])

theorem Digest.length_toBytes (d : Digest) : (Digest.toBytes d).length = DIGEST_BYTES := by
  simp [Digest.toBytes]

end CommitGolf.CompressionBaseline
