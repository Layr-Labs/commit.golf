import CommitGolfCandidate.LinkedSaltLayout
import RiscvZkvm.Rv64.Instructions

/-!
# K6: the chain programs' arithmetic against `LinkedSalt.schedule LinkedSalt.period`

The commit and opener images of the register-chained generator (S9-K6P, `k3-work/k3-k6p/tools/k6img.py`) compute
the group replies of the linked schedule. This file holds the program-independent facts their execution proofs use.
- Leaf `i` lies in head `head i = (i % 4096) / 11` of tile `i / 4096`; its group is `(coord i).1 = 373 (i / 4096) + head i`.
- Commit: head `h` is keyed iff `h % 34 = 0` (`commit_keyed`, input `CounterSalt.input`); otherwise the generator reads,
  in place, the whole reply of the previous head, which is the group of leaf `i - 11` (`commit_linked`).
- Opener: the reply of a group is the keyed reply of its restart head `h - h % 34`, followed by `h % 34` links
  (`opener_chain`); the restart head's counter is the one the opener rows compute (`restart_counter`).
- Salts: the K1 parts of the group reply (`chain_salt`); `Counter.slice_eq` turns them into reply words.
-/

namespace TwoPermutationPrototype.K6Chain
open CommitGolf
open CommitGolfCandidate.Permutation
open CommitGolfCandidate.Permutation.CounterSalt (groups coord input ctr firstLeaf)
open CommitGolfCandidate.Permutation.NonceChain (Word1600 Key)
set_option maxRecDepth 22000

/-- The generator reply of group `j` under the K6 schedule (keyed restart every 34 heads). -/
noncomputable def chainReply (π : Equiv.Perm Word1600) (k : Key) (j : Fin groups) : Word1600 :=
  (LinkedSalt.schedule LinkedSalt.period).reply π CounterSalt.input k j

/-- `chainReply` is the linked schedule's reply, by definition. -/
theorem chainReply_eq (π : Equiv.Perm Word1600) (k : Key) (j : Fin groups) :
    chainReply π k j = (LinkedSalt.schedule LinkedSalt.period).reply π CounterSalt.input k j := rfl

/-- Head of leaf `i` within its tile. -/
def head (i : Nat) : Nat := (i % 4096) / 11

/-- Links after the restart: the opener's `j`. -/
def links (i : Nat) : Nat := head i % 34

theorem head_lt (i : Nat) : head i < 373 := by unfold head; omega

theorem links_le (i : Nat) : links i ≤ 33 := by unfold links; omega

theorem group_val (i : Index) : (coord i).1.val = 373 * (i.val / 4096) + head i.val := rfl

theorem group_mod (i : Index) : (coord i).1.val % 373 = head i.val := by
  rw [group_val]; have := head_lt i.val; omega

theorem keyed_iff (i : Index) : ((coord i).1.val % 373) % LinkedSalt.period = 0 ↔ head i.val % 34 = 0 := by
  rw [group_mod]

/-- A keyed head (`head % 34 = 0`, including the first head of every tile) answers its counter input. -/
theorem commit_keyed (π : Equiv.Perm Word1600) (k : Key) (i : Index) (keyed : head i.val % 34 = 0) :
    chainReply π k (coord i).1 = π (input (coord i).1 k) :=
  LinkedSalt.reply_keyed LinkedSalt.period π k _ ((keyed_iff i).mpr keyed)

/-- The previous head of a linked head is the group of the leaf 11 places back (same tile). -/
theorem pred_group (i : Index) (r0 : (i.val % 4096) % 11 = 0) (linked : head i.val % 34 ≠ 0) :
    LinkedSalt.pred (coord i).1 = (coord ⟨i.val - 11, by have := i.isLt; omega⟩).1 := by
  apply Fin.ext
  show (coord i).1.val - 1 = (coord ⟨i.val - 11, _⟩).1.val
  rw [group_val, group_val]
  unfold head at linked ⊢
  have hi := i.isLt
  have pos : 11 ≤ i.val % 4096 := by omega
  dsimp only
  omega

/-- A linked head's generator input is the previous head's whole reply. -/
theorem commit_linked (π : Equiv.Perm Word1600) (k : Key) (i : Index) (r0 : (i.val % 4096) % 11 = 0)
    (linked : head i.val % 34 ≠ 0) :
    chainReply π k (coord i).1 = π (chainReply π k (coord ⟨i.val - 11, by have := i.isLt; omega⟩).1) := by
  unfold chainReply
  rw [LinkedSalt.reply_linked LinkedSalt.period π k _ (by rw [group_mod]; exact linked), pred_group i r0 linked]

/-- The restart head of group `j`. -/
def restart (j : Fin groups) : Fin groups := ⟨j.val - (j.val % 373) % 34, by have := j.isLt; omega⟩

/-- Rank (mod 373) of the `s`-th head after the restart, mod 34, is `s` (as long as `s` stays within the links). -/
private theorem restart_mod (x s : Nat) (hs : s ≤ x % 373 % 34) : ((x - x % 373 % 34 + s) % 373) % 34 = s := by
  have h1 := Nat.div_add_mod x 373
  have h2 := Nat.div_add_mod (x % 373) 34
  have hlt := Nat.mod_lt x (show 0 < 373 by decide)
  have hb := Nat.mod_lt (x % 373) (show 0 < 34 by decide)
  have e : x - x % 373 % 34 + s = (s + 34 * (x % 373 / 34)) + 373 * (x / 373) := by omega
  rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (show s + 34 * (x % 373 / 34) < 373 by omega),
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (show s < 34 by omega)]

private theorem chain_from_restart (π : Equiv.Perm Word1600) (k : Key) (j : Fin groups) :
    ∀ t, t ≤ (j.val % 373) % 34 → ∀ g : Fin groups, g.val = (restart j).val + t →
      chainReply π k g = (⇑π)^[t] (π (input (restart j) k)) := by
  have hr : (restart j).val = j.val - (j.val % 373) % 34 := rfl
  intro t
  induction t with
  | zero =>
    intro _ g hg
    have e : g = restart j := Fin.ext (by simpa using hg)
    subst e
    have m := restart_mod j.val 0 (Nat.zero_le _)
    rw [Nat.add_zero] at m
    exact LinkedSalt.reply_keyed LinkedSalt.period π k _
      (by show ((restart j).val % 373) % 34 = 0; rw [hr]; exact m)
  | succ t ih =>
    intro ht g hg
    have m := restart_mod j.val (t + 1) ht
    unfold chainReply
    rw [LinkedSalt.reply_linked LinkedSalt.period π k g
      (by show (g.val % 373) % 34 ≠ 0; rw [hg, hr, m]; omega), Function.iterate_succ_apply']
    congr 1
    exact ih (by omega) (LinkedSalt.pred g) (by show g.val - 1 = _; rw [hg]; omega)

/-- The opener's regeneration: keyed call for the restart head, then `(j % 373) % 34` links in place. -/
theorem opener_chain (π : Equiv.Perm Word1600) (k : Key) (j : Fin groups) :
    chainReply π k j = (⇑π)^[(j.val % 373) % 34] (π (input (restart j) k)) :=
  chain_from_restart π k j _ le_rfl j (by show j.val = j.val - (j.val % 373) % 34 + (j.val % 373) % 34; omega)

theorem restart_links (i : Index) : ((coord i).1.val % 373) % 34 = links i.val := by
  rw [group_mod]; rfl

private theorem tile_split (T u : Nat) (hu : u < 373) : (373 * T + u) / 373 = T ∧ (373 * T + u) % 373 = u := by
  rw [show 373 * T + u = u + 373 * T by omega, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hu,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hu]
  exact ⟨Nat.zero_add T, rfl⟩

theorem restart_val (i : Index) : (restart (coord i).1).val = 373 * (i.val / 4096) + (head i.val - links i.val) := by
  show (coord i).1.val - ((coord i).1.val % 373) % 34 = _
  rw [group_mod, group_val]
  have : links i.val ≤ head i.val := Nat.mod_le _ _
  unfold links at this ⊢
  omega

/-- First leaf of the restart head of leaf `i`'s group: `i - rank - 11 j`. -/
theorem restart_first_leaf (i : Index) :
    firstLeaf (restart (coord i).1) = i.val - (i.val % 4096) % 11 - 11 * links i.val := by
  unfold firstLeaf
  rw [restart_val]
  have hl : links i.val ≤ head i.val := Nat.mod_le _ _
  obtain ⟨d, m⟩ := tile_split (i.val / 4096) (head i.val - links i.val) (by have := head_lt i.val; omega)
  rw [d, m]
  have a1 : 11 * head i.val + (i.val % 4096) % 11 = i.val % 4096 := Nat.div_add_mod _ _
  have a2 : 4096 * (i.val / 4096) + i.val % 4096 = i.val := Nat.div_add_mod _ _
  omega

/-- The counter of the restart head, as the opener rows build it:
`x7 = ((((i - r) - j * 11) + 1) << 8) + 4096` with `r = (i % 4096) % 11` and `j = links i`. -/
theorem restart_counter (i : Index) :
    ((((BitVec.ofNat 64 i.val - BitVec.ofNat 64 ((i.val % 4096) % 11)) - BitVec.ofNat 64 (links i.val) * 11#64)
      + 1#64) <<< (8 : Nat)) + 4096#64 = ctr (restart (coord i).1) := by
  have hi : i.val < 16777216 := i.isLt
  have lj := links_le i.val
  have le1 : (i.val % 4096) % 11 ≤ i.val := by omega
  have le2 : 11 * links i.val ≤ i.val - (i.val % 4096) % 11 := by
    have a0 : links i.val ≤ head i.val := Nat.mod_le _ _
    have a1 : 11 * head i.val + (i.val % 4096) % 11 = i.val % 4096 := Nat.div_add_mod _ _
    have a2 : i.val % 4096 ≤ i.val := Nat.mod_le _ _
    omega
  rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) le1, ← BitVec.ofNat_mul, Nat.mul_comm,
    BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) le2, ← BitVec.ofNat_add, BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 _ * BitVec.ofNat 64 256 + BitVec.ofNat 64 4096 = _
  rw [← BitVec.ofNat_mul, ← BitVec.ofNat_add]
  unfold ctr
  rw [restart_first_leaf]
  congr 1
  omega

/-- The salt of leaf `i` is the K1 part of its group's chain reply (`Counter.slice_eq` gives the reply words). -/
theorem chain_salt (π : Equiv.Perm Word1600) (k : Key) (i : Index) :
    LinkedSalt.salts (LinkedSalt.schedule LinkedSalt.period) π k i =
      (CounterSalt.parts (chainReply π k (coord i).1)).1 (coord i).2 := rfl

/-! ### The opener rows' M-extension steps (`divu x30,x28,x29`, `remu x30,x30,x31`) -/

open RiscvZkvm.Rv64 in
/-- `divu x30,x28,x29` with `x28 = i % 4096`, `x29 = 11` gives the head. -/
theorem divu_head (i : Index) : rv64_divu (BitVec.ofNat 64 (i.val % 4096)) 11#64 = BitVec.ofNat 64 (head i.val) := by
  unfold rv64_divu head
  change BitVec.ofNat 64 (i.val % 4096) / 11#64 = _
  apply BitVec.eq_of_toNat_eq
  have h : i.val % 4096 < 4096 := Nat.mod_lt _ (by decide)
  have a : i.val % 4096 < 18446744073709551616 := Nat.lt_of_lt_of_le h (by decide)
  have b : i.val % 4096 / 11 < 18446744073709551616 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) a
  simp only [BitVec.toNat_udiv, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show i.val % 4096 < 2 ^ 64 from a), Nat.mod_eq_of_lt (show i.val % 4096 / 11 < 2 ^ 64 from b)]

open RiscvZkvm.Rv64 in
/-- `remu x30,x30,x31` with `x30 = head`, `x31 = 34` gives the link count. -/
theorem remu_links (i : Index) : rv64_remu (BitVec.ofNat 64 (head i.val)) 34#64 = BitVec.ofNat 64 (links i.val) := by
  unfold rv64_remu links
  change BitVec.ofNat 64 (head i.val) % 34#64 = _
  apply BitVec.eq_of_toNat_eq
  have h := head_lt i.val
  have a : head i.val < 18446744073709551616 := Nat.lt_of_lt_of_le h (by decide)
  have b : head i.val % 34 < 18446744073709551616 := Nat.lt_of_le_of_lt (Nat.mod_le _ _) a
  simp only [BitVec.toNat_umod, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show head i.val < 2 ^ 64 from a), Nat.mod_eq_of_lt (show head i.val % 34 < 2 ^ 64 from b)]

end TwoPermutationPrototype.K6Chain
