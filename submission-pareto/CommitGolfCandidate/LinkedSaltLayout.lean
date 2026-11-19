import CommitGolfCandidate.LinkedSaltSchedule
import CommitGolfCandidate.CounterSaltLayout

/-! The K6 schedule on the generator heads: 373 heads per tile, a keyed restart (the tree's
`CounterSalt.input`, private key with a public counter) at every rank `0 mod m`, every other head
reads the previous head's whole reply. Salts are the `CounterSalt.splitReply` slices of each reply. -/
namespace CommitGolfCandidate.Permutation.LinkedSalt
open CommitGolf
open NonceChain (Word1600 Key)
set_option exponentiation.threshold 2048
set_option maxRecDepth 8000

/-- The head before head `j` in commit order. -/
def pred (j : Fin CounterSalt.groups) : Fin CounterSalt.groups :=
  ⟨j.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) j.isLt⟩

/-- Head `j` (tile `j / 373`, rank `j % 373`) is keyed when its rank is `0 mod m`. -/
def headLink (m : Nat) (j : Fin CounterSalt.groups) : Option (Fin CounterSalt.groups) :=
  if (j.val % 373) % m = 0 then none else some (pred j)

private theorem pos_of_linked {m : Nat} {j : Fin CounterSalt.groups} (h : (j.val % 373) % m ≠ 0) :
    0 < j.val := by
  rcases Nat.eq_zero_or_pos j.val with z | p
  · rw [z] at h
    simp at h
  · exact p

private theorem headLink_some {m : Nat} {i j : Fin CounterSalt.groups} (h : headLink m i = some j) :
    (i.val % 373) % m ≠ 0 ∧ j = pred i := by
  unfold headLink at h
  by_cases hc : (i.val % 373) % m = 0
  · rw [if_pos hc] at h
    exact absurd h (by simp)
  · rw [if_neg hc] at h
    exact ⟨hc, (Option.some.inj h).symm⟩

def schedule (m : Nat) : Schedule CounterSalt.groups where
  link := headLink m
  link_lt := by
    intro i j h
    obtain ⟨hc, rfl⟩ := headLink_some h
    have p := pos_of_linked hc
    show i.val - 1 < i.val
    omega
  link_inj := by
    intro i i' j h h'
    obtain ⟨hc, rfl⟩ := headLink_some h
    obtain ⟨hc', e⟩ := headLink_some h'
    have p := pos_of_linked hc
    have p' := pos_of_linked hc'
    have v : i.val - 1 = i'.val - 1 := congrArg Fin.val e
    apply Fin.ext
    omega

/-- K6: a keyed restart every 34 heads. -/
abbrev period : Nat := 34

theorem reply_keyed (m : Nat) (π : Equiv.Perm Word1600) (k : Key) (j : Fin CounterSalt.groups)
    (h : (j.val % 373) % m = 0) :
    (schedule m).reply π CounterSalt.input k j = π (CounterSalt.input j k) := by
  have hl : (schedule m).link j = none := by
    show headLink m j = none
    unfold headLink
    rw [if_pos h]
  rw [Schedule.reply_eq (schedule m) π CounterSalt.input k j]
  unfold Schedule.input
  rw [hl]

theorem reply_linked (m : Nat) (π : Equiv.Perm Word1600) (k : Key) (j : Fin CounterSalt.groups)
    (h : (j.val % 373) % m ≠ 0) :
    (schedule m).reply π CounterSalt.input k j = π ((schedule m).reply π CounterSalt.input k (pred j)) := by
  have hl : (schedule m).link j = some (pred j) := by
    show headLink m j = some (pred j)
    unfold headLink
    rw [if_neg h]
  rw [Schedule.reply_eq (schedule m) π CounterSalt.input k j]
  unfold Schedule.input
  rw [hl]

/-- The salt array of any linked schedule over the generator heads. -/
noncomputable def salts (σ : Schedule CounterSalt.groups) (π : Equiv.Perm Word1600) (k : Key) :=
  CounterSalt.nonceAt fun j => (CounterSalt.splitReply (σ.reply π CounterSalt.input k j)).1

theorem budget (t : Nat) :
    let q := t + (2*LENGTH + (4194304 + t))
    ((t : ℝ)+1)/2^121 + 2*((CounterSalt.groups:ℝ)*((3*q+2*CounterSalt.groups:ℝ)/2^192)) ≤
      ((t:ℝ)+1)/2^120 := by
  norm_num [CounterSalt.groups,LENGTH,LOG_LENGTH,Nat.cast_add,Nat.cast_mul]
  nlinarith [Nat.cast_nonneg (α := ℝ) t]

end CommitGolfCandidate.Permutation.LinkedSalt
