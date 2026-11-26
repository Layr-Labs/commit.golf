import CommitGolfCandidate.ReconstructedCommitParentsSpec
import Mathlib.Tactic

namespace CommitGolfCandidate.Reconstruction.CommitParents
open Binding

def Cell (d k : Nat) := d ≤ 24 ∧ 2^d ≤ k ∧ k < 2^(d+1)
def Guard (d : Nat) := addr d (2^(d+1))

private theorem powers {a b : Nat} (h : a < b) : 2^(a+1) ≤ 2^b :=
  Nat.pow_le_pow_right (by decide) h

theorem slot_unique {d k e j : Nat} (a : 2^d ≤ k ∧ k ≤ 2^(d+1)) (b : 2^e ≤ j ∧ j ≤ 2^(e+1))
    (eq : addr d k = addr e j) : d = e ∧ k = j := by
  unfold addr at eq
  by_cases de : d < e
  · have p := powers de; omega
  · by_cases ed : e < d
    · have p := powers ed; omega
    · omega

/-- Logical contents at the start of parent k of level d. The label on a
residue child appears when that child's binary parent consumes it. -/
def stage (tree : Nat → Nat → Digest) (d k e j : Nat) : Digest :=
  if d+1 < e then consumed e j (tree e j)
  else if e = d+1 then if j < 2*k then consumed e j (tree e j) else written e (tree e j)
  else if e = d ∧ j < k then written e (tree e j)
  else zeroDigest

def Snapshot (mem : Nat → Digest) (tree : Nat → Nat → Digest) (d k : Nat) :=
  (∀ e j, Cell e j → mem (addr e j) = stage tree d k e j) ∧
  ∀ e, e < 24 → mem (Guard e) = zeroDigest

theorem entry_snapshot {mem tree}
    (leaves : ∀ j, 2^24 ≤ j → j < 2^25 → mem (addr 24 j) = written 24 (tree 24 j))
    (fresh : ∀ e j, e < 24 → 2^e ≤ j → j < 2^(e+1) → mem (addr e j) = zeroDigest)
    (guards : ∀ e, e < 24 → mem (Guard e) = zeroDigest) :
    Snapshot mem tree 23 (2^23) := by
  refine ⟨?_,guards⟩
  rintro e j ⟨ev,lo,hi⟩
  by_cases h : e = 24
  · subst e
    simpa only [stage,show ¬23+1<24 by decide,ite_false,show 24=23+1 by decide,ite_true,
      show ¬ j < 2*2^23 by omega] using leaves j lo hi
  · have top : e < 24 := by omega
    have no : ¬ (e = 23 ∧ j < 2^23) := by rintro ⟨rfl,small⟩;omega
    simpa only [stage,show ¬23+1<e by omega,show e≠23+1 by omega,no,ite_false] using fresh _ _ top lo hi

theorem ready_pair {mem tree d k} (snap : Snapshot mem tree d k)
    (depth : d < 24) (lo : 2^d ≤ k) (hi : k < 2^(d+1)) :
    mem (addr (d+1) (2*k)) = written (d+1) (tree (d+1) (2*k)) ∧
    mem (addr (d+1) (2*k+1)) = written (d+1) (tree (d+1) (2*k+1)) ∧
    mem (addr d (k+1)) = zeroDigest := by
  have pow₁ := Nat.pow_succ 2 d
  have pow₂ := Nat.pow_succ 2 (d+1)
  have left := snap.1 (d+1) (2*k) ⟨by omega,by omega,by omega⟩
  have right := snap.1 (d+1) (2*k+1) ⟨by omega,by omega,by omega⟩
  refine ⟨by simpa [stage] using left, by simpa [stage,show ¬ 2*k+1<2*k by omega] using right,?_⟩
  by_cases last : k+1 = 2^(d+1)
  · exact last ▸ snap.2 d depth
  · simpa [stage,show ¬ d+1<d by omega,show ¬ k+1<k by omega] using snap.1 d (k+1) ⟨by omega,by omega,by omega⟩

/-- The trapdoor changes in precisely two cell locations during one parent.
The right input tag is an idempotent write for all ordinary source levels. -/
def update (mem : Nat → Digest) (tree : Nat → Nat → Digest) (d k x : Nat) :=
  if x = addr d k then written d (tree d k)
  else if x = addr (d+1) (2*k+1) then consumed (d+1) (2*k+1) (tree (d+1) (2*k+1))
  else mem x

theorem advance {mem tree d k} (snap : Snapshot mem tree d k)
    (depth : d < 24) (lo : 2^d ≤ k) (hi : k < 2^(d+1)) :
    Snapshot (update mem tree d k) tree d (k+1) := by
  have p := Nat.pow_succ 2 d
  have p' := Nat.pow_succ 2 (d+1)
  have here : 2^d ≤ k ∧ k ≤ 2^(d+1) := ⟨lo,hi.le⟩
  have source : 2^(d+1) ≤ 2*k+1 ∧ 2*k+1 ≤ 2^(d+1+1) := ⟨by omega,by omega⟩
  constructor
  · rintro e j ⟨inTree,lo',hi'⟩
    have ij := And.intro lo' hi'.le
    by_cases a : addr e j = addr d k
    · obtain ⟨rfl,rfl⟩ := slot_unique ij here a
      simp [update,stage]
    · by_cases b : addr e j = addr (d+1) (2*k+1)
      · obtain ⟨rfl,rfl⟩ := slot_unique ij source b
        simp [update,stage,a,show 2*k+1 < 2*(k+1) by omega]
      · rw [update,ite_eq_right a,ite_eq_right b,snap.1 _ _ ⟨inTree,lo',hi'⟩]
        by_cases de : e = d+1
        · subst e
          by_cases even : j = 2*k
          · subst j; simp [stage,written_left]
          · have different : j ≠ 2*k+1 := fun eq => b (eq ▸ rfl)
            have stable : j < 2*k ↔ j < 2*(k+1) := by omega
            simp [stage,stable]
        · have stable : e = d ∧ j < k ↔ e = d ∧ j < k+1 := by
            constructor
            · rintro ⟨rfl,z⟩; exact ⟨rfl,by omega⟩
            · rintro ⟨rfl,z⟩
              have diff : j ≠ k := fun h => a (congrArg (addr e) h)
              exact ⟨rfl,by omega⟩
          simp [stage,de,stable]
  · intro e he
    have g : 2^e ≤ 2^(e+1) ∧ 2^(e+1) ≤ 2^(e+1) := ⟨Nat.pow_le_pow_right (by decide) (by omega),le_rfl⟩
    have a : Guard e ≠ addr d k := by
      intro eq; have := slot_unique g here eq; obtain ⟨rfl,z⟩ := this; omega
    have b : Guard e ≠ addr (d+1) (2*k+1) := by
      intro eq; have := slot_unique g source eq; obtain ⟨rfl,z⟩ := this; omega
    simp [update,a,b,snap.2 e he]

theorem next_level {mem tree d} (snap : Snapshot mem tree (d+1) (2^(d+2))) :
    Snapshot mem tree d (2^d) := by
  refine ⟨?_,snap.2⟩
  rintro e j h
  rw [snap.1 e j h]
  obtain ⟨_,lo,hi⟩ := h
  have pow' := Nat.pow_succ 2 d
  have pow'' := Nat.pow_succ 2 (d+2)
  by_cases deep : d+2 < e
  · simp [stage,deep,show d+1<e by omega]
  by_cases child : e=d+2
  · subst e
    have fix : j < 2*2^(d+2) := by omega
    simp [stage,fix]
  by_cases current : e=d+1
  · subst e
    have large : ¬j < 2*2^d := by omega
    simp [stage,hi,large]
  by_cases current : e=d
  · subst e
    simp [stage,deep,child,show ¬j<2^d by omega]
  · simp [stage,deep,child,current,show e≠d+1 by omega,show ¬d+1<e by omega]

end CommitGolfCandidate.Reconstruction.CommitParents
