import CommitGolfCandidate.LateParents

namespace CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def fillLevel (h : Compression) (height : Nat) : Nat → MachineState → MachineState
  | 0, s => s
  | n+1, s => writeParent h (fillLevel h height n s) height n

attribute [local irreducible] store readBuffer

theorem fill_preserves (h : Compression) (height n : Nat) (s : MachineState) (addr len : Nat)
    (bound : n ≤ levelCount (height+1)) (valid : addr+len ≤ 2^64)
    (sep : ∀ j < n, addr+len ≤ nodeAddress (height+1) j ∨ nodeAddress (height+1) j + 32 ≤ addr) :
    readBuffer (fillLevel h height n s) addr len = readBuffer s addr len := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have b := parent_below_salts (height+1) n (by omega)
    change _ ≤ 5905584160 at b
    unfold fillLevel writeParent compressAt
    exact (store_away _ _ _ _ _ (by omega) valid (sep n (by omega))).trans
      (ih (by omega) (fun j hj => sep j (by omega)))

theorem filled_parent (h : Compression) (height n p : Nat) (s : MachineState)
    (ht : height < LOG_LENGTH) (bound : n ≤ levelCount (height+1)) (inside : p < n)
    (gap : readBuffer s (nodeAddress height (2*p)+64) 32 = 0) :
    readBuffer (fillLevel h height n s) (nodeAddress (height+1) p) 32 =
      h (parentBlock (readBuffer s (nodeAddress height (2*p)) 32)
                     (readBuffer s (nodeAddress height (2*p+1)) 32)) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases last : p=n
    · subst n
      let base := nodeAddress height (2*p)
      have small (d : Nat) (hd : d+32 ≤ 96) :
          readBuffer (fillLevel h height p s) (base+d) 32 = readBuffer s (base+d) 32 := by
        have row := parent_row_disjoint height p p ht (by omega)
        have hi := parent_below_salts (height+1) p (by omega)
        change _ ≤ 5905584160 at hi
        apply fill_preserves _ _ _ _ _ _ (by omega)
        · dsimp [base]; omega
        · intro j hj
          have bj := parent_row_disjoint height p j ht (by omega)
          left; dsimp [base]; omega
      have left := small 0 (by decide)
      have right := small 32 (by decide)
      have zero := small 64 (by decide)
      rw [Nat.add_zero] at left
      have eq : base+32 = nodeAddress height (2*p+1) := (children_contiguous height p).1.symm
      rw [eq] at right
      exact parent_output _ _ _ _ _ _ left right (zero.trans gap)
    · exact (parent_separate _ h height n ht (by omega) p (by omega)).trans (ih (by omega) (by omega))

theorem all_salts_survive (h : Compression) (height n : Nat) (s : MachineState) (i : Index)
    (bound : n ≤ levelCount (height+1)) :
    readBuffer (fillLevel h height n s) (saltAddress i) 24 = readBuffer s (saltAddress i) 24 := by
  have hi := i.isLt; change i.val < 16777216 at hi
  apply fill_preserves _ _ _ _ _ _ bound
  · unfold saltAddress rowBase; split <;> omega
  · intro j hj
    have e := parent_below_salts (height+1) j (by omega)
    right; unfold saltAddress; omega

end CommitGolfCandidate.Late
