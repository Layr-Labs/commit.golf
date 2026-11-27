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

theorem filled_parent (H : Compression) (h n p : Nat) (s : MachineState)
    (ht : h<LOG_LENGTH) (bound : n≤levelCount (h+1)) (inside : p<n) :
    readBuffer (fillLevel H h n s) (nodeAddress (h+1) p) 32=H (readBuffer s (rowAddress h p) 96) := by
  induction n with
  | zero=>omega
  | succ n ih=>
    by_cases last:p=n
    · subst n
      have top:=parent_below_salts (h+1) p (by omega)
      have sep:=row_disjoint h p p ht (by omega)
      have stable:=fill_preserves H h p s (rowAddress h p) 96 (by omega) (by unfold rowBase at top;omega)
        (fun j _=>Or.inl (row_disjoint h p j ht (by omega)))
      unfold fillLevel writeParent compressAt
      erw [store_read,stable]
    · exact (parent_separate _ H h n ht (by omega) p (by omega)).trans (ih (by omega) (by omega))

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
