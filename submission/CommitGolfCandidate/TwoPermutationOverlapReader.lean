import CommitGolfCandidate.TwoPermutationCheckerLeafCode
namespace TwoPermutationPrototype.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open TwoPermutationPrototype.RV64
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

theorem offset_word (start words bytes : Nat) (off : bytes = 8*words) :
    wordAddress start + BitVec.ofNat 64 bytes = wordAddress (start+words) := by
  rw [off,wordAddress_add]
  rfl

def headerCell (mem : Memory) (sc no : Nat) (tag : Word) (j : Nat) : Word :=
  if j=0 then tag else if j<5 then mem (sc+20+j) else mem (no+(j-5))

/-- An aligned read of the seven-word wrapper header. The reply and nonce sources
are disjoint from the target, so all loads see their original words. -/
theorem copy_header_view (state : MachineState) (d sc no : Nat) (tag : Word)
    (left : sc+25 ≤ d) (right : d+33 ≤ no) (limit : no+2 ≤ 2^33)
    (n : Nat) (small : n ≤ 6) (q : Nat) (hq : q < 2^33) :
    memoryView (copyHeader state (wordAddress d) (wordAddress sc) (wordAddress no) tag n) q =
      if d+8 ≤ q ∧ q < d+9+n then
        headerCell (memoryView state) sc no tag (q-(d+8)) else memoryView state q := by
  induction n generalizing q with
  | zero =>
    rw [copyHeader, offset_word d 8 64 rfl, memory_at_store (by omega) (by omega)]
    unfold writeWord
    by_cases same : q=d+8
    · subst q
      simp [headerCell]
    · rw [if_neg same, if_neg (by omega)]
  | succ n ih =>
    let atWord := if n < 4 then sc+21+n else no+(n-4)
    have address : (if n<4 then wordAddress sc+BitVec.ofNat 64 (168+8*n)
        else wordAddress no+BitVec.ofNat 64 (8*(n-4))) = wordAddress atWord := by
      by_cases h : n<4
      · simp only [h,ite_true,atWord]
        exact offset_word sc (21+n) _ (by omega) |>.trans (by rw [Nat.add_assoc])
      · simp only [h,ite_false,atWord]
        exact offset_word no _ _ rfl
    have dest : wordAddress d+BitVec.ofNat 64 (72+8*n) = wordAddress (d+9+n) := by
      rw [Nat.add_assoc,offset_word d (9+n) _ (by omega)]
    have off : ¬(d+8 ≤ atWord ∧ atWord < d+9+n) := by dsimp [atWord]; split <;> omega
    have below : atWord < 2^33 := by dsimp [atWord]; split <;> omega
    rw [copyHeader, address, dest, memory_at_store (by omega) (by omega)]
    unfold writeWord
    change (if q = d+9+n then memoryView _ atWord else memoryView _ q) = _
    by_cases same : q=d+9+n
    · subst q
      rw [if_pos rfl, ih (by omega) atWord below, if_neg off, if_pos (by omega)]
      have idx : d+9+n-(d+8) = n+1 := by omega
      rw [idx]
      by_cases four : n<4
      · change memoryView state atWord = headerCell (memoryView state) sc no tag (n+1)
        simp only [atWord,if_pos four,headerCell,if_neg (Nat.succ_ne_zero n),
          if_pos (by omega : n+1<5)]
        exact congrArg (memoryView state) (by omega)
      · change memoryView state atWord = headerCell (memoryView state) sc no tag (n+1)
        simp only [atWord,if_neg four,headerCell,if_neg (Nat.succ_ne_zero n),
          if_neg (by omega : ¬ n+1<5)]
        exact congrArg (memoryView state) (by omega)
    · rw [if_neg same, ih (by omega) q hq]
      by_cases h : d+8 ≤ q ∧ q < d+9+n
      · rw [if_pos h,if_pos (by omega)]
      · rw [if_neg h,if_neg (by omega)]

end TwoPermutationPrototype.Checker
