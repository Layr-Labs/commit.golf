import CommitGolfCandidate.S5MemoryStep

namespace CommitGolfCandidate.S5Machine
open CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
attribute [local irreducible] nextPair writeBits

theorem apply_preserves_salt (ws : List PairCoins) (p : Nat) (s : MachineState)
    (a : AtPair s p) (enough : p+ws.length ≤ pairCount) (i : Nat) (past : i/2 < p) :
    readBuffer (applyPairs p s ws) (saltAddress i) 24 = readBuffer s (saltAddress i) 24 := by
  induction ws generalizing p s with
  | nil => rfl
  | cons w ws ih =>
    have bound : p < pairCount := by simp only [List.length_cons] at enough; omega
    rw [applyPairs, ih (p+1) _ (next_pair_invariant a bound w)
      (by simp only [List.length_cons] at enough; omega) (by omega), read_next _ _ _ _ _ a]
    exact later_pair_preserves_salt s w i p past bound

theorem apply_reads_salt (ws : List PairCoins) (p : Nat) (s : MachineState)
    (a : AtPair s p) (enough : p+ws.length ≤ pairCount) (i : Nat)
    (lo : p ≤ i/2) (hi : i/2 < p+ws.length) :
    readBuffer (applyPairs p s ws) (saltAddress i) 24 =
      pairSalts (ws[i/2-p]?.getD 0) (i.testBit 0) := by
  induction ws generalizing p s with
  | nil => simp at hi; omega
  | cons w ws ih =>
    simp only [List.length_cons] at enough hi
    have bound : p < pairCount := by omega
    have a' := next_pair_invariant a bound w
    by_cases e : i/2 = p
    · rw [applyPairs, apply_preserves_salt _ _ _ a' (by omega) _ (by omega), read_next _ _ _ _ _ a]
      rw [← e]
      simpa using read_pair_salt s w i
    · rw [applyPairs, ih (p+1) _ a' (by omega) (by omega) (by omega)]
      rw [show i/2-p = (i/2-(p+1))+1 by omega, List.getElem?_cons_succ]

theorem apply_preserves_buffer (ws : List PairCoins) (p : Nat) (s : MachineState)
    (a : AtPair s p) (enough : p+ws.length ≤ pairCount) (addr count : Nat)
    (inRange : addr+count ≤ 2^64)
    (sep : ∀ j, p ≤ j → j < p+ws.length →
      addr+count ≤ pairAddress j ∨ pairAddress j+48 ≤ addr) :
    readBuffer (applyPairs p s ws) addr count = readBuffer s addr count := by
  induction ws generalizing p s with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.length_cons] at enough sep
    have bound : p < pairCount := by omega
    have next := ih (p+1) _ (next_pair_invariant a bound w) (by omega)
      (fun j a b => sep j (by omega) (by omega))
    rw [applyPairs, next, read_next _ _ _ _ _ a]
    exact write_bits_read_outside s w (pairAddress p) addr count
      (by have h := (pair_address_valid p bound).2
          change pairAddress p + 48 ≤ 2^36 at h
          change pairAddress p + 48 ≤ 2^64; omega) inRange (sep p le_rfl (by omega))

end CommitGolfCandidate.S5Machine
