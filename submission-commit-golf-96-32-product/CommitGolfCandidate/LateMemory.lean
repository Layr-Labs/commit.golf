import CommitGolfCandidate.LateModel
import CommitGolfCandidate.InputMemory
import CommitGolfCandidate.WriteMemoryCore

namespace CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def rowBase := 5905584160
def pairAddress (j : Nat) := rowBase + 192*j + 72
def saltAddress (i : Nat) := rowBase + 96*i + (if i%2 = 0 then 72 else 0)

theorem salt_address_pair (i : Nat) :
    saltAddress i = pairAddress (i/2) + (if i.testBit 0 then 24 else 0) := by
  simp only [saltAddress, pairAddress, Nat.testBit_eq_decide_div_mod_eq, Nat.pow_zero, Nat.div_one]
  split <;> split <;> simp_all <;> omega

theorem pair_address_valid (j : Nat) (hi : j < LENGTH/2) :
    pairAddress j % 8 = 0 ∧ pairAddress j + 48 ≤ MEMORY_BYTES := by
  change j < 8388608 at hi
  change (5905584160 + 192*j + 72) % 8 = 0 ∧ 5905584160 + 192*j + 72 + 48 ≤ 2^36
  omega

theorem disjoint_pairs {j k : Nat} (h : j < k) : pairAddress j + 48 ≤ pairAddress k := by
  unfold pairAddress
  omega

end CommitGolfCandidate.Late
