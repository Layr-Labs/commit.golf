import Std

namespace CommitGolfCandidate.Reconstruction

/-- Numeric parameters transcribed from the selected handoff. Depth zero is the root. -/
structure Profile where
  widths : List Nat
  calls : List Nat
  bases : List Nat
  lows : List Nat
  moduli : List Nat
  recordBases : List Nat
  headerBits : Nat
  capLow : Nat
  capHeader : Nat
  capGroup : Nat
  proofAlignment : Nat
  proofBytes : Nat
  commitCycles : Nat
  openingCycles : Nat

def sameSize : Profile where
  widths := [256, 240, 240, 240, 240, 240, 240, 240, 232, 232, 232, 232, 232, 232, 232, 233, 233, 233, 234, 235, 236, 238, 238, 238, 240]
  calls := [0, 0, 0, 0, 0, 0, 0, 0, 8, 8, 9, 9, 9, 8, 8, 7, 6, 6, 4, 3, 2, 0, 0, 0, 0]
  bases := [1, 1, 1, 1, 1, 1, 1, 1, 211, 211, 1325, 1325, 1325, 1677, 1677, 137, 1491, 1491, 1677, 1491, 1, 1, 1, 1, 1]
  lows := [256, 240, 240, 240, 240, 240, 240, 240, 224, 224, 221, 221, 221, 221, 221, 225, 222, 222, 223, 224, 236, 238, 238, 238, 240]
  moduli := [0, 0, 0, 0, 0, 0, 0, 0, 906238099456, 906238099456, 711353958400, 711353958400, 711353958400, 900332519424, 900332519424, 1176821039104, 1600949059584, 1600949059584, 3601330077696, 6403796238336, 0, 0, 0, 0, 0]
  recordBases := [1491, 1677, 1491, 1491, 137, 1677, 1677, 1325, 1325, 1325]
  headerBits := 102
  capLow := 224
  capHeader := 31
  capGroup := 4
  proofAlignment := 8
  proofBytes := 65544
  commitCycles := 1489523308
  openingCycles := 210404

/-- Ten nontrivial lower-record digits, ordered from the leaf toward the cap. -/
theorem lower_radices : ((sameSize.bases.drop 10).reverse.filter (1 < ·)) =
    sameSize.recordBases := by decide

theorem header_capacity :
    2 ^ (sameSize.headerBits - 1) < sameSize.recordBases.prod ∧
    sameSize.recordBases.prod ≤ 2 ^ sameSize.headerBits := by decide

theorem cap_digit_capacity : 2 ^ 30 < 211 ^ sameSize.capGroup ∧
    211 ^ sameSize.capGroup ≤ 2 ^ sameSize.capHeader := by decide

def recordBits : Nat := 120 + sameSize.headerBits + (sameSize.lows.drop 10).sum

theorem lower_record : (sameSize.lows.drop 10).length = 15 ∧
    (sameSize.lows.drop 10).sum = 3411 ∧ recordBits = 3633 := by decide

/-- Per-position path accounting for the profile before sharing any upper paths.
An ordinary internal node costs one call, a paid one uses its positive schedule entry,
and a leaf takes two calls. -/
theorem path_query_sum : 2 + ((sameSize.calls.take 24).map (max 1)).sum = 100 := by decide

/-- Cost of visiting every internal node once with its scheduled query count. -/
def internalQueries (nodes : Nat) : List Nat → Nat
  | [] => 0
  | n :: ns => nodes * max 1 n + internalQueries (2 * nodes) ns

def treeQueries := 1400832 + 2 * 2 ^ 24 + internalQueries 1 (sameSize.calls.take 24)

theorem full_tree_budget :
    treeQueries = 56030463 ∧ treeQueries ≤ 100 * 2 ^ 24 := by decide

/-- Permutation calls: 342 salt-generator calls per 4,096-leaf tile and two per leaf. -/
def permutationQueries := 1400832 + 2 * 2 ^ 24

theorem query_split : treeQueries = permutationQueries + internalQueries 1 (sameSize.calls.take 24) ∧
    permutationQueries = 34955264 ∧ internalQueries 1 (sameSize.calls.take 24) = 21075199 := by decide

/-- Remaining cycle allowance after paying for the calls in this traversal model, at eight
cycles per compression call and thirty per permutation call. All other commitment costs,
including the seed syscall, must fit this allowance. -/
theorem remaining_commit_cycles :
    8 * internalQueries 1 (sameSize.calls.take 24) + 30 * permutationQueries + 272263796 =
      sameSize.commitCycles := by decide

theorem target_totals : sameSize.commitCycles + sameSize.openingCycles = 1489733712 := by decide

end CommitGolfCandidate.Reconstruction
