import CommitGolfCandidate.S5TrialJoin
import CommitGolfCandidate.S5TrialPatchSplit

namespace CommitGolfCandidate.S5Machine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W)
open Reader (window)
attribute [local irreducible] S5.atProof S5.packedInput readBuffer S5.complete Reader.window slotValue

private theorem low_bound (v n w : Nat) : window v n w<2^w:=by
  unfold window;exact Nat.mod_lt (v/2^n) (Nat.two_pow_pos w)

theorem last_slot_patch_word (x : CheckInput) (new : Fin 4) :
    (slotValue x 0 170).extractLsb' 192 64 ||| (W new.val <<< 36) =
      (slotValue x new 170).extractLsb' 192 64 := by
  exact join_tail_word (window (S5.packedInput x) 555132 36) new _ _
    (low_bound _ _ _) (last_slot_split x 0) (last_slot_split x new)
end CommitGolfCandidate.S5Machine.Check
