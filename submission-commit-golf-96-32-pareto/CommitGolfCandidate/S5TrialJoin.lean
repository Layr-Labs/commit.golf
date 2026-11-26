import CommitGolfCandidate.S5CapPairHead
namespace CommitGolfCandidate.S5Machine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W)
theorem join_tail_word (lo : Nat) (q : Fin 4) (a b : Word) (small : lo<2^36)
    (base : a=W (lo+2^36*(0 : Fin 4).val)) (full : b=W (lo+2^36*q.val)) :
    a ||| (W q.val <<< 36)=b := by
  have loFit : lo<2^64:=small.trans (by decide)
  have qFit : q.val<2^64:=q.isLt.trans (by decide)
  have low : (W lo).toNat=lo:=Nat.mod_eq_of_lt loFit
  have high : (W q.val).toNat=q.val:=Nat.mod_eq_of_lt qFit
  have aeq : a=W lo := by simpa only [Fin.val_zero,Nat.mul_zero,Nat.add_zero] using base
  rw [aeq,full,Writer.joined_word (W lo) (W q.val) 36 (by rw [low];exact small),low,high]
  rfl
end CommitGolfCandidate.S5Machine.Check
