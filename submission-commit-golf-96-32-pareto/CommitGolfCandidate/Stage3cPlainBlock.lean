import CommitGolfCandidate.ChainedEncoding
import CommitGolfCandidate.Stage3cParent
import CommitGolf.Riscv
namespace CommitGolfCandidate.Chained.BinaryMachine
open RiscvZkvm.Rv64

theorem append_value {n k : Nat} (a : BitVec n) (b : BitVec k) :
    (a ++ b).toNat=2^k*a.toNat+b.toNat := by
  rw [BitVec.toNat_append,←Nat.shiftLeft_add_eq_or_of_lt b.isLt,Nat.shiftLeft_eq,Nat.mul_comm]

/-- Ninety-six bytes at a binary parent: left child, right child, then a tag word and 24 zero bytes. -/
def parentBlock (l r : Output) (tag : Word) : Input := ((0:BitVec 192) ++ tag) ++ (r ++ l)

theorem parentBlock_plain (d : Height) (l r : Output) (plain : ¬(8≤d.val ∧ d.val<16)) :
    parentBlock l r 0=pack (.inl (workClass d,r ++ l)) := by
  apply BitVec.eq_of_toNat_eq
  rw [pack_value,symbolCode,workClass,if_neg plain]
  unfold parentBlock;rw [append_value,append_value];simp [firstTag]

end CommitGolfCandidate.Chained.BinaryMachine
