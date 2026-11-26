import CommitGolfCandidate.S5CursorFrame
namespace CommitGolfCandidate.S5Machine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
def peerBit (r h : Nat) :=4030*r+S5.layerBits h
def peerOffset (r h : Nat) :=824*r+24+32*(if h=0 then 0 else h+1)
def view (batch : Bool) (x : CheckInput) := if batch then S5.batchView x 0 else S5.plainView x

private theorem zero_high (v bits : Nat) (low : v<2^bits) : v%2^bits+2^bits*(0:Nat)=v := by rw [Nat.mul_zero,Nat.add_zero,Nat.mod_eq_of_lt low]
private theorem input_bound (x : CheckInput) : S5.packedInput x<2^S5.wireBits:=BitVec.isLt (S5.atProof x 0 69396)
attribute [local irreducible] S5.packedInput readBuffer
theorem packed_zero (x : CheckInput) : S5.complete (S5.packedInput x) 0=S5.packedInput x:=
  zero_high _ _ (input_bound x)
end CommitGolfCandidate.S5Machine.Check
