import CommitGolfCandidate.ReconstructedOpeningRowData

namespace CommitGolfCandidate.Reconstruction.OpeningRowOps
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel OpeningOps OpeningCursor OpeningPut OpeningRowData
open TwoPermutationPrototype.RV64

structure Input (start width : Nat) where
  root : Nat
  initial : Model
  word : Nat → Word
  room : (root+start+192)/64 < capacity
  fits : width≤64

def Input.data {s n : Nat} (x : Input s n) : Data := ⟨x.root,s,n,x.word,x.initial,x.room,x.fits⟩

theorem plusBit (x a b n : Nat) (imm : BitVec 12) (sum : a+b=n) (bits : signExtend12 imm=W b) :
    W (x+a)+signExtend12 imm=W (x+n) := by rw [bits,←BitVec.ofNat_add,Nat.add_assoc,sum]

theorem pointer (x : Data) (k : Nat) (ok : k<4) :
    ((W (atBit x k) >>> (3 : Nat)) &&& signExtend12 4088)+wordAddress base=OpeningRowData.addr x k :=
  word_address _ (bounded x k ok)

theorem bare (x : Data) (k : Nat) (ok : k<4) (z : off x=0) :
    (W (atBit x k) >>> (3 : Nat))+wordAddress base=OpeningRowData.addr x k :=
  CapWriter.byte_at_boundary _ (bounded x k ok) ((alignment x k).trans z)

theorem current (x : Data) (k : Nat) : OpeningRowData.addr x k+signExtend12 0=wordAddress (cell (atBit x k)) :=
  BitVec.add_zero _
theorem following (x : Data) (k : Nat) : OpeningRowData.addr x k+signExtend12 8=wordAddress (cell (atBit x k)+1) := by
  rw [wordAddress_add];rfl

theorem left (x : Data) (k : Nat) : x.word k <<< ((W (off x)).toNat%64)=x.word k <<< off x := by rw [off_value]
theorem rightNeg (x : Data) (k : Nat) (nz : off x≠0) :
    x.word k >>> ((((0 : BitVec 32)-(W (off x)).truncate 32).signExtend 64).toNat%64)=high x k := by
  rw [negative x nz];rfl
theorem rightSub (x : Data) (k : Nat) (nz : off x≠0) :
    x.word k >>> (((64 : Word)-W (off x)).toNat%64)=high x k := by rw [subtract x nz];rfl

end CommitGolfCandidate.Reconstruction.OpeningRowOps
