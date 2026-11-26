import CommitGolf.Riscv

namespace TwoPermutationPrototype.PackedOpening.StreamCopy
open CommitGolf RiscvZkvm.Rv64

def width (head : Bool) := if head then 480 else 479
def origin (head : Bool) := if head then 1316 else 2315
def guardWord (head : Bool) := if head then 156 else 264
def copyOff (w j : Nat) := j + (if w-435≤j then 1 else 0)

def pairs (count : Nat) (src : Nat → Nat) : List Instr :=
  (List.range count).flatMap fun j => [.LBU .x23 .x30 (BitVec.ofNat 12 (src j)),
    .SB .x24 .x23 (BitVec.ofNat 12 j)]

def code (head : Bool) : List Instr :=
  let w:=width head
  [.ADDI .x30 .x20 0,.ADDI .x24 .x20 0,.ADDI .x25 .x16 0,
    .BEQ .x25 .x0 (BitVec.ofNat 13 (4*(2*w+5)))] ++
  pairs w (copyOff w) ++
  [.ADDI .x30 .x30 (BitVec.ofNat 12 (w+1)),.ADDI .x24 .x24 (BitVec.ofNat 12 w),
    .ADDI .x25 .x25 4095,.BNE .x25 .x0 (BitVec.ofNat 13 (8192-4*(2*w+3))),
    .SUB .x28 .x26 .x24,.ANDI .x28 .x28 4088,.ADD .x28 .x24 .x28,.BEQ .x24 .x28 80] ++
  pairs 8 id ++ [.ADDI .x30 .x30 8,.ADDI .x24 .x24 8,.BNE .x24 .x28 8120,.BEQ .x24 .x26 24] ++
  pairs 1 id ++ [.ADDI .x30 .x30 1,.ADDI .x24 .x24 1,.BNE .x24 .x26 8176,
    .ADDI .x22 .x18 0,.JAL .x0 (BitVec.ofNat 21 (2097152-4*(origin head+2*w+38-guardWord head)))]

def price (w k L : Nat) :=
  let E:=L-(w+1)*k
  if L=k then 0 else 13+(2*w+4)*k+19*(E/8)+5*(E%8)

end TwoPermutationPrototype.PackedOpening.StreamCopy
