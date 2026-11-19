import CommitGolf.Riscv

namespace TwoPermutationPrototype.Packed.Checker.HeadRestore
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def headLoop : Nat := 18
def bodyStart : Nat := 36
def bodyLoop : Nat := 38
def bodyCopy : Nat := 44
def insertStart : Nat := 50
def insertLoop : Nat := 52
def cleanup : Nat := 63
def finish : Nat := 77

def code : List Instr := [
  .ADDI .x18 .x16 0,
  .ADDI .x0 .x0 0,
  .ADDI .x0 .x0 0,
  .ADD .x17 .x17 .x18,
  .ADDI .x19 .x0 498,
  .SLLI .x19 .x19 22,
  .ADDI .x19 .x19 1920,
  .SLLI .x19 .x19 2,
  .BLTU .x19 .x17 7424,
  .ADDI .x18 .x0 481,
  .MUL .x18 .x16 .x18,
  .BLTU .x17 .x18 7412,
  .SUB .x18 .x17 .x16,
  .ADDI .x19 .x0 1,
  .SLLI .x19 .x19 33,
  .ADD .x19 .x15 .x19,
  .ADD .x20 .x15 .x18,
  .ADDI .x22 .x0 0,
  .BEQ .x22 .x16 72,
  .ADDI .x24 .x0 480,
  .MUL .x24 .x22 .x24,
  .ADDI .x24 .x24 44,
  .ADD .x27 .x15 .x24,
  .LBU .x28 .x27 0,
  .SRLI .x28 .x28 6,
  .ADDI .x0 .x0 0,
  .ADDI .x0 .x0 0,
  .ADDI .x0 .x0 0,
  .ADDI .x0 .x0 0,
  .MUL .x0 .x0 .x0,
  .ADDI .x0 .x0 0,
  .ADDI .x0 .x0 0,
  .ADD .x27 .x19 .x22,
  .SB .x27 .x28 0,
  .ADDI .x22 .x22 1,
  .JAL .x0 2097084,
  .ADDI .x25 .x0 480,
  .ADDI .x22 .x18 0,
  .BEQ .x22 .x0 48,
  .ADDI .x22 .x22 4095,
  .ADDI .x23 .x22 435,
  .DIVU .x23 .x23 .x25,
  .BLTU .x23 .x16 8,
  .ADDI .x23 .x16 0,
  .ADD .x23 .x23 .x22,
  .ADD .x24 .x15 .x22,
  .LBU .x28 .x24 0,
  .ADD .x23 .x15 .x23,
  .SB .x23 .x28 0,
  .JAL .x0 2097108,
  .ADDI .x22 .x0 0,
  .ADDI .x21 .x15 45,
  .BEQ .x22 .x16 44,
  .ADD .x27 .x19 .x22,
  .LBU .x28 .x27 0,
  .SB .x21 .x28 0,
  .LBU .x29 .x21 4095,
  .ANDI .x29 .x29 63,
  .SB .x21 .x29 4095,
  .SB .x27 .x0 0,
  .ADDI .x21 .x21 481,
  .ADDI .x22 .x22 1,
  .JAL .x0 2097112,
  .ADDI .x18 .x0 0,
  .ADDI .x19 .x0 0,
  .ADDI .x20 .x0 0,
  .ADDI .x21 .x0 0,
  .ADDI .x22 .x0 0,
  .ADDI .x23 .x0 0,
  .ADDI .x24 .x0 0,
  .ADDI .x25 .x0 0,
  .ADDI .x26 .x0 0,
  .ADDI .x27 .x0 0,
  .ADDI .x28 .x0 0,
  .ADDI .x29 .x0 0,
  .ADDI .x30 .x0 0,
  .ADDI .x31 .x0 0,
  .JAL .x0 2096160
]

def words : List (BitVec 32) := [
  0x00080913, 0x00000013, 0x00000013, 0x012888b3, 0x1f200993, 0x01699993, 0x78098993, 0x00299993,
  0xd119e0e3, 0x1e100913, 0x03280933, 0xcf28eae3, 0x41088933, 0x00100993, 0x02199993, 0x013789b3,
  0x01278a33, 0x00000b13, 0x050b0463, 0x1e000c13, 0x038b0c33, 0x02cc0c13, 0x01878db3, 0x000dce03,
  0x006e5e13, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x02000033, 0x00000013, 0x00000013,
  0x01698db3, 0x01cd8023, 0x001b0b13, 0xfbdff06f, 0x1e000c93, 0x00090b13, 0x020b0863, 0xfffb0b13,
  0x1b3b0b93, 0x039bdbb3, 0x010be463, 0x00080b93, 0x016b8bb3, 0x01678c33, 0x000c4e03, 0x01778bb3,
  0x01cb8023, 0xfd5ff06f, 0x00000b13, 0x02d78a93, 0x030b0663, 0x01698db3, 0x000dce03, 0x01ca8023,
  0xffface83, 0x03fefe93, 0xffda8fa3, 0x000d8023, 0x1e1a8a93, 0x001b0b13, 0xfd9ff06f, 0x00000913,
  0x00000993, 0x00000a13, 0x00000a93, 0x00000b13, 0x00000b93, 0x00000c13, 0x00000c93, 0x00000d13,
  0x00000d93, 0x00000e13, 0x00000e93, 0x00000f13, 0x00000f93, 0xc21ff06f
]

@[simp] theorem code_length : code.length=78 := rfl
@[simp] theorem words_length : words.length=78 := rfl

set_option maxRecDepth 8192 in
theorem decoded_words : words.map (fun w => (decodeInstruction w).bind fun i => match i with
  | .base b => some b
  | _ => none)=code.map some := by decide

end TwoPermutationPrototype.Packed.Checker.HeadRestore
