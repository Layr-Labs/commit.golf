import CommitGolfCandidate.Layout2Blocks
import CommitGolfCandidate.Layout2Memory
import CommitGolfCandidate.TwoPermutationOpeningBlocks

namespace CommitGolfCandidate.Layout2
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open TwoPermutationPrototype.Opening (getReg_setReg)
set_option maxRecDepth 6000
set_option maxHeartbeats 3000000

def regOut (s : MachineState) (r : Reg) : Block → Word
  | .entry => s.getReg r
  | .guard => if .x6=r then ((s.getReg .x16) * 534#64) else s.getReg r
  | .empty => s.getReg r
  | .init => if .x21=r then 8#64 else if .x20=r then 4#64 else if .x9=r then (s.getReg .x16) else if .x8=r then (s.getReg .x15) else s.getReg r
  | .choose => s.getReg r
  | .full => if .x31=r then (pc 718) else if .x19=r then (s.getReg .x2) else if .x18=r then (2047#64 + 89#64) else s.getReg r
  | .next => if .x9=r then ((s.getReg .x9) + (signExtend12 4092)) else if .x8=r then ((s.getReg .x8) + (s.getReg .x18)) else s.getReg r
  | .tail => s.getReg r
  | .one => if .x5=r then 1#64 else s.getReg r
  | .two => if .x5=r then 2#64 else s.getReg r
  | .three => if .x5=r then (61440#64 + (signExtend12 2464)) else if .x18=r then 1602#64 else s.getReg r
  | .pair => if .x5=r then (40960#64 + 1760#64) else if .x18=r then 1068#64 else s.getReg r
  | .single => if .x5=r then (32768#64 + 1408#64) else if .x18=r then 534#64 else s.getReg r
  | .callTail => if .x31=r then (pc 739) else if .x19=r then ((s.getReg .x2) + (s.getReg .x5)) else s.getReg r
  | .clearHead => if .x6=r then (((s.getReg .x10) + 2047#64) + 89#64) else if .x5=r then (s.getReg .x10) else s.getReg r
  | .clearCell => if .x5=r then ((s.getReg .x5) + 8#64) else s.getReg r
  | .restore => if .x6=r then 534#64 else if .x21=r then 0#64 else if .x20=r then 0#64 else if .x19=r then 0#64 else if .x18=r then 0#64 else if .x9=r then 0#64 else if .x8=r then 0#64 else if .x31=r then 0#64 else if .x30=r then 0#64 else if .x29=r then 0#64 else if .x28=r then 0#64 else if .x7=r then 0#64 else if .x5=r then 0#64 else s.getReg r
  | .copyHead => if .x7=r then ((s.getReg .x8) + (s.getReg .x18)) else if .x6=r then (s.getReg .x10) else if .x5=r then (s.getReg .x8) else s.getReg r
  | .copyByte => if .x6=r then ((s.getReg .x6) + 1#64) else if .x5=r then ((s.getReg .x5) + 1#64) else if .x28=r then ((s.getByte (s.getReg .x5)).zeroExtend 64) else s.getReg r
  | .writeHead => if .x5=r then (s.getReg .x8) else s.getReg r
  | .byteHead => if .x28=r then 0#64 else if .x6=r then 0#64 else s.getReg r
  | .bitStep => if .x28=r then ((s.getReg .x28) + 1#64) else if .x19=r then ((s.getReg .x19) + 2#64) else if .x6=r then ((s.getReg .x6) ||| (((((s.getByte ((((s.getHalfword (s.getReg .x19)).zeroExtend 64) >>> (3:Nat)) + (s.getReg .x10))).zeroExtend 64) >>> ((((s.getHalfword (s.getReg .x19)).zeroExtend 64) &&& 7#64).toNat % 64)) &&& 1#64) <<< ((s.getReg .x28).toNat % 64))) else if .x30=r then (((((s.getByte ((((s.getHalfword (s.getReg .x19)).zeroExtend 64) >>> (3:Nat)) + (s.getReg .x10))).zeroExtend 64) >>> ((((s.getHalfword (s.getReg .x19)).zeroExtend 64) &&& 7#64).toNat % 64)) &&& 1#64) <<< ((s.getReg .x28).toNat % 64)) else if .x29=r then (((s.getHalfword (s.getReg .x19)).zeroExtend 64) &&& 7#64) else s.getReg r
  | .emitByte => if .x5=r then ((s.getReg .x5) + 1#64) else s.getReg r
  | .ret => s.getReg r

def memOut (s : MachineState) : Block → MachineState
  | .entry => s
  | .guard => s
  | .empty => s
  | .init => s
  | .choose => s
  | .full => s
  | .next => s
  | .tail => s
  | .one => s
  | .two => s
  | .three => s
  | .pair => s
  | .single => s
  | .callTail => s
  | .clearHead => s
  | .clearCell => (s.setMem (s.getReg .x5) 0#64)
  | .restore => s
  | .copyHead => s
  | .copyByte => (s.setByte (s.getReg .x6) (((s.getByte (s.getReg .x5)).zeroExtend 64).truncate 8))
  | .writeHead => s
  | .byteHead => s
  | .bitStep => s
  | .emitByte => (s.setByte (s.getReg .x5) ((s.getReg .x6).truncate 8))
  | .ret => s

def pcOut (s : MachineState) : Block → Word
  | .entry => pc 705
  | .guard => if BitVec.ult (s.getReg .x17) ((s.getReg .x16) * 534#64) then pc 364 else pc 708
  | .empty => if (s.getReg .x16) == 0#64 then pc 745 else pc 709
  | .init => pc 713
  | .choose => if BitVec.ult (s.getReg .x9) (s.getReg .x20) then pc 721 else pc 714
  | .full => pc 759
  | .next => pc 713
  | .tail => if (s.getReg .x9) == 0#64 then pc 739 else pc 722
  | .one => if (s.getReg .x9) == 1#64 then pc 734 else pc 724
  | .two => if (s.getReg .x9) == 2#64 then pc 730 else pc 726
  | .three => pc 737
  | .pair => pc 737
  | .single => pc 737
  | .callTail => pc 759
  | .clearHead => pc 742
  | .clearCell => if ((s.getReg .x5) + 8#64) != (s.getReg .x6) then pc 742 else pc 745
  | .restore => pc 1
  | .copyHead => pc 762
  | .copyByte => if ((s.getReg .x5) + 1#64) != (s.getReg .x7) then pc 762 else pc 767
  | .writeHead => pc 768
  | .byteHead => pc 770
  | .bitStep => if ((s.getReg .x28) + 1#64) != (s.getReg .x21) then pc 770 else pc 782
  | .emitByte => if ((s.getReg .x5) + 1#64) != (s.getReg .x7) then pc 768 else pc 785
  | .ret => ((s.getReg .x31) &&& ~~~1#64)

def accessible (s : MachineState) : Block → Prop
  | .entry => True
  | .guard => True
  | .empty => True
  | .init => True
  | .choose => True
  | .full => True
  | .next => True
  | .tail => True
  | .one => True
  | .two => True
  | .three => True
  | .pair => True
  | .single => True
  | .callTail => True
  | .clearHead => True
  | .clearCell => accessValid (s.getReg .x5) 8=true
  | .restore => True
  | .copyHead => True
  | .copyByte => accessValid (s.getReg .x5) 1=true ∧ accessValid (s.getReg .x6) 1=true
  | .writeHead => True
  | .byteHead => True
  | .bitStep => accessValid (s.getReg .x19) 2=true ∧ accessValid ((((s.getHalfword (s.getReg .x19)).zeroExtend 64) >>> (3:Nat)) + (s.getReg .x10)) 1=true
  | .emitByte => accessValid (s.getReg .x5) 1=true
  | .ret => True


theorem zero (s : MachineState) : s.getReg .x0=0 := rfl
theorem mem_pc (s : MachineState) (p : Word) : (s.setPC p).mem=s.mem := rfl
theorem pc_pc (s : MachineState) (p : Word) : (s.setPC p).pc=p := rfl
theorem mem_reg (s : MachineState) (r : Reg) (v : Word) : (s.setReg r v).mem=s.mem := by cases r <;> rfl
theorem reg_byte (s : MachineState) (a : Word) (v : Byte) (r : Reg) :
    (s.setByte a v).getReg r=s.getReg r := by cases r <;> rfl
theorem reg_word (s : MachineState) (a v : Word) (r : Reg) :
    (s.setMem a v).getReg r=s.getReg r := by cases r <;> rfl
theorem pc_ite (p : Prop) [Decidable p] (s : MachineState) (a b : Word) :
    (if p then s.setPC a else s.setPC b).pc=(if p then a else b) := by split <;> rfl
theorem reg_ite (p : Prop) [Decidable p] (s : MachineState) (a b : Word) (r : Reg) :
    (if p then s.setPC a else s.setPC b).getReg r=s.getReg r := by split <;> rfl
theorem mem_ite (p : Prop) [Decidable p] (s : MachineState) (a b : Word) :
    (if p then s.setPC a else s.setPC b).mem=s.mem := by split <;> rfl
theorem imm12_0 : signExtend12 0=0#64 := rfl
theorem imm12_1 : signExtend12 1=1#64 := rfl
theorem imm12_2 : signExtend12 2=2#64 := rfl
theorem imm12_3 : signExtend12 3=3#64 := rfl
theorem imm12_4 : signExtend12 4=4#64 := rfl
theorem imm12_7 : signExtend12 7=7#64 := rfl
theorem imm12_8 : signExtend12 8=8#64 := rfl
theorem imm12_10 : signExtend12 10=10#64 := rfl
theorem imm12_14 : signExtend12 14=14#64 := rfl
theorem imm12_16 : signExtend12 16=16#64 := rfl
theorem imm12_48 : signExtend12 48=48#64 := rfl
theorem imm12_89 : signExtend12 89=89#64 := rfl
theorem imm12_534 : signExtend12 534=534#64 := rfl
theorem imm12_1068 : signExtend12 1068=1068#64 := rfl
theorem imm12_1408 : signExtend12 1408=1408#64 := rfl
theorem imm12_1602 : signExtend12 1602=1602#64 := rfl
theorem imm12_1760 : signExtend12 1760=1760#64 := rfl
theorem imm12_2047 : signExtend12 2047=2047#64 := rfl
theorem imm12_2464 : signExtend12 2464=18446744073709549984#64 := rfl
theorem imm12_4092 : signExtend12 4092=18446744073709551612#64 := rfl
theorem imm13_20 : signExtend13 20=20#64 := rfl
theorem imm13_32 : signExtend13 32=32#64 := rfl
theorem imm13_44 : signExtend13 44=44#64 := rfl
theorem imm13_72 : signExtend13 72=72#64 := rfl
theorem imm13_148 : signExtend13 148=148#64 := rfl
theorem imm13_6820 : signExtend13 6820=18446744073709550244#64 := rfl
theorem imm13_8128 : signExtend13 8128=18446744073709551552#64 := rfl
theorem imm13_8148 : signExtend13 8148=18446744073709551572#64 := rfl
theorem imm13_8176 : signExtend13 8176=18446744073709551600#64 := rfl
theorem imm13_8184 : signExtend13 8184=18446744073709551608#64 := rfl
theorem imm21_16 : signExtend21 16=16#64 := rfl
theorem imm21_32 : signExtend21 32=32#64 := rfl
theorem imm21_84 : signExtend21 84=84#64 := rfl
theorem imm21_168 : signExtend21 168=168#64 := rfl
theorem imm21_2820 : signExtend21 2820=2820#64 := rfl
theorem imm21_2094124 : signExtend21 2094124=18446744073709548588#64 := rfl
theorem imm21_2097124 : signExtend21 2097124=18446744073709551588#64 := rfl


set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

attribute [local simp] regOut memOut pcOut accessible

end CommitGolfCandidate.Layout2
