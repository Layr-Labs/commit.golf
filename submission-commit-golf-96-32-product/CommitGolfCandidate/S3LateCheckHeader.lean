import CommitGolfCandidate.TruncWireImage
import CommitGolfCandidate.S3LateCheckMicroBlocks
import CommitGolfCandidate.LateOpenWrites
import CommitGolfCandidate.LateOpenControl
import CommitGolfCandidate.LateMemoryStep

namespace CommitGolfCandidate.Late.Check3.Micro
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open CommitGolfCandidate.Late.Open (Calc Bin Expr original)
inductive Test where | dispatch | normalLen | batchLen | empty | parity | skipEven deriving DecidableEq
def Test.start : Test → Nat
  | .dispatch=>6 | .normalLen=>11 | .batchLen=>200 | .empty=>14 | .parity=>415 | .skipEven=>418
def Test.target : Test → Nat
  | .dispatch=>433 | .normalLen | .batchLen=>84 | .empty=>81 | .parity=>419 | .skipEven=>421
def Test.args : Test → Reg × Reg
  | .dispatch=>(.x27,.x6) | .normalLen=>(.x7,.x17) | .batchLen=>(.x6,.x17)
  | .empty=>(.x27,.x0) | .parity=>(.x28,.x0) | .skipEven=>(.x0,.x0)
def Test.beq : Test → Bool
  | .normalLen | .batchLen => false | _ => true
def Test.bits (b : Test) : BitVec 13 := BitVec.ofInt 13 (4*((b.target : Int)-(b.start : Int)))
def Test.instr (b : Test) := if b.beq then Instr.BEQ b.args.1 b.args.2 b.bits else Instr.BNE b.args.1 b.args.2 b.bits
def Test.taken (b : Test) (s : MachineState) : Bool :=
  if b.beq then s.getReg b.args.1 == s.getReg b.args.2 else s.getReg b.args.1 != s.getReg b.args.2
def Test.after (b : Test) (s : MachineState) :=
  s.setPC (pcAt (if b.taken s then b.target else b.start+1))

theorem test_run (b : Test) (s : MachineState) (pc : s.pc=pcAt b.start) : Runs s (b.after s) 1 1 := by
  have enc : decodeInstruction (checkWord b.start)=some (.base b.instr) := by cases b <;> rfl
  have bound : b.start<433 := by cases b <;> decide
  have rs : Runs s (execInstrBr s b.instr) 1 1 := by
    have st : ordinaryStep s (.base b.instr)=some (execInstrBr s b.instr) := by cases b <;> rfl
    have cost : instructionCycles (.base b.instr)=1 := by cases b <;> rfl
    exact cost ▸ one _ bound _ enc s _ pc st
  have tgt : pcAt b.start+signExtend13 b.bits=pcAt b.target := by cases b <;> rfl
  have fall := pc_succ b.start
  have same : execInstrBr s b.instr = b.after s := by
    have choose (c : Bool) :
        (if c then s.setPC (s.pc+signExtend13 b.bits) else s.setPC (s.pc+4)) =
          s.setPC (pcAt (if c then b.target else b.start+1)) := by
      cases c <;> simp only [Bool.false_eq_true,if_false,if_true,pc,tgt,fall]
    by_cases eq : b.beq = true
    · simp only [Test.instr,Test.after,Test.taken,if_pos eq]
      exact choose (s.getReg b.args.1 == s.getReg b.args.2)
    · simp only [Test.instr,Test.after,Test.taken,if_neg eq]
      exact choose (s.getReg b.args.1 != s.getReg b.args.2)
  exact same ▸ rs


theorem after_regs (b : Test) (s : MachineState) (r : Reg) : (b.after s).getReg r=s.getReg r :=
  MachineState.getReg_setPC

theorem after_pc (b : Test) (s : MachineState) : (b.after s).pc=pcAt (if b.taken s then b.target else b.start+1) := rfl

theorem after_mem (b : Test) (s : MachineState) : (b.after s).mem=s.mem := rfl

theorem basic (b : Part) (s : MachineState) (pc : s.pc=pcAt b.start) (noRead : b.reads=[]) : BlockResult b s :=
  block_result b s pc (by rw [noRead];simp)

end CommitGolfCandidate.Late.Check3.Micro
