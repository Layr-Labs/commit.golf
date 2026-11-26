import CommitGolfCandidate.LateCheckMicroBlocks
import CommitGolfCandidate.LateOpenPathModel

namespace CommitGolfCandidate.Late.Check.Micro
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open CommitGolfCandidate.Late.Open (Calc Bin Expr original)
inductive Test where | dispatch | normalLen | batchLen | empty | parity | skipEven deriving DecidableEq
def Test.start : Test → Nat
  | .dispatch=>6 | .normalLen=>11 | .batchLen=>200 | .empty=>14 | .parity=>415 | .skipEven=>418
def Test.target : Test → Nat
  | .dispatch=>197 | .normalLen | .batchLen=>84 | .empty=>81 | .parity=>419 | .skipEven=>421
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

def dispatch (s : MachineState) := Test.dispatch.after (Part.dispatch.after s)
def lengthState (s : MachineState) (b : Bool) :=
  if b then Test.batchLen.after (Part.batchLen.after (dispatch s))
  else Test.normalLen.after (Part.normalLen.after (dispatch s))
def initialRows (s : MachineState) := Part.batchReady.after (lengthState s true)
def normalRows (s : MachineState) := Test.empty.after (Part.normalReady.after (lengthState s false))

theorem dispatch_reg (s : MachineState) (pc : s.pc=pcAt 0) (r : Reg) :
    (dispatch s).getReg r=(Part.dispatch.equation r).eval s := by
  exact (after_regs ..).trans ((basic .dispatch s pc rfl).regs r)

private theorem chooseDispatch (s : MachineState) (pc : s.pc=pcAt 0) :
    Test.dispatch.taken (Part.dispatch.after s) = (s.getReg .x16 == 128) := by
  have h := basic .dispatch s pc rfl
  change ((Part.dispatch.after s).getReg .x27 == (Part.dispatch.after s).getReg .x6) = _
  rw [h.regs,h.regs]
  change (s.getReg .x16+0 == 128) = _;simp

theorem dispatchRun (s : MachineState) (pc : s.pc=pcAt 0) :
    Runs s (dispatch s) 7 7 :=
  (basic .dispatch s pc rfl).runs.trans (test_run .dispatch _ (basic .dispatch s pc rfl).pc)

theorem dispatch_pc (s : MachineState) (pc : s.pc=pcAt 0) :
    (dispatch s).pc=pcAt (if s.getReg .x16=128 then 197 else 7) := by
  unfold dispatch;rw [after_pc,chooseDispatch s pc]; by_cases eq : s.getReg .x16=128 <;> simp [eq,Test.target,Test.start]

theorem dispatch_mem (s : MachineState) (pc : s.pc=pcAt 0) : (dispatch s).mem=s.mem :=
  (after_mem ..).trans (basic .dispatch s pc rfl).mem

theorem batchHeader (s : MachineState) (pc : s.pc=pcAt 0) (mode : s.getReg .x16=128)
    (size : s.getReg .x17=72704) : Runs s (initialRows s) 17 17 := by
  have pre := dispatch_pc s pc;rw [if_pos mode] at pre
  have len := basic .batchLen (dispatch s) pre rfl
  let t := Part.batchLen.after (dispatch s)
  have guard : Test.batchLen.taken t=false := by
    change (t.getReg .x6 != t.getReg .x17)=false
    rw [len.regs,len.regs]
    change (72704 != (dispatch s).getReg .x17)=false
    rw [dispatch_reg s pc];change (72704 != s.getReg .x17)=false;rw [size];rfl
  have ready : (lengthState s true).pc=pcAt 201 := by
    change (Test.batchLen.after t).pc=_
    rw [after_pc,guard];rfl
  exact (((dispatchRun s pc).trans len.runs).trans (test_run .batchLen t len.pc)).trans
    (basic .batchReady _ ready rfl).runs

structure NormalHeader (s t : MachineState) : Prop where
  pc : t.pc=pcAt (if s.getReg .x16=0 then 81 else 15)
  idx : t.getReg .x24=s.getReg .x13
  value : t.getReg .x8=s.getReg .x14
  proof : t.getReg .x25=s.getReg .x15
  root : t.getReg .x26=s.getReg .x11
  left : t.getReg .x27=s.getReg .x16
  scratch : t.getReg .x21=256
  depth : t.getReg .x30=24
  mem : t.mem=s.mem

theorem normalHeader (s : MachineState) (pc : s.pc=pcAt 0) (mode : s.getReg .x16≠128)
    (size : s.getReg .x16*792=s.getReg .x17) : Runs s (normalRows s) 15 18 ∧ NormalHeader s (normalRows s) := by
  have pp := dispatch_pc s pc;rw [if_neg mode] at pp
  have len := basic .normalLen (dispatch s) pp rfl
  let t:=Part.normalLen.after (dispatch s)
  have guard : Test.normalLen.taken t=false := by
    change (t.getReg .x7 != t.getReg .x17)=false
    rw [len.regs,len.regs]
    change ((dispatch s).getReg .x16*792 != (dispatch s).getReg .x17)=false
    rw [dispatch_reg s pc,dispatch_reg s pc]
    change (s.getReg .x16*792 != s.getReg .x17)=false
    rw [size];simp
  have enter : (lengthState s false).pc=pcAt 12 := by
    change (Test.normalLen.after t).pc=_;rw [after_pc,guard];rfl
  have ready := basic .normalReady _ enter rfl
  have left : (Part.normalReady.after (lengthState s false)).getReg .x27=s.getReg .x16 := by
    rw [ready.regs];change (Test.normalLen.after t).getReg .x27=_
    rw [after_regs,len.regs];change (dispatch s).getReg .x27=_
    rw [dispatch_reg s pc];change s.getReg .x16+0=s.getReg .x16;simp
  constructor
  · exact ((((dispatchRun s pc).trans len.runs).trans (test_run .normalLen t len.pc)).trans ready.runs).trans
      (test_run .empty _ ready.pc)
  · constructor
    · change (Test.empty.after _).pc=_
      rw [after_pc];change pcAt (if (Part.normalReady.after (lengthState s false)).getReg .x27 == (0 : Word) then 81 else 15)=_
      rw [left];by_cases z : s.getReg .x16=0 <;> simp [z]
    · change (Test.empty.after _).getReg .x24=_
      rw [after_regs,ready.regs];change (Test.normalLen.after t).getReg .x24=_
      rw [after_regs,len.regs];change (dispatch s).getReg .x24=_
      rw [dispatch_reg s pc];change s.getReg .x13+0=_;simp
    · change (Test.empty.after _).getReg .x8=_
      rw [after_regs,ready.regs];change (Test.normalLen.after t).getReg .x8=_
      rw [after_regs,len.regs];change (dispatch s).getReg .x8=_
      rw [dispatch_reg s pc];change s.getReg .x14+0=_;simp
    · change (Test.empty.after _).getReg .x25=_
      rw [after_regs,ready.regs];change (Test.normalLen.after t).getReg .x25=_
      rw [after_regs,len.regs];change (dispatch s).getReg .x25=_
      rw [dispatch_reg s pc];change s.getReg .x15+0=_;simp
    · change (Test.empty.after _).getReg .x26=_
      rw [after_regs,ready.regs];change (Test.normalLen.after t).getReg .x26=_
      rw [after_regs,len.regs];change (dispatch s).getReg .x26=_
      rw [dispatch_reg s pc];change s.getReg .x11+0=_;simp
    · change (Test.empty.after _).getReg .x27=_
      rw [after_regs,ready.regs];change (Test.normalLen.after t).getReg .x27=_
      rw [after_regs,len.regs];change (dispatch s).getReg .x27=_
      rw [dispatch_reg s pc];change s.getReg .x16+0=_;simp
    · exact (after_regs .empty _ .x21).trans (ready.regs .x21)
    · exact (after_regs .empty _ .x30).trans (ready.regs .x30)
    · exact (after_mem .empty _).trans (ready.mem.trans ((after_mem .normalLen t).trans (len.mem.trans (dispatch_mem s pc))))

end CommitGolfCandidate.Late.Check.Micro
