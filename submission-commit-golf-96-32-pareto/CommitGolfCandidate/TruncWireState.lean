import CommitGolfCandidate.TruncMoves
import CommitGolfCandidate.TruncSteps
namespace CommitGolfCandidate.Trunc.Wire
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 12000

def blockPrefix (ops : List Instr) (s : MachineState) (k : Nat) := (ops.take k).foldl execInstrBr s

def srcWidth (back record : Bool) := if back then short record else wide record
def dstWidth (back record : Bool) := if back then wide record else short record

def pointers (back record : Bool) (s : MachineState) :=
  let a:=BitVec.ofNat 64 (srcWidth back record)
  let b:=BitVec.ofNat 64 (dstWidth back record)
  ((s.setReg .x18 (if back then s.getReg .x18-a else s.getReg .x18+a)).setReg
    .x19 (if back then s.getReg .x19-b else s.getReg .x19+b)).setPC (s.pc+8)

def before (back record : Bool) (s : MachineState) := if back then pointers back record s else s
def moved (back record : Bool) (s : MachineState) :=
  (sequence back record).foldl execInstrBr (before back record s)
def ready (back record : Bool) (s : MachineState) :=
  let m:=moved back record s
  if back then m else pointers back record m

def regStep (back record : Bool) (entry : Word) (s : MachineState) : MachineState :=
  let t:=ready back record s
  let r:=t.getReg .x28-1
  (t.setReg .x28 r).setPC (if r=0 then entry+BitVec.ofNat 64 (4*((sequence back record).length+4)) else entry)

def initOps (back : Bool) : List Instr := if back then
  [.ADDI .x18 .x0 1, .SLLI .x18 .x18 11, .ADDI .x18 .x18 544, .SLLI .x18 .x18 11, .ADDI .x18 .x18 35, .SLLI .x18 .x18 11, .ADDI .x18 .x18 544, .ADDI .x19 .x0 1, .SLLI .x19 .x19 11, .ADDI .x19 .x19 544, .SLLI .x19 .x19 11, .ADDI .x19 .x19 37, .SLLI .x19 .x19 11, .ADDI .x19 .x19 32, .ADDI .x28 .x0 128]
  else [.ADDI .x18 .x0 1, .SLLI .x18 .x18 11, .ADDI .x18 .x18 544, .SLLI .x18 .x18 11, .ADDI .x18 .x18 2, .SLLI .x18 .x18 11, .ADDI .x18 .x18 32, .ADDI .x19 .x0 1, .SLLI .x19 .x19 11, .ADDI .x19 .x19 544, .SLLI .x19 .x19 11, .ADDI .x19 .x19 2, .SLLI .x19 .x19 11, .ADDI .x19 .x19 32, .ADDI .x28 .x0 128]
def endOps (back : Bool) : List Instr := if back then
  [.ADDI .x17 .x0 35, .SLLI .x17 .x17 11, .ADDI .x17 .x17 0, .ADDI .x18 .x0 0, .ADDI .x19 .x0 0, .ADDI .x28 .x0 0, .ADDI .x6 .x0 128, .JAL .x0 2094080]
  else [.ADDI .x11 .x0 33, .SLLI .x11 .x11 11, .ADDI .x11 .x11 512, .ADDI .x5 .x0 1, .ADDI .x10 .x0 0]
def init (back : Bool) (s : MachineState) := (initOps back).foldl execInstrBr s
def endState (back : Bool) (s : MachineState) := (endOps back).foldl execInstrBr s
def reset (s : MachineState) := execInstrBr s (.ADDI .x28 .x0 128)
def packedEnd (s : MachineState) :=
  let first:=init false (s.setPC (loc 142))
  let rows:=(regStep false true (loc 157))^[128] first
  endState false ((regStep false false (loc 664))^[128] (reset rows))
def unpackedEnd (s : MachineState) :=
  let first:=init true (s.setPC (loc 413))
  let slots:=(regStep true false (loc 428))^[128] first
  endState true ((regStep true true (loc 464))^[128] (reset slots))

def PackRun : Prop := ∀ (s : MachineState) (f : Nat) (coins : Bool), s.pc=loc 141 →
  execute (submission.image .opening) (69143+f) s coins=pure ⟨.success,packedEnd s,69143,0⟩

def PackedBytes : Prop := ∀ (s : MachineState) (i : Nat), i<68096 →
  byte (packedEnd s) (10871640096+i)=byte s (10871640096+narrowIndex i)

@[simp] theorem packedLength (s : MachineState) : (packedEnd s).getReg .x11=68096 := by
  have endLength (t : MachineState) : (endState false t).getReg .x11=68096 := by
    simp [endState,endOps,execInstrBr,MachineState.getReg,MachineState.setReg,MachineState.setPC,signExtend12]
  exact endLength _

end CommitGolfCandidate.Trunc.Wire
