import CommitGolfCandidate.Stage3cOpenDispatch
import CommitGolfCandidate.Stage3cOpenTable
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

def setupList (batch : Bool) : List Instr :=
  [.ADDI .x8 .x12 0,.ADDI .x9 .x13 0,.ADDI .x18 .x15 0,.ADDI .x19 .x15 0,.LUI .x6 393216,.ADD .x20 .x8 .x6] ++
  if batch then [.ADDI .x21 .x0 1024,.ADDI .x23 .x0 0,.ADDI .x24 .x0 0,.ADDI .x25 .x0 3,.ADDI .x26 .x0 1,.ADDI .x27 .x0 64]
  else [.ADDI .x22 .x16 0,.ADDI .x25 .x0 3]
def setupPC (b : Bool) := if b then 8 else 368
def openSetup (b : Bool) (s : MachineState) := (setupList b).foldl execInstrBr s

private theorem setup_layout (b : Bool) : (setupList b).all setupOp ∧
    ∀ j : Fin (setupList b).length, matchesWord .opening (setupPC b+j.val,(setupList b)[j.val]) := by cases b <;> decide +kernel

theorem setup_run (s : MachineState) (b : Bool) (pc : s.pc=pcAt (setupPC b)) :
    Runs s (openSetup b s) (setupList b).length (setupList b).length ∧
      (openSetup b s).pc=pcAt (if b then 20 else 376) ∧ (openSetup b s).mem=s.mem := by
  obtain ⟨ok,sites⟩:=setup_layout b
  have sane:=List.all_eq_true.mp ok
  have frame:=header_properties _ s sane
  refine ⟨?_,?_,frame.1⟩
  · intro fuel;apply execute_linear .opening true _ _ _ _ pc (fun op h=>header_straight op (sane _ h))
    intro j hj
    have h:=sites ⟨j,hj⟩
    have bound : setupPC b+j<words .opening := by
      have lengthBound : (setupList b).length≤12 := by cases b <;> decide
      have startBound : setupPC b≤368 := by cases b <;> decide
      change setupPC b+j<939;omega
    apply site bound;simpa [matchesWord,bound] using h
  · rw [show (openSetup b s).pc=_ from frame.2,pc,pc_delta];cases b <;> rfl

structure SeedRegs (b : Bool) (k : Nat) (s : MachineState) : Prop where
  base : s.getReg .x8=W tdBase
  indices : s.getReg .x9=W indexBase
  start : s.getReg .x18=W proofBase
  dest : s.getReg .x19=W proofBase
  salts : s.getReg .x20=W rowBase
  marks : b=true→s.getReg .x21=1024
  pending : b=true→s.getReg .x23=0 ∧ s.getReg .x24=0
  constants : b=true→s.getReg .x26=1 ∧ s.getReg .x27=64
  count : b=false→s.getReg .x22=W k

theorem setup_regs (s : MachineState) (b : Bool) (k : Nat) (td : s.getReg .x12=W tdBase)
    (ix : s.getReg .x13=W indexBase) (out : s.getReg .x15=W proofBase) (n : s.getReg .x16=W k) :
    SeedRegs b k (openSetup b s) := by
  change s.regs .x12=W tdBase at td
  change s.regs .x13=W indexBase at ix
  change s.regs .x15=W proofBase at out
  change s.regs .x16=W k at n
  cases b <;> constructor <;> simp +decide [openSetup,setupList,execInstrBr,MachineState.getReg,
    MachineState.setPC,MachineState.setReg,signExtend12,W,tdBase,indexBase,proofBase,rowBase,td,ix,out,n] at * <;> simp_all +decide
end CommitGolfCandidate.Chained.BinaryMachine.Open
