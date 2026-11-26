import CommitGolfCandidate.TruncGuardModel
import CommitGolfCandidate.TruncSteps
namespace CommitGolfCandidate.Trunc.Guard
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8000
set_option maxHeartbeats 200000

def cleared (s : MachineState) := s.setHalfword (s.getReg .x21+30) 0
def ghost (s : MachineState) (b : Bool) (v : Word) (i : Nat) : MachineState :=
  {s with regs:=fun r=>if r=.x29 then v else s.regs r,
          mem:=(if b then cleared s else s).mem,pc:=loc i}

theorem gzero (s : MachineState) (b : Bool) (v : Word) (i : Nat) : (ghost s b v i).getReg .x0=0#64 := rfl

theorem atStart (s : MachineState) (i : Nat) (pc : s.pc=loc i) : ghost s false (s.getReg .x29) i=s := by
  have eqn : (fun r=>if r=Reg.x29 then s.getReg .x29 else s.regs r)=s.regs := by
    funext r;by_cases e : r=.x29 <;> simp [e,MachineState.getReg]
  change {s with regs:=_,mem:=s.mem,pc:=loc i}=s
  rw [eqn,←pc]

theorem atEnd (s : MachineState) (b : Bool) (i : Nat) :
    ghost s b (s.getReg .x29) i = (if b then cleared s else s).setPC (loc i) := by
  cases b <;> cases s <;> simp only [ghost,cleared,MachineState.setPC,MachineState.setHalfword,MachineState.setMem,
    Bool.false_eq_true,ite_false,ite_true,MachineState.mk.injEq,true_and,and_true]
  all_goals funext r;by_cases e : r=.x29 <;> simp [e,MachineState.getReg]

theorem g29 (s : MachineState) (b v i) : (ghost s b v i).getReg .x29=v := by simp [ghost,MachineState.getReg]
theorem g30 (s : MachineState) (b v i) : (ghost s b v i).getReg .x30=s.getReg .x30 := rfl
theorem g19 (s : MachineState) (b v i) : (ghost s b v i).getReg .x19=s.getReg .x19 := rfl
theorem g21 (s : MachineState) (b v i) : (ghost s b v i).getReg .x21=s.getReg .x21 := rfl
theorem gpc (s : MachineState) (b v i) : (ghost s b v i).pc=loc i := rfl

theorem samePC (s : MachineState) (b v i j) : (ghost s b v i).setPC (loc j)=ghost s b v j := rfl
theorem new29 (s : MachineState) (b v i j) (z : Word) :
    ((ghost s b v i).setReg .x29 z).setPC (loc j)=ghost s b z j := by
  cases s;simp only [ghost,MachineState.setPC,MachineState.setReg,MachineState.mk.injEq,true_and,and_true]
  funext r;by_cases e : r=.x29 <;> simp [e]

theorem add (s : MachineState) (b : Bool) (v z : Word) (i j : Nat) (off : BitVec 12)
    (bi : i<2048) (cd : ((Trunc.wireImage true).code[i]?).bind decodeInstruction=some (.base (.ADDI .x29 .x29 off)))
    (inc : loc i+4=loc j) (value : v+signExtend12 off=z) :
    Runs (Trunc.wireImage true) (ghost s b v i) (ghost s b z j) 1 1 := by
  apply one i _ _ (.ADDI .x29 .x29 off) bi rfl cd _ rfl
  simp only [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,gpc,g29,value,inc,new29,ite_true]

theorem jump (s : MachineState) (b : Bool) (v : Word) (i j : Nat) (off : BitVec 21)
    (bi : i<2048) (cd : ((Trunc.wireImage true).code[i]?).bind decodeInstruction=some (.base (.JAL .x0 off)))
    (toPC : loc i+signExtend21 off=loc j) :
    Runs (Trunc.wireImage true) (ghost s b v i) (ghost s b v j) 1 1 :=
  jumpAt _ _ i j off bi rfl cd toPC

theorem nop (s : MachineState) (b : Bool) (v : Word) (i j : Nat) (bi : i<2048)
    (cd : ((Trunc.wireImage true).code[i]?).bind decodeInstruction=some (.base (.ADDI .x0 .x0 0)))
    (inc : loc i+4=loc j) : Runs (Trunc.wireImage true) (ghost s b v i) (ghost s b v j) 1 1 := by
  apply one i _ _ _ bi rfl cd _ rfl
  simp only [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,gpc,inc];rfl

theorem ge (s : MachineState) (v : Word) (i j : Nat) (off : BitVec 13) (bi : i<2048)
    (cd : ((Trunc.wireImage true).code[i]?).bind decodeInstruction=some (.base (.BGEU .x29 .x30 off)))
    (toPC : (if ¬v.toNat<(s.getReg .x30).toNat then loc i+signExtend13 off else loc i+4)=loc j) :
    Runs (Trunc.wireImage true) (ghost s false v i) (ghost s false v j) 1 1 := by
  apply one i _ _ _ bi rfl cd _ rfl
  by_cases lt : v.toNat<(s.getReg .x30).toNat <;>
    simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,gpc,g30,g29,BitVec.ult,lt] at toPC ⊢ <;> rw [toPC] <;> rfl

theorem nz (s : MachineState) (v : Word) (i j : Nat) (off : BitVec 13) (bi : i<2048)
    (cd : ((Trunc.wireImage true).code[i]?).bind decodeInstruction=some (.base (.BNE .x29 .x0 off)))
    (toPC : (if v≠0 then loc i+signExtend13 off else loc i+4)=loc j) :
    Runs (Trunc.wireImage true) (ghost s false v i) (ghost s false v j) 1 1 := by
  apply one i _ _ _ bi rfl cd _ rfl
  by_cases e : v=0#64
  · have dst : loc i+4=loc j := (if_neg (not_not_intro (show v=0 from e))).symm.trans toPC
    simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,gpc,g29,
      gzero,e,dst,samePC] <;> first | rfl | rw [show loc i+4#64=loc j from dst];rfl
  · have dst : loc i+signExtend13 off=loc j := (if_pos (show v≠0 from e)).symm.trans toPC
    simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,gpc,g29,
      gzero,e,dst,samePC] <;> first | rfl | rw [show loc i+4#64=loc j from dst];rfl

theorem slotZero (s : MachineState) (v : Word) (i j : Nat) (off : BitVec 13) (bi : i<2048)
    (cd : ((Trunc.wireImage true).code[i]?).bind decodeInstruction=some (.base (.BEQ .x19 .x0 off)))
    (toPC : (if s.getReg .x19=0 then loc i+signExtend13 off else loc i+4)=loc j) :
    Runs (Trunc.wireImage true) (ghost s false v i) (ghost s false v j) 1 1 := by
  apply one i _ _ _ bi rfl cd _ rfl
  by_cases e : s.getReg .x19=0#64
  · have dst : loc i+signExtend13 off=loc j := (if_pos (show s.getReg .x19=0 from e)).symm.trans toPC
    simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,gpc,g19,
      gzero,e,dst,samePC] <;> first | rfl | rw [show loc i+4#64=loc j from dst];rfl
  · have dst : loc i+4=loc j := (if_neg (show s.getReg .x19≠0 from e)).symm.trans toPC
    simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,gpc,g19,
      gzero,e,dst,samePC] <;> first | rfl | rw [show loc i+4#64=loc j from dst];rfl

theorem mask (s : MachineState) (scratch : s.getReg .x21=256) (v : Word) (i j : Nat) (bi : i<2048)
    (cd : ((Trunc.wireImage true).code[i]?).bind decodeInstruction=some (.base (.SH .x21 .x0 30)))
    (inc : loc i+4=loc j) : Runs (Trunc.wireImage true) (ghost s false v i) (ghost s true v j) 1 1 := by
  apply one i _ _ _ bi rfl cd _ rfl
  have valid : memoryArgumentsValid (ghost s false v i) (.SH .x21 .x0 30)=true := by
    change accessValid ((ghost s false v i).getReg .x21+signExtend12 30) 2=true
    rw [g21,scratch];decide
  simp only [ordinaryStep,valid,ite_true,execInstrBr,g21,gpc,inc,show signExtend12 30=30#64 by decide,
    show (ghost s false v i).getReg .x0=0#64 from rfl]
  rfl

end CommitGolfCandidate.Trunc.Guard
