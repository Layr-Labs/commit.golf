import CommitGolfCandidate.TruncGuardModel
import CommitGolfCandidate.TruncSteps
namespace CommitGolfCandidate.Trunc.CapGuard
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8000
set_option maxHeartbeats 200000

def cleared (s : MachineState) := s.setHalfword (s.getReg .x12+30) 0
def ghost (s : MachineState) (b : Bool) (v : Word) (i : Nat) : MachineState :=
  {s with regs:=fun r=>if r=.x12 then v else s.regs r,
          mem:=(if b then cleared s else s).mem,pc:=loc i}

theorem gzero (s : MachineState) (b : Bool) (v : Word) (i : Nat) : (ghost s b v i).getReg .x0=0#64 := rfl

theorem atStart (s : MachineState) (i : Nat) (pc : s.pc=loc i) : ghost s false (s.getReg .x12) i=s := by
  have eqn : (fun r=>if r=Reg.x12 then s.getReg .x12 else s.regs r)=s.regs := by
    funext r;by_cases e : r=.x12 <;> simp [e,MachineState.getReg]
  change {s with regs:=_,mem:=s.mem,pc:=loc i}=s
  rw [eqn,←pc]

theorem atEnd (s : MachineState) (b : Bool) (i : Nat) :
    ghost s b (s.getReg .x12) i = (if b then cleared s else s).setPC (loc i) := by
  cases b <;> cases s <;> simp only [ghost,cleared,MachineState.setPC,MachineState.setHalfword,MachineState.setMem,
    Bool.false_eq_true,ite_false,ite_true,MachineState.mk.injEq,true_and,and_true]
  all_goals funext r;by_cases e : r=.x12 <;> simp [e,MachineState.getReg]

theorem g12 (s : MachineState) (b v i) : (ghost s b v i).getReg .x12=v := by simp [ghost,MachineState.getReg]
theorem g30 (s : MachineState) (b v i) : (ghost s b v i).getReg .x30=s.getReg .x30 := rfl
theorem g19 (s : MachineState) (b v i) : (ghost s b v i).getReg .x19=s.getReg .x19 := rfl
theorem gpc (s : MachineState) (b v i) : (ghost s b v i).pc=loc i := rfl

theorem samePC (s : MachineState) (b v i j) : (ghost s b v i).setPC (loc j)=ghost s b v j := rfl
theorem new12 (s : MachineState) (b v i j) (z : Word) :
    ((ghost s b v i).setReg .x12 z).setPC (loc j)=ghost s b z j := by
  cases s;simp only [ghost,MachineState.setPC,MachineState.setReg,MachineState.mk.injEq,true_and,and_true]
  funext r;by_cases e : r=.x12 <;> simp [e]

theorem add (s : MachineState) (b : Bool) (v z : Word) (i j : Nat) (off : BitVec 12)
    (bi : i<2048) (cd : ((submission.image .check).code[i]?).bind decodeInstruction=some (.base (.ADDI .x12 .x12 off)))
    (inc : loc i+4=loc j) (value : v+signExtend12 off=z) :
    Runs (submission.image .check) (ghost s b v i) (ghost s b z j) 1 1 := by
  apply one i _ _ (.ADDI .x12 .x12 off) bi rfl cd _ rfl
  simp only [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,gpc,g12,value,inc,new12,ite_true]

theorem jump (s : MachineState) (b : Bool) (v : Word) (i j : Nat) (off : BitVec 21)
    (bi : i<2048) (cd : ((submission.image .check).code[i]?).bind decodeInstruction=some (.base (.JAL .x0 off)))
    (toPC : loc i+signExtend21 off=loc j) :
    Runs (submission.image .check) (ghost s b v i) (ghost s b v j) 1 1 :=
  jumpAt _ _ i j off bi rfl cd toPC

theorem nop (s : MachineState) (b : Bool) (v : Word) (i j : Nat) (bi : i<2048)
    (cd : ((submission.image .check).code[i]?).bind decodeInstruction=some (.base (.ADDI .x0 .x0 0)))
    (inc : loc i+4=loc j) : Runs (submission.image .check) (ghost s b v i) (ghost s b v j) 1 1 := by
  apply one i _ _ _ bi rfl cd _ rfl
  simp only [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,gpc,inc];rfl


theorem zeroEdge (s : MachineState) (v : Word) (i j : Nat) (off : BitVec 13) (bi : i<2048)
    (cd : ((submission.image .check).code[i]?).bind decodeInstruction=some (.base (.BEQ .x12 .x0 off)))
    (toPC : (if v=0 then loc i+signExtend13 off else loc i+4)=loc j) :
    Runs (submission.image .check) (ghost s false v i) (ghost s false v j) 1 1 := by
  apply one i _ _ _ bi rfl cd _ rfl
  by_cases e : v=0#64
  · have dst : loc i+signExtend13 off=loc j := (if_pos (show v=0 from e)).symm.trans toPC
    simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,gpc,g12,
      gzero,e,dst,samePC] <;> first | rfl | rw [show loc i+4#64=loc j from dst];rfl
  · have dst : loc i+4=loc j := (if_neg (show v≠0 from e)).symm.trans toPC
    simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,gpc,g12,
      gzero,e,dst,samePC] <;> first | rfl | rw [show loc i+4#64=loc j from dst];rfl

private theorem restoreAddr (x : Word) : (x-544)+signExtend12 574=x+30 := by
  simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc];rfl

theorem clearEdge (s : MachineState) (valid : accessValid (s.getReg .x12+30) 2)
    (v : Word) (value : v=s.getReg .x12-544) :
    Runs (submission.image .check) (ghost s false v 1021) (ghost s true v 1022) 1 1 := by
  apply one 1021 _ _ (.SH .x12 .x0 574) (by decide) rfl (by rfl) _ rfl
  have addr : (ghost s false v 1021).getReg .x12+signExtend12 574=s.getReg .x12+30 := by rw [g12,value,restoreAddr]
  have ok : memoryArgumentsValid (ghost s false v 1021) (.SH .x12 .x0 574)=true := by
    change accessValid (_+_) 2=true;rw [addr];exact valid
  simp only [ordinaryStep,ok,ite_true,execInstrBr,addr,gpc,show (ghost s false v 1021).getReg .x0=0#64 from rfl]
  rfl

theorem runCap (s : MachineState) (pc : s.pc=loc 389) (valid : accessValid (s.getReg .x12+30) 2) :
    Runs (submission.image .check) s ((if s.getReg .x12=544 then s else cleared s).setPC (loc 1026)) 6 6 := by
  let x:=s.getReg .x12
  have h0:=jump s false x 389 1019 2520 (by decide) (by rfl) (by decide)
  have h1:=add s false x (x-544) 1019 1020 3552 (by decide) (by rfl) (by decide)
    (by simp only [BitVec.sub_eq_add_neg];rfl)
  have final (b : Bool) := add s b (x-544) x 1025 1026 544 (by decide) (by rfl) (by decide)
    (by change x-544+544=x;exact BitVec.sub_add_cancel x 544)
  by_cases root : x=544
  · have eq : x-544=0 := by rw [root];decide
    have h2:=zeroEdge s (x-544) 1020 1023 12 (by decide) (by rfl) (by rw [if_pos eq];decide)
    have h3:=nop s false (x-544) 1023 1024 (by decide) (by rfl) (by decide)
    have h4:=jump s false (x-544) 1024 1025 4 (by decide) (by rfl) (by decide)
    have h:=chain (chain (chain (chain (chain h0 h1) h2) h3) h4) (final false)
    rw [atStart s 389 pc,atEnd] at h
    rw [if_pos root];exact h
  · have ne : x-544≠0 := by
      intro eq;apply root
      calc x=(x-544)+544 := (BitVec.sub_add_cancel x _).symm
           _=544 := by rw [eq];decide
    have h2:=zeroEdge s (x-544) 1020 1021 12 (by decide) (by rfl) (by rw [if_neg ne];decide)
    have h3:=clearEdge s valid (x-544) rfl
    have h4:=jump s true (x-544) 1022 1025 12 (by decide) (by rfl) (by decide)
    have h:=chain (chain (chain (chain (chain h0 h1) h2) h3) h4) (final true)
    rw [atStart s 389 pc,atEnd] at h
    rw [if_neg root];exact h

end CommitGolfCandidate.Trunc.CapGuard
