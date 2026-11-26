import CommitGolfCandidate.S5Trace
namespace CommitGolfCandidate.S5Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

def emptyOpenPath : PathCode := [(0,.BNE .x16 .x0 20),(1,.ADDI .x11 .x0 0),
  (2,.ADDI .x5 .x0 1),(3,.ADDI .x10 .x0 0)]

def emptyCheckPath (accept : Bool) : PathCode := [
  (0,.ADDI .x8 .x11 0),(1,.ADDI .x9 .x13 0),(2,.ADDI .x18 .x14 0),(3,.ADDI .x19 .x15 0),
  (4,.ADD .x20 .x15 .x17),(5,.ADDI .x21 .x0 0),(6,.ADDI .x22 .x0 0),(7,.ADDI .x23 .x16 0),
  (8,.BNE .x23 .x0 16),(9,.BEQ .x17 .x0 8)] ++
  (if accept then [(11,.JAL .x0 9276),(2330,.ADDI .x5 .x0 1),(2331,.ADDI .x10 .x0 0)]
   else [(10,.JAL .x0 9292),(2333,.ADDI .x5 .x0 1),(2334,.ADDI .x10 .x0 1)])

private theorem opening_sites : emptyOpenPath.all (matchesWord .opening) := by decide +kernel
private theorem checking_sites (a : Bool) : (emptyCheckPath a).all (matchesWord .check) := by cases a <;> decide +kernel

private theorem empty_open_state (s : MachineState) (pc : s.pc=pcAt 0) (empty : s.getReg .x16=0) :
    pathReady s emptyOpenPath ∧
    let t := pathEnd s emptyOpenPath
    t.pc=pcAt 4 ∧ t.getReg .x5=1 ∧ t.getReg .x10=0 ∧ t.getReg .x11=0 := by
  change s.regs .x16=0 at empty
  simp +decide [emptyOpenPath,pathReady,pathEnd,pc,empty,ordinaryStep,instructionCycles,memoryArgumentsValid,
    memAccess,execInstrBr,MachineState.getReg,MachineState.setReg,MachineState.setPC,pcAt,signExtend12] at * <;> simp_all +decide

private theorem empty_check_state (s : MachineState) (pc : s.pc=pcAt 0) (empty : s.getReg .x16=0) (a : Bool)
    (val : (s.getReg .x17==0)=a) :
    pathReady s (emptyCheckPath a) ∧
    let t:=pathEnd s (emptyCheckPath a)
    t.pc=pcAt (if a then 2332 else 2335) ∧ t.getReg .x5=1 ∧ t.getReg .x10=(if a then 0 else 1) := by
  change s.regs .x16=0 at empty
  change (s.regs .x17==0)=a at val
  cases a <;> simp +decide [emptyCheckPath,pathReady,pathEnd,pc,empty,val,ordinaryStep,instructionCycles,
    memoryArgumentsValid,memAccess,execInstrBr,MachineState.getReg,MachineState.setReg,MachineState.setPC,pcAt,signExtend12] at * <;> simp_all +decide

theorem empty_open_run (s : MachineState) (pc : s.pc=pcAt 0) (empty : s.getReg .x16=0) (fuel : Nat) :
    let t:=pathEnd s emptyOpenPath
    execute (image .opening) (fuel+5) s true=pure ⟨.success,t,5,0⟩ ∧ t.getReg .x11=0 := by
  obtain ⟨valid,last,sel,success,length⟩:=empty_open_state s pc empty
  refine ⟨?_,length⟩
  have halt:=site (p:=.opening) (n:=4) (op:=.ECALL) (by decide) (by rfl) _ last
  rw [show fuel+5=(fuel+1)+emptyOpenPath.length by rfl,path_run _ _ _ _ opening_sites valid]
  rw [execute,halt,sel,success];rfl

theorem empty_check_run (s : MachineState) (pc : s.pc=pcAt 0) (empty : s.getReg .x16=0)
    (a : Bool) (val : (s.getReg .x17==0)=a) (fuel : Nat) :
    execute (image .check) (fuel+14) s false=pure ⟨if a then .success else .failure,pathEnd s (emptyCheckPath a),14,0⟩ := by
  obtain ⟨valid,last,sel,code⟩:=empty_check_state s pc empty a val
  have haltSite : Site .check (if a then 2332 else 2335) .ECALL := by
    cases a <;> apply site (by decide) <;> rfl
  rw [show fuel+14=(fuel+1)+(emptyCheckPath a).length by cases a <;> rfl,path_run _ _ _ _ (checking_sites a) valid]
  rw [execute,haltSite _ last,sel,code]
  cases a <;> rfl
end CommitGolfCandidate.S5Machine
