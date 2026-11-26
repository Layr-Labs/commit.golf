import CommitGolfCandidate.ReconstructedCheckEpilogue

namespace CommitGolfCandidate.Reconstruction.CheckHalt
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding Binding.Machine CheckRecorded CommitBlocks OracleComp
open TwoPermutationPrototype.Sampling
set_option maxHeartbeats 950000

def status (x : Word) : Word:=if x.slt 0 then 1 else 0

def finished (s : MachineState) : MachineState := (((s.setReg .x11 (s.getReg .x10)).setReg .x10 (status (s.getReg .x10))).setReg .x5 1).setPC (addr 23)

theorem trampoline (o : Oracle) (s : MachineState) (pc : s.pc=addr 20) : Segment o 3 s (finished s) [] := by
  let t:=(s.setReg .x11 (s.getReg .x10)).setPC (addr 21)
  let u:=(t.setReg .x10 (status (s.getReg .x10))).setPC (addr 22)
  have a : Segment o 1 s t []:=by
    apply plain _ _ _ _ (CheckMemoryOps.parsed (n:=20) (ins:=.base (.ADDI .x11 .x10 0)) (by decide) s pc)
    simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,pc,signExtend12,t];rfl
  have b : Segment o 1 t u []:=by
    apply plain _ _ _ _ (CheckMemoryOps.parsed (n:=21) (ins:=.base (.SLT .x10 .x10 .x0)) (by decide) t rfl)
    rfl
  have c : Segment o 1 u (finished s) []:=by
    apply plain _ _ _ _ (CheckMemoryOps.parsed (n:=22) (ins:=.base (.ADDI .x5 .x0 1)) (by decide) u rfl)
    rfl
  simpa using compose a (compose b c)

def exit (x : Word) : Riscv.Exit:=if x.slt 0 then .failure else .success

theorem terminal (o : Oracle) (s : MachineState) (pc : s.pc=addr 20) (fuel : Nat) :
    (observation o (4+fuel) s).1.1.exit=exit (s.getReg .x10) ∧ (observation o (4+fuel) s).1.2=[] ∧
      (observation o (4+fuel) s).2=0 ∧ (observation o (4+fuel) s).1.1.state.getReg .x11=s.getReg .x10 := by
  obtain ⟨fee,pre⟩:=trampoline o s pc
  have raw : execute image (fuel+1) (finished s) false = pure ⟨exit (s.getReg .x10),finished s,1,0⟩:=by
    rw [execute,CheckMemoryOps.parsed (n:=23) (ins:=.base .ECALL) (by decide) (finished s) rfl]
    change pure (⟨if (finished s).getReg .x10=0 then .success else .failure,finished s,1,0⟩ : Execution)=_
    have rv : (finished s).getReg .x10=status (s.getReg .x10):=rfl
    rw [rv]
    cases signed : (s.getReg .x10).slt 0#64 <;> simp [status,exit,signed]
  have endState : observation o (fuel+1) (finished s)=((⟨exit (s.getReg .x10),finished s,1,0⟩,[]),0) := by
    unfold observation;rw [raw,record_rows_pure];rfl
  rw [show 4+fuel=3+(fuel+1) by omega,pre,endState]
  exact ⟨rfl,rfl,rfl,rfl⟩

end CommitGolfCandidate.Reconstruction.CheckHalt
