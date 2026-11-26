import CommitGolfCandidate.TruncPhaseBoth
namespace CommitGolfCandidate.Trunc.Wire
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 20000
set_option maxHeartbeats 400000

theorem packedBytes : PackedBytes := by
  intro s i hi
  have f : Frame false (s.setPC (loc 140)) (packedEnd s) 69120 := (phases false (s.setPC (loc 140)) rfl).2
  have h:=f (base+i) (by unfold base;omega)
  have inside : passed false 69120 (base+i) := by unfold passed;dsimp;omega
  rw [if_pos inside,show base+i-base=i by omega] at h
  exact h

private theorem endOpeningPC (t : MachineState) (pc : t.pc=loc 704) : (endState false t).pc=loc 709 := by
  simp [endState,endOps,execInstrBr,MachineState.setPC,pc,loc]

theorem packRun : PackRun := by
  intro s fuel coins pc
  have jump:=jumpAt (submission.image .opening) s 134 140 24 (by decide) pc (by rfl) (by decide)
  have body : Runs (submission.image .opening) (s.setPC (loc 140)) (packedEnd s) 70165 70165 := (phases false (s.setPC (loc 140)) rfl).1
  let z:=packedEnd s
  have final : z.pc=loc 709 := by
    have c:=firstCursors false (s.setPC (loc 140)) rfl
    have f:=allCursors false true 128 (by decide) _ c
    have c2:=nextCursors false _ f
    have last:=allCursors false false 128 (by decide) _ c2
    have p:=endPC false _ last
    exact endOpeningPC (secondPhase false (s.setPC (loc 140))) p
  have opcode:=fetchAt (submission.image .opening) z 709 .ECALL (by decide) final (by rfl)
  have tailRegs (t : MachineState) : (endState false t).getReg .x5=1 ∧ (endState false t).getReg .x10=0 := by
    simp [endState,endOps,execInstrBr,MachineState.getReg,MachineState.setPC,MachineState.setReg,signExtend12]
  have t0 : z.getReg .x5=1 := (tailRegs _).1
  have a0 : z.getReg .x10=0 := (tailRegs _).2
  rw [show 70167+fuel=1+(70165+(fuel+1)) by omega,jump,body]
  change (do let a←(do let r←execute (submission.image .opening) (fuel+1) z coins;return r.charge 70165 0);return a.charge 1 0)=_
  simp only [execute,opcode,t0,a0,↓reduceIte,pure_bind];rfl
end CommitGolfCandidate.Trunc.Wire
