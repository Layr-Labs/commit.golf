import CommitGolfCandidate.S4Mask238
namespace CommitGolfCandidate.Trunc
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

/-- Two writes to the same scratch register leave the last value. -/
theorem overwrite6 (s : MachineState) (old new : Word) : (s.setReg .x6 old).setReg .x6 new=s.setReg .x6 new := by
  cases s
  simp only [MachineState.setReg,MachineState.mk.injEq,and_true,true_and]
  funext r;by_cases e:r=Reg.x6 <;> simp [e]
theorem overwrite10 (s : MachineState) (old new : Word) : (s.setReg .x10 old).setReg .x10 new=s.setReg .x10 new := by
  cases s
  simp only [MachineState.setReg,MachineState.mk.injEq,and_true,true_and]
  funext r;by_cases e:r=Reg.x10 <;> simp [e]

theorem loadShiftMask (z : BitVec 16) :
    ((z.zeroExtend 64 <<< 50) >>> 50)=z.zeroExtend 64 &&& 16383 := by
  apply BitVec.eq_of_getLsbD_eq;intro i h;interval_cases i <;> simp (config:={decide:=true})
theorem storeAfter6 (s : MachineState) (addr pc : Word) (z : BitVec 32) :
    let l:=execInstrBr s (.LHU .x6 .x12 28)
    let t:=execInstrBr l (.AND .x6 .x6 .x28)
    (t.setWord32 addr z).setPC pc = ((s.setWord32 addr z).setReg .x6 (t.getReg .x6)).setPC pc := by
  dsimp only
  let a:=(s.getHalfword (s.getReg .x12+signExtend12 28)).zeroExtend 64
  let b:=a &&& s.getReg .x28
  change ((((s.setReg .x6 a).setReg .x6 b).setWord32 addr z).setPC pc)=_
  rw [overwrite6]
  rfl
end CommitGolfCandidate.Trunc
