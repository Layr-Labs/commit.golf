import CommitGolfCandidate.TruncBPrepare
namespace CommitGolfCandidate.Trunc.Batch
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 6000
set_option maxHeartbeats 150000
attribute [local irreducible] marksState Runs

private theorem extendNonzero (b : Byte) (h : b≠0) : b.zeroExtend 64 ≠ 0#64 := by
  intro e;apply h;have hh:=congrArg (fun w : Word => w.truncate 8) e;simpa using hh

theorem arrive00 (o : Oracle) (s : MachineState) (p : Fin 128) (a : Args p s)
    (pc : s.pc=5316) (left : flagL s p = 0) (right : flagR s p = 0) :
    ∃ t,Runs o s t 4 0 ∧ SameData s t ∧ t.pc=5436 := by
  obtain ⟨run,keep,bpc,l,r⟩ := loadFlags o s p a pc
  let t0:=marksState s
  have lf : t0.getReg .x6 = 0#64 := by rw [show t0.getReg .x6=_ from l];rw [left] <;> rfl
  have rf : t0.getReg .x7 = 0#64 := by rw [show t0.getReg .x7=_ from r];rw [right] <;> rfl
  let t1:=t0.setPC 5372
  have h1 := branch307Yes o t0 bpc lf
  let t2:=t1.setPC 5436
  have h2 := branch319Yes o t1 rfl rf
  exact ⟨t2,(runs_trans (runs_trans run h1) h2),((keep.atPC 5372).atPC 5436),rfl⟩

theorem arrive01 (o : Oracle) (s : MachineState) (p : Fin 128) (a : Args p s)
    (pc : s.pc=5316) (left : flagL s p = 0) (right : flagR s p ≠ 0) :
    ∃ t,Runs o s t 4 0 ∧ SameData s t ∧ t.pc=5376 := by
  obtain ⟨run,keep,bpc,l,r⟩ := loadFlags o s p a pc
  let t0:=marksState s
  have lf : t0.getReg .x6 = 0#64 := by rw [show t0.getReg .x6=_ from l];rw [left] <;> rfl
  have rf : t0.getReg .x7 ≠ 0#64 := by rw [show t0.getReg .x7=_ from r];exact extendNonzero _ right
  let t1:=t0.setPC 5372
  have h1 := branch307Yes o t0 bpc lf
  let t2:=t1.setPC 5376
  have h2 := branch319No o t1 rfl rf
  exact ⟨t2,(runs_trans (runs_trans run h1) h2),((keep.atPC 5372).atPC 5376),rfl⟩

theorem arrive10 (o : Oracle) (s : MachineState) (p : Fin 128) (a : Args p s)
    (pc : s.pc=5316) (left : flagL s p ≠ 0) (right : flagR s p = 0) :
    ∃ t,Runs o s t 4 0 ∧ SameData s t ∧ t.pc=5336 := by
  obtain ⟨run,keep,bpc,l,r⟩ := loadFlags o s p a pc
  let t0:=marksState s
  have lf : t0.getReg .x6 ≠ 0#64 := by rw [show t0.getReg .x6=_ from l];exact extendNonzero _ left
  have rf : t0.getReg .x7 = 0#64 := by rw [show t0.getReg .x7=_ from r];rw [right] <;> rfl
  let t1:=t0.setPC 5328
  have h1 := branch307No o t0 bpc lf
  let t2:=t1.setPC 5336
  have h2 := branch308Yes o t1 rfl rf
  exact ⟨t2,(runs_trans (runs_trans run h1) h2),((keep.atPC 5328).atPC 5336),rfl⟩

theorem arrive11 (o : Oracle) (s : MachineState) (p : Fin 128) (a : Args p s)
    (pc : s.pc=5316) (left : flagL s p ≠ 0) (right : flagR s p ≠ 0) :
    ∃ t,Runs o s t 5 0 ∧ SameData s t ∧ t.pc=5408 := by
  obtain ⟨run,keep,bpc,l,r⟩ := loadFlags o s p a pc
  let t0:=marksState s
  have lf : t0.getReg .x6 ≠ 0#64 := by rw [show t0.getReg .x6=_ from l];exact extendNonzero _ left
  have rf : t0.getReg .x7 ≠ 0#64 := by rw [show t0.getReg .x7=_ from r];exact extendNonzero _ right
  let t1:=t0.setPC 5328
  have h1 := branch307No o t0 bpc lf
  let t2:=t1.setPC 5332
  have h2 := branch308No o t1 rfl rf
  let t3:=t2.setPC 5408
  have h3 := jump309 o t2 rfl
  exact ⟨t3,(runs_trans (runs_trans (runs_trans run h1) h2) h3),(((keep.atPC 5328).atPC 5332).atPC 5408),rfl⟩
end CommitGolfCandidate.Trunc.Batch
