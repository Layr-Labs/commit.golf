import CommitGolfCandidate.PairPrepare
namespace CommitGolfCandidate.PairCap.Batch
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 6000
set_option maxHeartbeats 150000
attribute [local irreducible] marksState Runs

private theorem extendNonzero (b : Byte) (h : b≠0) : b.zeroExtend 64 ≠ 0#64 := by
  intro e;apply h;have hh:=congrArg (fun w : Word => w.truncate 8) e;simpa using hh

theorem arrive00 (o : Oracle) (s : MachineState) (p : Fin 128) (a : Args p s)
    (pc : s.pc=6892) (left : flagL s p = 0) (right : flagR s p = 0) :
    ∃ t,Runs o s t 4 0 ∧ SameData s t ∧ t.pc=7200 := by
  obtain ⟨run,keep,bpc,l,r⟩ := loadFlags o s p a pc
  let t0:=marksState s
  have lf : t0.getReg .x6 = 0#64 := by rw [show t0.getReg .x6=_ from l];rw [left] <;> rfl
  have rf : t0.getReg .x7 = 0#64 := by rw [show t0.getReg .x7=_ from r];rw [right] <;> rfl
  let t1:=t0.setPC 7040
  have h1 := ckb2b701Yes o t0 bpc lf
  let t2:=t1.setPC 7200
  have h2 := ckb2b736Yes o t1 rfl rf
  exact ⟨t2,(runs_trans (runs_trans run h1) h2),((keep.atPC 7040).atPC 7200),rfl⟩

theorem arrive01 (o : Oracle) (s : MachineState) (p : Fin 128) (a : Args p s)
    (pc : s.pc=6892) (left : flagL s p = 0) (right : flagR s p ≠ 0) :
    ∃ t,Runs o s t 4 0 ∧ SameData s t ∧ t.pc=7044 := by
  obtain ⟨run,keep,bpc,l,r⟩ := loadFlags o s p a pc
  let t0:=marksState s
  have lf : t0.getReg .x6 = 0#64 := by rw [show t0.getReg .x6=_ from l];rw [left] <;> rfl
  have rf : t0.getReg .x7 ≠ 0#64 := by rw [show t0.getReg .x7=_ from r];exact extendNonzero _ right
  let t1:=t0.setPC 7040
  have h1 := ckb2b701Yes o t0 bpc lf
  let t2:=t1.setPC 7044
  have h2 := ckb2b736No o t1 rfl rf
  exact ⟨t2,(runs_trans (runs_trans run h1) h2),((keep.atPC 7040).atPC 7044),rfl⟩

theorem arrive10 (o : Oracle) (s : MachineState) (p : Fin 128) (a : Args p s)
    (pc : s.pc=6892) (left : flagL s p ≠ 0) (right : flagR s p = 0) :
    ∃ t,Runs o s t 4 0 ∧ SameData s t ∧ t.pc=6912 := by
  obtain ⟨run,keep,bpc,l,r⟩ := loadFlags o s p a pc
  let t0:=marksState s
  have lf : t0.getReg .x6 ≠ 0#64 := by rw [show t0.getReg .x6=_ from l];exact extendNonzero _ left
  have rf : t0.getReg .x7 = 0#64 := by rw [show t0.getReg .x7=_ from r];rw [right] <;> rfl
  let t1:=t0.setPC 6904
  have h1 := ckb2b701No o t0 bpc lf
  let t2:=t1.setPC 6912
  have h2 := ckb2b702Yes o t1 rfl rf
  exact ⟨t2,(runs_trans (runs_trans run h1) h2),((keep.atPC 6904).atPC 6912),rfl⟩

theorem arrive11 (o : Oracle) (s : MachineState) (p : Fin 128) (a : Args p s)
    (pc : s.pc=6892) (left : flagL s p ≠ 0) (right : flagR s p ≠ 0) :
    ∃ t,Runs o s t 5 0 ∧ SameData s t ∧ t.pc=7168 := by
  obtain ⟨run,keep,bpc,l,r⟩ := loadFlags o s p a pc
  let t0:=marksState s
  have lf : t0.getReg .x6 ≠ 0#64 := by rw [show t0.getReg .x6=_ from l];exact extendNonzero _ left
  have rf : t0.getReg .x7 ≠ 0#64 := by rw [show t0.getReg .x7=_ from r];exact extendNonzero _ right
  let t1:=t0.setPC 6904
  have h1 := ckb2b701No o t0 bpc lf
  let t2:=t1.setPC 6908
  have h2 := ckb2b702No o t1 rfl rf
  let t3:=t2.setPC 7168
  have h3 := ckb2j703 o t2 rfl
  exact ⟨t3,(runs_trans (runs_trans (runs_trans run h1) h2) h3),(((keep.atPC 6904).atPC 6908).atPC 7168),rfl⟩
end CommitGolfCandidate.PairCap.Batch
