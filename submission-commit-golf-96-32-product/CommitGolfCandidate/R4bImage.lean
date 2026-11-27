import CommitGolfCandidate.R4bSchedule
import CommitGolfCandidate.S4OpenEntry
set_option Elab.async false
namespace CommitGolfCandidate.R4b
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open CommitGolfCandidate.S4
open Machine (W Code)
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000
def scan (pc : Nat) : List Instr→Bool
  | []=>true
  | i::rest=>Machine.stands .opening pc i && scan (pc+1) rest
private theorem scanAppend (p : Nat) (xs ys : List Instr) (a : scan p xs) (b : scan (p+xs.length) ys) : scan p (xs++ys) := by
  induction xs generalizing p with
  | nil=>simpa using b
  | cons i xs ih=>
    obtain ⟨first,last⟩:=Bool.and_eq_true_iff.mp a
    apply Bool.and_eq_true_iff.mpr;refine ⟨first,ih (p+1) last ?_⟩
    rwa [show p+1+xs.length=p+(i::xs).length by simp;omega]
private theorem scanSound (p : Nat) (xs : List Instr) (h : scan p xs) : Machine.Matches .opening p xs := by
  induction xs generalizing p with
  | nil=>intro j hj;cases hj
  | cons i xs ih=>
    obtain ⟨a,b⟩:=Bool.and_eq_true_iff.mp h
    intro j hj;cases j with
    | zero=>exact Machine.stood a
    | succ j=>
      have e:=ih (p+1) b j (by simpa using hj)
      exact (show p+1+j=p+(j+1) by omega) ▸ e
private theorem row0 : scan 16401 (rowCode 0) ∧ (rowCode 0).length=320 := by decide +kernel
private theorem row1 : scan 16721 (rowCode 1) ∧ (rowCode 1).length=377 := by decide +kernel
private theorem row2 : scan 17098 (rowCode 2) ∧ (rowCode 2).length=377 := by decide +kernel
private theorem row3 : scan 17475 (rowCode 3) ∧ (rowCode 3).length=375 := by decide +kernel
theorem tileShape : tileCode.length=1449 ∧ clocks tileCode=1521 ∧ Machine.Matches .opening 16401 tileCode := by
  refine ⟨by decide +kernel,by decide +kernel,scanSound _ _ ?_⟩
  change scan 16401 (rowCode 0 ++ (rowCode 1 ++ (rowCode 2 ++ (rowCode 3 ++ []))))
  apply scanAppend _ _ _ row0.1;rw [row0.2]
  apply scanAppend _ _ _ row1.1;rw [row1.2]
  apply scanAppend _ _ _ row2.1;rw [row2.2]
  simpa using row3.1

def initOps : List Machine.Sym.Calc := [
  .addi .x1 .x0 7,
  .slli .x1 .x1 11,
  .addi .x1 .x1 2047,
  .slli .x1 .x1 11,
  .addi .x1 .x1 2039,
  .slli .x1 .x1 11,
  .addi .x1 .x1 2000,
  .addi .x2 .x0 7,
  .slli .x2 .x2 11,
  .addi .x2 .x2 2047,
  .slli .x2 .x2 11,
  .addi .x2 .x2 2043,
  .slli .x2 .x2 11,
  .addi .x2 .x2 2000,
  .addi .x16 .x0 7,
  .slli .x16 .x16 11,
  .addi .x16 .x16 2047,
  .slli .x16 .x16 11,
  .addi .x16 .x16 2047,
  .slli .x16 .x16 11,
  .addi .x16 .x16 2000,
  .addi .x11 .x0 3,
  .slli .x11 .x11 11,
  .addi .x11 .x11 0,
  .addi .x3 .x0 1408,
  .slli .x3 .x3 11,
  .addi .x3 .x3 2,
  .slli .x3 .x3 11,
  .addi .x3 .x3 104,
  .addi .x4 .x0 1024,
  .slli .x4 .x4 11,
  .addi .x4 .x4 2,
  .slli .x4 .x4 11,
  .addi .x4 .x4 32,
  .addi .x5 .x0 184,
  .addi .x10 .x0 96,
  .addi .x9 .x0 32]
def setupValue : Reg→Machine.Sym.Expr
  | .x0=>.lit 0
  | .x1=>.lit (W tableBase) | .x2=>.lit (W (tableBase+8192))
  | .x3=>.lit (W (Late.rowBase+72)) | .x4=>.lit (W Open.tdBase) | .x5=>.lit (W 184)
  | .x10=>.lit (W 96) | .x11=>.lit (W 6144) | .x16=>.lit (W (tableBase+16384))
  | .x9=>.lit (W 32) | r=>.reg r

theorem initRegs (r : Reg) : (initOps.foldl Machine.Sym.bump Machine.Sym.original) r=setupValue r := by
  cases r <;> decide +kernel
theorem initValid : (Machine.Fragment.arithmetic initOps).valid .opening 16364 16401 ∧
    initOps.all (fun i=>i.dst != .x0) ∧ Machine.Sym.requirements Machine.Sym.original initOps=[] ∧
    initOps.length=37 ∧ Machine.Sym.price initOps=37 := by decide +kernel
end CommitGolfCandidate.R4b
