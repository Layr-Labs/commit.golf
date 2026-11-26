import CommitGolfCandidate.ReconstructedCommitParentsLine

namespace CommitGolfCandidate.Reconstruction.CommitParents
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CommitExact
open Image (Atom)

def headOps (i : Nat) : List Atom := Image.shifts i ++ [.source ⟨i%64,by omega⟩]
def outOps (i : Nat) : List Atom := [.dest ⟨i%128,by omega⟩]

def srcReg (s : MachineState) (i : Nat) :=
  if i≠0 ∧ i%64=0 then s.getReg .x18+s.getReg .x22 else s.getReg .x18

def dstReg (s : MachineState) (i : Nat) :=
  if i≠0 ∧ i%128=0 then s.getReg .x19+s.getReg .x22 else s.getReg .x19

theorem head_ready (s : MachineState) (i : Nat) : ready s (headOps i) := by
  unfold headOps Image.shifts
  split_ifs <;> simp [ready,memoryArgumentsValid,memAccess,Image.Atom.op]

theorem out_ready (s : MachineState) (i : Nat) : ready s (outOps i) := by
  simp [outOps,ready,memoryArgumentsValid,memAccess,Image.Atom.op]

theorem head_regs (s : MachineState) (i : Nat) :
    let t := runPlain s (headOps i)
    t.mem=s.mem ∧ t.getReg .x10 = srcReg s i + signExtend12 (Image.sourceImm ⟨i%64,by omega⟩) ∧
    t.getReg .x18 = srcReg s i ∧ t.getReg .x19=dstReg s i ∧
    ∀ r, r ≠ .x10 → r ≠ .x18 → r ≠ .x19 → t.getReg r=s.getReg r := by
  unfold headOps Image.shifts srcReg dstReg
  split_ifs <;>
    simp [Image.Atom.op,runPlain,execInstrBr,MachineState.setPC,MachineState.setReg,MachineState.getReg] <;> intro r a b c <;> simp [a,b,c]

theorem out_regs (s : MachineState) (i : Nat) :
    let t := runPlain s (outOps i)
    t.mem=s.mem ∧ t.getReg .x12 = s.getReg .x19 + signExtend12 (Image.destImm ⟨i%128,by omega⟩) ∧
    ∀ r, r ≠ .x12 → t.getReg r = s.getReg r := by
  simp [outOps,Image.Atom.op,runPlain,execInstrBr,MachineState.setPC,MachineState.setReg,MachineState.getReg]
  intro r h
  simp [h]

theorem source_disp : ∀ i : Fin 64, signExtend12 (Image.sourceImm i) = BitVec.ofNat 64 (64*i.val)-2048 := by decide
theorem dest_disp : ∀ i : Fin 128, signExtend12 (Image.destImm i) = BitVec.ofNat 64 (32*i.val)-2048 := by decide

theorem centre_add (a n : Nat) (large : n ≤ a+2048) :
    BitVec.ofNat 64 (a+2048-n) + (BitVec.ofNat 64 n - 2048) = BitVec.ofNat 64 a := by
  have eq : BitVec.ofNat 64 (a+2048-n) + BitVec.ofNat 64 n = BitVec.ofNat 64 a + 2048 := by
    rw [←BitVec.ofNat_add,Nat.sub_add_cancel large,BitVec.ofNat_add];rfl
  bv_omega

end CommitGolfCandidate.Reconstruction.CommitParents
