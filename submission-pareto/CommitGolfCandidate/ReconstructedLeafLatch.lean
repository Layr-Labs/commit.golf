import CommitGolfCandidate.ReconstructedLeafRun

namespace CommitGolfCandidate.Reconstruction.LeafLatch
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 TwoPermutationPrototype.RV64
open LeafModel LeafMacros CommitWindows LeafContent LeafPrelude Generator LeafLane CommitBlocks CommitSetup

def latchCode : List Instr := [.ADDI .x19 .x19 32,.ADDI .x20 .x20 4095]
def left (i : Index) := 4095-(tileOf i).val
def nextModel (m : Model) (i : Index) := (m.set .x19 (wordAddress (center i+4))).set .x20 (BitVec.ofNat 64 (left i))

theorem next_mem (m : Model) (i : Index) : (nextModel m i).mem=m.mem := rfl
theorem next_reg (m : Model) (i : Index) (r : Reg) (a : r≠.x19) (b : r≠.x20) :
    (nextModel m i).reg r = m.reg r := by simp only [nextModel,Model.set,Ne.symm a,Ne.symm b,false_and,ite_false]

private theorem ops (o : Oracle) (m : Model) (i : Index) (anchor : m.reg .x19 = wordAddress (center i))
    (n : m.reg .x20 = BitVec.ofNat 64 (4096-(tileOf i).val)) : Contract o latchCode m (nextModel m i) := by
  let a := m.set .x19 (wordAddress (center i+4))
  have s1 : Contract o [.ADDI .x19 .x19 32] m a := LeafModel.addi _ _ _ _ _ _ (by rw [anchor]; exact plus _ 4 _ rfl)
  have count : 4096-(tileOf i).val = left i+1 := by have := (tileOf i).isLt; unfold left; omega
  have s2 : Contract o [.ADDI .x20 .x20 4095] a (nextModel m i) := LeafModel.addi _ _ _ _ _ _ (by
    change m.reg .x20 + 0xffffffffffffffff#64 = _
    rw [n,count,BitVec.ofNat_add,BitVec.add_assoc]
    exact BitVec.add_zero _)
  exact LeafModel.combine s1 s2

private theorem branch (o : Oracle) (s : MachineState) (pc : s.pc = addr 53014) (v : Word)
    (count : s.getReg .x20 = v) :
    CommitExact.Segment o im 1 s (s.setPC (if v=0 then addr 53016 else addr 53015)) := by
  apply CommitExact.plain o im _ _ (.base (.BEQ .x20 .x0 8)) (fetch_at 53014 _ rfl s pc)
  change some (if s.getReg .x20 == s.getReg .x0 then s.setPC (s.pc+signExtend13 8) else s.setPC (s.pc+4)) = _
  rw [count,show s.getReg .x0=0 from rfl,pc]
  by_cases z : v=0
  · rw [z]; rfl
  · have nz : (v == 0) = false := beq_eq_false_iff_ne.mpr z
    rw [nz,if_neg z]
    rfl

private theorem jump (o : Oracle) (s : MachineState) (pc : s.pc = addr 53015) :
    CommitExact.Segment o im 1 s (s.setPC (addr 19)) := by
  apply CommitExact.plain o im _ _ (.base (.JAL .x0 1885168)) (fetch_at 53015 _ rfl s pc)
  change some (s.setPC (s.pc+signExtend21 1885168)) = _
  rw [pc]; rfl

/-- At the final leaf of each tile the fixed loop latch advances the heap anchor.
The branch on its last iteration enters the parent program. -/
theorem run (o : Oracle) (m : Model) (i : Index) (s : MachineState) (pc : s.pc=addr 53012)
    (fits : Fits s m) (anchor : m.reg .x19=wordAddress (center i))
    (count : m.reg .x20=BitVec.ofNat 64 (4096-(tileOf i).val)) :
    ∃ t, CommitExact.Segment o im (if left i=0 then 3 else 4) s t ∧ Fits t (nextModel m i) ∧
      t.pc= (if left i=0 then addr 53016 else addr 19) := by
  obtain ⟨t,trace,ht⟩ := ops o m i anchor count s fits
  have seg := trace.segment 53012 pc (by decide +kernel)
  change CommitExact.Segment o im 2 s t at seg
  have loc : t.pc=addr 53014 := trace.next_pc _ pc
  let v := BitVec.ofNat 64 (left i)
  have actual : t.getReg .x20=v := ht.registers _
  have br := branch o t loc v actual
  have zero : v=0 ↔ left i=0 := by
    have small : left i<2^64 := by unfold left; omega
    constructor
    · intro h; have w := congrArg BitVec.toNat h
      change left i%2^64=0 at w; rwa [Nat.mod_eq_of_lt small] at w
    · intro h; change BitVec.ofNat 64 (left i)=0; rw [h]; rfl
  by_cases z : left i=0
  · rw [if_pos (zero.mpr z)] at br
    exact ⟨_,by simpa only [z,ite_true] using CommitExact.compose seg br,ht.pc _,by simp [z,MachineState.setPC]⟩
  · rw [if_neg (mt zero.mp z)] at br
    have j := jump o (t.setPC (addr 53015)) rfl
    exact ⟨_,by simpa only [z,ite_false] using CommitExact.compose (CommitExact.compose seg br) j,
      (ht.pc _).pc _,by simp [z,MachineState.setPC]⟩

end CommitGolfCandidate.Reconstruction.LeafLatch
