import CommitGolfCandidate.ReconstructedCapLoad

namespace CommitGolfCandidate.Reconstruction.CapWordStep
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel LeafSteps TwoPermutationPrototype.RV64 OpeningCursor
open CommitBlocks (addr)
set_option maxRecDepth 12000
attribute [local irreducible] ArtifactEncoding.decode execute

def imm (a : Word) (i : BitVec 12) : Word := (a.truncate 32+(signExtend12 i).truncate 32).signExtend 64

theorem addiw (o : Oracle) (m : Model) (s : MachineState) (fit : Fits s m)
    (pc : Nat) (pos : s.pc=addr pc) (small : pc<1660) (rd rs : Reg) (i : BitVec 12)
    (atCode : OpeningStraight.actualAt pc=some (.base (.ADDIW rd rs i))) :
    ∃ t, CommitExact.Segment o OpeningStraight.image 1 s t ∧ t.pc=addr (pc+1) ∧ Fits t (m.set rd (imm (m.reg rs) i)) := by
  let t := (s.setReg rd (imm (m.reg rs) i)).setPC (s.pc+4)
  have op : ordinaryStep s (.base (.ADDIW rd rs i))=some t := by
    change some ((s.setReg rd _).setPC (s.pc+4))=_
    rw [fit.registers];rfl
  exact ⟨_,CommitExact.plain o _ _ _ _ (OpeningStraight.fetched pc _ small atCode s pos) op,
    by change s.pc+4=_;rw [pos];exact (CommitBlocks.addr_next pc).symm,(fit.reg rd _).pc _⟩

theorem jump (o : Oracle) (s : MachineState) (i j : Nat) (imm : BitVec 21) (loc : s.pc=addr i) (bound : i<1660)
    (listed : OpeningStraight.actualAt i=some (.base (.JAL .x0 imm))) (dest : addr i+signExtend21 imm=addr j) :
    CommitExact.Segment o OpeningStraight.image 1 s (s.setPC (addr j)) := by
  apply CommitExact.plain o _ _ _ _ (OpeningStraight.fetched i _ bound listed s loc)
  change some (s.setPC (s.pc+signExtend21 imm))=_
  exact congrArg (fun v => some (s.setPC v)) ((congrArg (·+signExtend21 imm) loc).trans dest)

theorem bne (o : Oracle) (s : MachineState) (i j : Nat) (r : Reg) (imm : BitVec 13)
    (loc : s.pc=addr i) (bound : i<1660) (listed : OpeningStraight.actualAt i=some (.base (.BNE r .x0 imm)))
    (dest : addr i+signExtend13 imm=addr j) (v : Word) (value : s.getReg r=v) :
    CommitExact.Segment o OpeningStraight.image 1 s (s.setPC (if v=0 then addr (i+1) else addr j)) := by
  apply CommitExact.plain o _ _ _ _ (OpeningStraight.fetched i _ bound listed s loc)
  change some (if !(s.getReg r==s.getReg .x0) then s.setPC (s.pc+signExtend13 imm) else s.setPC (s.pc+4))=_
  rw [value,show s.getReg .x0=0 from rfl,loc,dest,←CommitBlocks.addr_next i]
  by_cases z : v=0
  · rw [z];rfl
  · rw [beq_eq_false_iff_ne.mpr z,ite_eq_right z];rfl

end CommitGolfCandidate.Reconstruction.CapWordStep
