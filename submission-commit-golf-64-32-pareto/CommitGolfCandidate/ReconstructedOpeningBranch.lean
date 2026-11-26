import CommitGolfCandidate.ReconstructedOpeningCursor

namespace CommitGolfCandidate.Reconstruction.OpeningBranch
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OpeningCursor CommitBlocks

theorem word_zero (c : Nat) : W (c%64)=0 ↔ c%64=0 := by
  constructor
  · intro z;have n := congrArg BitVec.toNat z;change (c%64)%2^64=0 at n;omega
  · intro z;rw [z];rfl

theorem less (o : Oracle) (s : MachineState) (a b : Reg) (i dst : Nat) (imm : BitVec 13)
    (pc : s.pc=addr i) (bound : i<1660) (op : OpeningStraight.actualAt i=some (.base (.BLTU a b imm)))
    (target : addr i+signExtend13 imm=addr dst) (l r : Nat) (hl : l<2^64) (hr : r<2^64)
    (left : s.getReg a=W l) (right : s.getReg b=W r) :
    CommitExact.Segment o OpeningStraight.image 1 s (s.setPC (if l<r then addr dst else addr (i+1))) := by
  apply CommitExact.plain o _ _ _ _ (OpeningStraight.fetched _ _ bound op s pc)
  change some (if (s.getReg a).ult (s.getReg b) then s.setPC (s.pc+signExtend13 imm) else s.setPC (s.pc+4))=_
  rw [left,right,pc,target,←addr_next,BitVec.ult_eq_decide]
  simp only [W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hl,Nat.mod_eq_of_lt hr,decide_eq_true_eq]
  split <;> rfl

theorem nonzero (o : Oracle) (s : MachineState) (i fall dst : Nat) (a : Reg) (imm : BitVec 13)
    (pc : s.pc=addr i) (bound : i<1660) (entry : OpeningStraight.actualAt i=some (.base (.BNE a .x0 imm)))
    (next : addr i+4=addr fall) (target : addr i+signExtend13 imm=addr dst) (v : Word) (value : s.getReg a=v) :
    CommitExact.Segment o OpeningStraight.image 1 s (s.setPC (if v=0 then addr fall else addr dst)) := by
  apply CommitExact.plain o _ _ _ _ (OpeningStraight.fetched _ _ bound entry s pc)
  change some (if s.getReg a != s.getReg .x0 then s.setPC (s.pc+signExtend13 imm) else s.setPC (s.pc+4))=_
  rw [value,show s.getReg .x0=0 from rfl,pc,next,target]
  simp only [bne_iff_ne]
  by_cases z : v=0
  · rw [ite_eq_right (fun ne => ne z),ite_eq_left z]
  · rw [ite_eq_left z,ite_eq_right z]

theorem atLeast (o : Oracle) (s : MachineState) (a b : Reg) (i dst : Nat) (imm : BitVec 13)
    (pc : s.pc=addr i) (bound : i<1660) (op : OpeningStraight.actualAt i=some (.base (.BGEU a b imm)))
    (target : addr i+signExtend13 imm=addr dst) (l r : Nat) (hl : l<2^64) (hr : r<2^64)
    (left : s.getReg a=W l) (right : s.getReg b=W r) :
    CommitExact.Segment o OpeningStraight.image 1 s (s.setPC (if l<r then addr (i+1) else addr dst)) := by
  apply CommitExact.plain o _ _ _ _ (OpeningStraight.fetched _ _ bound op s pc)
  change some (if ¬(s.getReg a).ult (s.getReg b) then s.setPC (s.pc+signExtend13 imm) else s.setPC (s.pc+4))=_
  rw [left,right,pc,target,←addr_next,BitVec.ult_eq_decide]
  simp only [W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hl,Nat.mod_eq_of_lt hr,decide_eq_true_eq]
  by_cases h : l<r
  · rw [ite_eq_right (fun ne => ne h),ite_eq_left h]
  · rw [ite_eq_left h,ite_eq_right h]

theorem jump (o : Oracle) (s : MachineState) (i dst : Nat) (imm : BitVec 21) (pc : s.pc=addr i) (bound : i<1660)
    (op : OpeningStraight.actualAt i=some (.base (.JAL .x0 imm))) (target : addr i+signExtend21 imm=addr dst) :
    CommitExact.Segment o OpeningStraight.image 1 s (s.setPC (addr dst)) := by
  apply CommitExact.plain o _ _ _ _ (OpeningStraight.fetched _ _ bound op s pc)
  change some (s.setPC (s.pc+signExtend21 imm))=_
  rw [pc,target]

end CommitGolfCandidate.Reconstruction.OpeningBranch
