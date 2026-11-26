import CommitGolfCandidate.ReconstructedOpeningReply
import CommitGolfCandidate.ReconstructedOpeningStraight

namespace CommitGolfCandidate.Reconstruction.OpeningLane
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel LeafSteps Generator CommitWindows
open TwoPermutationPrototype.RV64 OpeningOps OpeningIndex OpeningQuery OpeningReply LeafContent
open CommitBlocks (addr)
open OpeningStraight (image Listed)
set_option maxHeartbeats 1200000
set_option maxRecDepth 12000
attribute [local irreducible] ArtifactEncoding.decode Riscv.execute atQuery HonestInputs.first

def beforeOps : List Op := [
  .reg .x10 (.srli .x16 19),.reg .x11 (.slli .x10 4),.reg .x10 (.slli .x10 2),
  .reg .x10 (.subw .x10 .x11),.reg .x10 (.add .x14 .x10),.reg .x11 (.slli .x10 48)]

private theorem before_table : Listed 185 (beforeOps.map Op.instr) := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩

def zeroOps : List Op := [.reg .x11 (.addi .x0 23)]
def nonzeroOps : List Op := [
  .reg .x10 (.slli .x10 49),.reg .x10 (.srli .x10 48),.reg .x11 (.addi .x10 4094)]
def loadOps (l : Fin 12) : List Op := [
  .reg .x10 (.slli .x11 32),.reg .x10 (.srli .x10 29),.reg .x10 (.add .x6 .x10),
  .ld .x12 .x10 0 (replyBase+(LeafNonce.firstWord l).val)]

private theorem zero_table : Listed 192 (zeroOps.map Op.instr) := ⟨rfl,True.intro⟩
private theorem nonzero_table : Listed 194 (nonzeroOps.map Op.instr) := ⟨rfl,rfl,rfl,True.intro⟩
private theorem load_table (l : Fin 12) : Listed 197 ((loadOps l).map Op.instr) := ⟨rfl,rfl,rfl,rfl,True.intro⟩

/-- The reciprocal-based computation in words 185–190 produces the exact lane. -/
theorem before (m : Model) (i : Index) (p : m.reg .x16=highProduct (slot i))
    (s : m.reg .x14=word (slot i)) :
    let t := after m beforeOps
    t.reg .x10=BitVec.ofNat 64 (laneOf i).val ∧ t.reg .x11=BitVec.ofNat 64 (laneOf i).val <<< 48 ∧
      t.mem=m.mem ∧ (∀ r, r≠.x10 → r≠.x11 → t.reg r=m.reg r) := by
  let a := m.reg .x16 >>> 19
  have calcLane : m.reg .x14 + (((a <<< 2).truncate 32 - (a <<< 4).truncate 32).signExtend 64) =
      BitVec.ofNat 64 (laneOf i).val := by
    dsimp only [a];rw [p,s];exact lane_value i
  have first : (after m beforeOps).reg .x10 = BitVec.ofNat 64 (laneOf i).val := calcLane
  refine ⟨first,?_,rfl,?_⟩
  · change (after m beforeOps).reg .x10 <<< (48 : Nat) = _
    rw [first]
  · intro r x y
    simp [after,beforeOps,Op.apply,Model.set,x.symm,y.symm]

private theorem guard (o : Oracle) (s : MachineState) (pc : s.pc=addr 191) (l : Fin 12)
    (r : s.getReg .x11 = BitVec.ofNat 64 l.val <<< 48) :
    CommitExact.Segment o image 1 s (s.setPC (if l.val=0 then addr 192 else addr 194)) := by
  have f := OpeningStraight.fetched 191 (.base (.BNE .x11 .x0 12)) (by decide) rfl s pc
  apply CommitExact.plain o image _ _ _ f
  change some (if s.getReg .x11 != s.getReg .x0 then s.setPC (s.pc+signExtend13 12) else s.setPC (s.pc+4)) = _
  rw [r,pc,show s.getReg .x0=0 from rfl]
  fin_cases l <;> rfl

private theorem jump (o : Oracle) (s : MachineState) (pc : s.pc=addr 193) :
    CommitExact.Segment o image 1 s (s.setPC (addr 197)) := by
  apply CommitExact.plain o image _ _ (.base (.JAL .x0 16)) (OpeningStraight.fetched _ _ (by decide) rfl s pc)
  change some (s.setPC (s.pc+signExtend21 16))=_
  rw [pc];rfl

private theorem lane_case (m : Model) (l : Fin 12) (zero : m.reg .x0=0)
    (atLane : m.reg .x10=BitVec.ofNat 64 l.val) :
    let t := if l.val=0 then after m zeroOps else after m nonzeroOps
    t.reg .x11=BitVec.ofNat 64 (LeafNonce.firstWord l).val ∧ t.mem=m.mem ∧
      (∀ r, r≠.x10 → r≠.x11 → t.reg r=m.reg r) := by
  by_cases z : l.val=0
  · rw [ite_eq_left z]
    refine ⟨?_,rfl,?_⟩
    · change m.reg .x0+23=_
      rw [zero];simp [LeafNonce.firstWord,z]
    · intro r _ y;simp [after,zeroOps,Op.apply,Model.set,y.symm]
  · rw [ite_eq_right z]
    refine ⟨?_,rfl,?_⟩
    · change ((m.reg .x10 <<< 49) >>> 48)+signExtend12 4094=_
      rw [atLane];fin_cases l <;> first | contradiction | rfl
    · intro r x y;simp [after,nonzeroOps,Op.apply,Model.set,x.symm,y.symm]

private theorem cases_run (o : Oracle) (m : Model) (l : Fin 12)
    (s : MachineState) (pc : s.pc=addr 191) (h : Fits s m) (b : m.reg .x11=BitVec.ofNat 64 l.val <<< 48) :
    ∃ t, CommitExact.Segment o image (if l.val=0 then 3 else 4) s t ∧ t.pc=addr 197 ∧
      Fits t (if l.val=0 then after m zeroOps else after m nonzeroOps) := by
  have g := guard o s pc l ((h.registers .x11).trans b)
  by_cases z : l.val=0
  · rw [ite_eq_left z] at g ⊢
    rw [ite_eq_left z]
    obtain ⟨t,r,p,f⟩ := OpeningStraight.block o m zeroOps 192 (by decide) zero_table
      (by simp [zeroOps,Checked,Op.Valid]) (s.setPC _) rfl (h.pc _)
    exact ⟨_,CommitExact.compose (CommitExact.compose g r) (jump o t p),rfl,f.pc _⟩
  · rw [ite_eq_right z] at g ⊢
    rw [ite_eq_right z]
    obtain ⟨t,r,p,f⟩ := OpeningStraight.block o m nonzeroOps 194 (by decide) nonzero_table
      (by simp [nonzeroOps,Checked,Op.Valid]) (s.setPC _) rfl (h.pc _)
    exact ⟨t,CommitExact.compose g r,p,f⟩

private theorem load_address (m : Model) (l : Fin 12) (base : m.reg .x6=wordAddress replyBase)
    (off : m.reg .x11=BitVec.ofNat 64 (LeafNonce.firstWord l).val) :
    Checked m (loadOps l) := by
  have small := (LeafNonce.firstWord l).isLt
  have room : replyBase+(LeafNonce.firstWord l).val < 2^33 := by unfold replyBase;omega
  simp only [loadOps,Checked,Op.Valid,true_and,and_true,Op.apply,Expr.eval]
  refine ⟨room,?_⟩
  change m.reg .x6+((m.reg .x11 <<< 32) >>> 29)+signExtend12 0=_
  rw [base,off];fin_cases l <;> rfl

structure Loaded (m t : Model) (l : Fin 12) : Prop where
  low : t.reg .x12=m.mem (replyBase+(LeafNonce.firstWord l).val)
  offset : t.reg .x11=BitVec.ofNat 64 (LeafNonce.firstWord l).val
  memory : t.mem=m.mem
  frame : ∀ r, r≠.x10 → r≠.x11 → r≠.x12 → t.reg r=m.reg r

/-- On either side of the wraparound branch, select the correct first salt word
from the actual 25-word oracle reply without changing RAM. -/
theorem select (o : Oracle) (m : Model) (i : Index) (s : MachineState) (pc : s.pc=addr 185)
    (h : Fits s m) (zero : m.reg .x0=0) (base : m.reg .x6=wordAddress replyBase)
    (p : m.reg .x16=highProduct (slot i)) (slotReg : m.reg .x14=word (slot i)) :
    ∃ t n, CommitExact.Segment o image (6+(if (laneOf i).val=0 then 3 else 4)+4) s t ∧
      t.pc=addr 201 ∧ Fits t n ∧ Loaded m n (laneOf i) := by
  let l := laneOf i
  let a := after m beforeOps
  let b := if l.val=0 then after a zeroOps else after a nonzeroOps
  obtain ⟨u,ru,pu,hu⟩ := OpeningStraight.block o m beforeOps 185 (by decide) before_table
    (by simp [beforeOps,Checked,Op.Valid]) s pc h
  obtain ⟨al,ax,am,ar⟩ := before m i p slotReg
  obtain ⟨v,rv,pv,hv⟩ := cases_run o a l u pu hu ax
  obtain ⟨bv,bm,br⟩ := lane_case a l ((ar _ (by decide) (by decide)).trans zero) al
  have bb : b.reg .x6=wordAddress replyBase :=
    (br _ (by decide) (by decide)).trans ((ar _ (by decide) (by decide)).trans base)
  obtain ⟨t,rt,pt,ht⟩ := OpeningStraight.block o b (loadOps l) 197 (by change 197+4≤1660;decide)
    (load_table l) (load_address b l bb bv) v pv hv
  refine ⟨t,after b (loadOps l),CommitExact.compose (CommitExact.compose ru rv) rt,pt,ht,?_,?_,?_,?_⟩
  · change b.mem _=m.mem _
    rw [show b.mem=a.mem from bm,show a.mem=m.mem from am]
  · exact bv
  · exact bm.trans am
  · intro r x y z
    have same : (after b (loadOps l)).reg r=b.reg r := by simp [after,loadOps,Op.apply,Model.set,x.symm,z.symm]
    exact same.trans ((br _ x y).trans (ar _ x y))

end CommitGolfCandidate.Reconstruction.OpeningLane
