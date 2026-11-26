import CommitGolfCandidate.ReconstructedCapLowCore
import CommitGolfCandidate.ReconstructedCapLowMergedWords

namespace CommitGolfCandidate.Reconstruction.CapLowLast
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel OpeningOps OpeningQuery OpeningCursor OpeningPut CapLowCore
open TwoPermutationPrototype (writeWord)
open TwoPermutationPrototype.RV64
open CommitBlocks (addr)
set_option maxRecDepth 18000
set_option maxHeartbeats 1900000

def start (c : Nat) : List Op := [.reg .x12 (.add .x26 .x23),.sd .x16 .x14 0 (cell c)]
def spill (c : Nat) : List Op := [.reg .x12 (.subw .x0 .x26),.reg .x12 (.srl .x30 .x12),.sd .x16 .x12 8 (cell c+1)]
def bump : List Op := [.reg .x24 (.addi .x24 4),.reg .x7 (.add .x7 .x23)]
def saved (m : Model) (c w : Nat) := if c%64+w>64 then after (after m (start c)) (spill c) else after m (start c)
def result (m : Model) (c w : Nat) := after (saved m c w) bump

theorem startChecks (m : Model) (c : Nat) (room : cell c+1<2^33) (ptr : m.reg .x16=wordAddress (cell c)) : Checked m (start c) := by
  simp only [start,Checked,Op.Valid,Op.apply,true_and,and_true];exact ⟨by omega,ptr ▸ BitVec.add_zero _⟩

theorem spillChecks (m : Model) (c : Nat) (room : cell c+1<2^33) (ptr : m.reg .x16=wordAddress (cell c)) : Checked m (spill c) := by
  simp only [spill,Checked,Op.Valid,Op.apply,true_and,and_true]
  refine ⟨room,?_⟩;change m.reg .x16+signExtend12 8=_;rw [ptr,wordAddress_add];rfl

theorem memory (m : Model) (c w : Nat) (small : w≤64) (zero : m.reg .x0=0) (off : m.reg .x26=W (c%64))
    (value : m.reg .x14=first m.mem c (m.reg .x30)) : (result m c w).mem=put m.mem c w (m.reg .x30) := by
  change (saved m c w).mem=_
  unfold saved put
  by_cases cross : c%64+w>64
  · simp only [ite_eq_left cross]
    have sh := CapLowMergedWords.shift m c off (by omega) zero
    change writeWord (writeWord m.mem (cell c) (m.reg .x14)) (cell c+1)
      (m.reg .x30 >>> ((CapLowMergedWords.signed m).toNat%64))=_
    rw [value,sh]
  · simp only [ite_eq_right cross]
    change writeWord m.mem (cell c) (m.reg .x14)=_;rw [value]

theorem carryReg (m : Model) (c w : Nat) (r : Reg) (keep : r≠.x12) :
    (saved m c w).reg r=m.reg r := by
  unfold saved;split <;> simp [after,start,spill,Op.apply,Model.set,Model.store,keep.symm]

theorem registers (m : Model) (c w : Nat) (cursor : m.reg .x7=W c) (width : m.reg .x23=W w) :
    (result m c w).reg .x7=W (c+w) ∧ (result m c w).reg .x24=m.reg .x24+4 ∧
    ∀ r, r≠.x12 → r≠.x7 → r≠.x24 → (result m c w).reg r=m.reg r := by
  refine ⟨?_,?_,?_⟩
  · change (saved m c w).reg .x7+(saved m c w).reg .x23=_
    rw [carryReg _ _ _ _ (by decide),carryReg _ _ _ _ (by decide),cursor,width,←BitVec.ofNat_add]
  · change (saved m c w).reg .x24+signExtend12 4=_
    rw [carryReg _ _ _ _ (by decide)];rfl
  · intro r a b d
    unfold result;rw [sameReg _ bump r (by simp [bump,changes,beq_eq_false_iff_ne.mpr d.symm,beq_eq_false_iff_ne.mpr b.symm])]
    exact carryReg _ _ _ _ a

private theorem gate (o : Oracle) (s : MachineState) (pc : s.pc=addr 1576) (n : Nat) (small : n<129)
    (counter : s.getReg .x12=W n) (limit : s.getReg .x28=65) :
    CommitExact.Segment o OpeningStraight.image 1 s (s.setPC (if n>64 then addr 1577 else addr 1509)) := by
  apply CommitExact.plain o _ _ _ (.base (.BLTU .x12 .x28 7924)) (OpeningStraight.fetched 1576 _ (by decide) rfl s pc)
  change some (if (s.getReg .x12).ult (s.getReg .x28) then s.setPC (s.pc+signExtend13 7924) else s.setPC (s.pc+4))=_
  rw [pc,counter,limit]
  have rule (i : Fin 129) : (W i.val).ult 65=decide (i.val≤64) := by exact (by decide : ∀ k : Fin 129, (W k.val).ult 65=decide (k.val≤64)) i
  rw [rule ⟨n,small⟩]
  by_cases high : n>64
  · simp only [ite_eq_left high,show ¬n≤64 by omega,decide_false,Bool.false_eq_true,ite_false];rfl
  · simp only [ite_eq_right high,show n≤64 by omega,decide_true,ite_true];rfl

theorem run (o : Oracle) (m : Model) (s : MachineState) (pc : s.pc=addr 1574) (fit : Fits s m) (c w : Nat)
    (small : w≤64) (room : cell c+1<2^33) (off : m.reg .x26=W (c%64)) (width : m.reg .x23=W w)
    (dst : m.reg .x16=wordAddress (cell c)) (limit : m.reg .x28=65) :
    ∃ (n : Nat) (t : MachineState), n≤9 ∧ CommitExact.Segment o OpeningStraight.image n s t ∧ t.pc=addr 1511 ∧ Fits t (result m c w) := by
  let a := after m (start c)
  obtain ⟨u,runA,locA,fitA⟩ := OpeningStraight.block o m (start c) 1574 (by change 1574+2≤1660;decide)
    ⟨rfl,rfl,True.intro⟩ (startChecks m c room dst) s pc fit
  have nreg : a.reg .x12=W (c%64+w) := by change m.reg .x26+m.reg .x23=_;rw [off,width,←BitVec.ofNat_add]
  have branch := gate o u locA (c%64+w) (by omega) ((fitA.registers _).trans nreg) ((fitA.registers _).trans limit)
  have middle : ∃ (n : Nat) (v : MachineState), n≤7 ∧ CommitExact.Segment o OpeningStraight.image n s v ∧
      v.pc=addr 1509 ∧ Fits v (saved m c w) := by
    by_cases cross : c%64+w>64
    · rw [ite_eq_left cross] at branch
      obtain ⟨t,rr,l,f⟩ := OpeningStraight.block o a (spill c) 1577 (by change 1577+3≤1660;decide)
        ⟨rfl,rfl,rfl,True.intro⟩ (spillChecks a c room dst) _ rfl (fitA.pc _)
      have go : CommitExact.Segment o OpeningStraight.image 1 t (t.setPC (addr 1509)) := by
        apply CommitExact.plain o _ _ _ (.base (.JAL .x0 2096868)) (OpeningStraight.fetched 1580 _ (by decide) rfl t l)
        change some (t.setPC (t.pc+signExtend21 2096868))=some (t.setPC (addr 1509))
        have loc : t.pc=addr 1580 := l
        have target : addr 1580+signExtend21 2096868=addr 1509 := by decide
        exact congrArg (fun pc => some (t.setPC pc)) ((congrArg (·+signExtend21 2096868) loc).trans target)
      exact ⟨7,_,by decide,CommitExact.compose (CommitExact.compose (CommitExact.compose runA branch) rr) go,rfl,
        by simp only [saved,ite_eq_left cross];exact f.pc _⟩
    · rw [ite_eq_right cross] at branch
      exact ⟨3,_,by decide,CommitExact.compose runA branch,rfl,by simp only [saved,ite_eq_right cross];exact fitA.pc _⟩
  obtain ⟨n,v,hn,rr,loc,f⟩ := middle
  obtain ⟨t,runB,locB,fitB⟩ := OpeningStraight.block o (saved m c w) bump 1509 (by decide) ⟨rfl,rfl,True.intro⟩
    (by simp [bump,Checked,Op.Valid]) v loc f
  exact ⟨n+2,t,by omega,CommitExact.compose rr runB,locB,fitB⟩

end CommitGolfCandidate.Reconstruction.CapLowLast
