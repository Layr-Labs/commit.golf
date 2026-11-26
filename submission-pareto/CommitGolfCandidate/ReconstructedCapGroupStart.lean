import CommitGolfCandidate.ReconstructedCapHeaderDigit

namespace CommitGolfCandidate.Reconstruction.CapGroupStart
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel OpeningOps OpeningQuery OpeningCursor
open TwoPermutationPrototype.RV64
open CommitBlocks (addr)
set_option maxRecDepth 16000

def before : List Op := [.reg .x12 (.addi .x0 4),.reg .x25 (.addi .x24 0)]
def four : List Op := [.reg .x25 (.addi .x0 4)]
def begin_ : List Op := [.reg .x16 (.addi .x0 0),.reg .x30 (.sub .x0 .x25),.reg .x25 (.add .x25 .x22)]

def chosen (m : Model) (rem : Nat) := if rem<4 then after m before else after (after m before) four
def result (m : Model) (rem : Nat) := after (chosen m rem) begin_

theorem groupSize (m : Model) (rem : Nat) (zero : m.reg .x0=0) (regs : m.reg .x24=W rem) :
    (chosen m rem).reg .x25=W (min 4 rem) := by
  unfold chosen
  by_cases h : rem<4
  · rw [ite_eq_left h,Nat.min_eq_right (by omega)]
    change m.reg .x24+0#64=_
    rw [regs,BitVec.add_zero]
  · rw [ite_eq_right h,Nat.min_eq_left (by omega)]
    change m.reg .x0+signExtend12 4=_
    rw [zero];rfl

theorem values (m : Model) (rem j : Nat) (positive : 0<rem) (zero : m.reg .x0=0) (pending : m.reg .x24=W rem)
    (index : m.reg .x22=W j-1) :
    let t := result m rem
    t.mem=m.mem ∧ t.reg .x16=0 ∧ t.reg .x30=CapHeaderDigit.neg (min 4 rem) ∧ t.reg .x25=W (j+min 4 rem-1) ∧
      ∀ r, r≠.x12 → r≠.x25 → r≠.x16 → r≠.x30 → t.reg r=m.reg r := by
  have common (r : Reg) (a : r≠.x12) (b : r≠.x25) : (chosen m rem).reg r=m.reg r := by
    unfold chosen;split <;> simp [after,before,four,Op.apply,Model.set,a.symm,b.symm]
  have reg := groupSize m rem zero pending
  have z := (common .x0 (by decide) (by decide)).trans zero
  have ptr := (common .x22 (by decide) (by decide)).trans index
  refine ⟨?_,?_,?_,?_,?_⟩
  · change (chosen m rem).mem=m.mem;unfold chosen;split <;> rfl
  · change (chosen m rem).reg .x0+0#64=_;rw [z];rfl
  · change (chosen m rem).reg .x0-(chosen m rem).reg .x25=_;rw [reg,z];rfl
  · change (chosen m rem).reg .x25+(chosen m rem).reg .x22=_
    rw [reg,ptr]
    have ord : 1≤j+min 4 rem := by omega
    have back : W (j+min 4 rem-1)+1=W (j+min 4 rem) := by
      change W (j+min 4 rem-1)+W 1=_;rw [←BitVec.ofNat_add,Nat.sub_add_cancel ord]
    have sum : W j+W (min 4 rem)=W (j+min 4 rem) := (BitVec.ofNat_add ..).symm
    bv_omega
  · intro r a b c d
    unfold result;rw [CapLowCore.sameReg _ begin_ r (by simp [begin_,CapLowCore.changes,
      beq_eq_false_iff_ne.mpr b.symm,beq_eq_false_iff_ne.mpr c.symm,beq_eq_false_iff_ne.mpr d.symm])]
    exact common r a b

theorem run (o : Oracle) (m : Model) (s : MachineState) (pc : s.pc=addr 1603) (fit : Fits s m)
    (rem : Nat) (bound : rem≤256) (pending : m.reg .x24=W rem) : ∃ n t, n≤7 ∧
    CommitExact.Segment o OpeningStraight.image n s t ∧ t.pc=addr 1610 ∧ Fits t (result m rem) := by
  let a := after m before
  obtain ⟨u,r,loc,fu⟩ := OpeningStraight.block o m before 1603 (by decide) ⟨rfl,rfl,True.intro⟩
    (by simp [before,Checked,Op.Valid]) s pc fit
  have zero : m.reg .x0=0 := (fit.registers _).symm.trans rfl
  have fourReg : a.reg .x12=W 4 := by change m.reg .x0+signExtend12 4=_;rw [zero];rfl
  have branch : CommitExact.Segment o OpeningStraight.image 1 u (u.setPC (if rem<4 then addr 1607 else addr 1606)) := by
    apply CommitExact.plain o _ _ _ (.base (.BLTU .x24 .x12 8)) (OpeningStraight.fetched 1605 _ (by decide) rfl u loc)
    change some (if (u.getReg .x24).ult (u.getReg .x12) then u.setPC (u.pc+signExtend13 8) else u.setPC (u.pc+4))=_
    have r' : u.getReg .x24=W rem := (fu.registers _).trans pending
    have f' : u.getReg .x12=W 4 := (fu.registers _).trans fourReg
    have pcU : u.pc=addr 1605 := loc
    rw [r',f',pcU,HonestCapState.unsigned (by omega : rem<2^64) (by decide : 4<2^64)]
    by_cases small : rem<4 <;> simp only [small,decide_true,decide_false,Bool.false_eq_true,ite_true,ite_false] <;> rfl
  have phase : ∃ k v, k≤4 ∧ CommitExact.Segment o OpeningStraight.image k s v ∧ v.pc=addr 1607 ∧ Fits v (chosen m rem) := by
    by_cases small : rem<4
    · rw [ite_eq_left small] at branch
      exact ⟨3,_,by decide,CommitExact.compose r branch,rfl,by rw [chosen,ite_eq_left small];exact fu.pc _⟩
    · rw [ite_eq_right small] at branch
      obtain ⟨v,q,vp,vf⟩ := OpeningStraight.block o a four 1606 (by decide) ⟨rfl,True.intro⟩
        (by simp [four,Checked,Op.Valid]) _ rfl (fu.pc _)
      exact ⟨4,v,by decide,CommitExact.compose (CommitExact.compose r branch) q,vp,by rw [chosen,ite_eq_right small];exact vf⟩
  obtain ⟨k,v,h,rr,vp,vf⟩ := phase
  obtain ⟨t,q,pt,ft⟩ := OpeningStraight.block o (chosen m rem) begin_ 1607 (by decide) ⟨rfl,rfl,rfl,True.intro⟩
    (by simp [begin_,Checked,Op.Valid]) v vp vf
  exact ⟨k+3,t,by omega,CommitExact.compose rr q,pt,ft⟩

end CommitGolfCandidate.Reconstruction.CapGroupStart
