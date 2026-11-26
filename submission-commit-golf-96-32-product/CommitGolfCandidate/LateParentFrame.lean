import CommitGolfCandidate.LateParentBody

namespace CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def levelSize (d : Fin 24) := levelCount (d.val+1)
def parentNextPC (d : Fin 24) (p : Nat) := if p<levelSize d then parentPC d (p%16) else parentEndPC d

structure ParentFrame (s : MachineState) (d : Fin 24) (p : Nat) extends ParentRegs s d p : Prop where
  pc : s.pc=pcAt (parentNextPC d p)
  count : 16 ≤ levelSize d → s.getReg .x20=BitVec.ofNat 64 (levelSize d/16-p/16)
  td : s.getReg .x9 = 4294971424
  root : s.getReg .x26 = 4294971392

private theorem branch_is (d : Nat) (s : MachineState) : parentBranch d s =
    if s.getReg .x20 != 0 then s.setPC (s.pc+signExtend13 (latchOffset d)) else s.setPC (s.pc+4) := rfl

private theorem branch_reg (d : Nat) (s : MachineState) (r : Reg) : (parentBranch d s).getReg r=s.getReg r := by
  have choose (c : Bool) (yes no : Word) : (if c then s.setPC yes else s.setPC no).getReg r = s.getReg r := by
    cases c <;> exact MachineState.getReg_setPC
  exact choose (s.getReg .x20 != 0) (s.pc+signExtend13 (latchOffset d)) (s.pc+4)

theorem tick_mem (h : Compression) {s : MachineState} {d : Fin 24} {p : Nat} (regs : ParentRegs s d p) :
    (parentTick h s d p).mem = (writeParent h s d p).mem := by
  let r := parentStore h s d p
  have same := parent_store_mem h s d p regs
  have adv (q : MachineState) : (advance q).mem=q.mem := rfl
  have br (q : MachineState) : (parentBranch d q).mem=q.mem := by
    have choose (c : Bool) (yes no : Word) : (if c then q.setPC yes else q.setPC no).mem=q.mem := by cases c <;> rfl
    exact choose (q.getReg .x20 != 0) (q.pc+signExtend13 (latchOffset d)) (q.pc+4)
  by_cases e : p%16=15
  · simp only [parentTick, if_pos e]
    exact (br _).trans ((adv _).trans same)
  · simpa only [parentTick, if_neg e] using same

private theorem layout : ∀ d : Fin 24,
    0 < levelSize d ∧ levelSize d ≤ 8388608 ∧
    (16 ≤ levelSize d → levelSize d %16=0) ∧
    parentEndPC d = parentBodyPC d + siteWidth d*min 16 (levelSize d) + (if 16≤levelSize d then 4 else 0) ∧
    (pcAt (latchPC d+3)) + signExtend13 (latchOffset d) = pcAt (parentBodyPC d) := by decide


private theorem advance_keeps (s : MachineState) (r : Reg)
    (a : Reg.x21 ≠ r) (b : Reg.x22 ≠ r) (c : Reg.x20 ≠ r) :
    (advance s).getReg r=s.getReg r := by
  simp only [advance,parentUpdates,List.foldl_cons,List.foldl_nil,execInstrBr,MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ a,MachineState.getReg_setReg_ne _ _ _ _ b,MachineState.getReg_setReg_ne _ _ _ _ c]

private theorem advance_values (s : MachineState) :
    (advance s).getReg .x21=s.getReg .x21+1536 ∧ (advance s).getReg .x22=s.getReg .x22+768 ∧
    (advance s).getReg .x20=s.getReg .x20-1 ∧ (advance s).pc=s.pc+12 := by
  refine ⟨rfl,rfl,?_,?_⟩
  · rw [BitVec.sub_eq_add_neg];rfl
  · change s.pc+4+4+4=s.pc+12;rw [BitVec.add_assoc,BitVec.add_assoc];rfl

private theorem result_keeps (h : Compression) (s : MachineState) (d : Fin 24) (p : Nat) (r : Reg)
    (a : Reg.x10 ≠ r) (b : Reg.x12 ≠ r) : (parentStore h s d p).getReg r=s.getReg r :=
  store_after_reg _ _ _ _ _ a b

private theorem result_pc (h : Compression) (s : MachineState) (d : Fin 24) (p : Nat) :
    (parentStore h s d p).pc=s.pc+BitVec.ofNat 64 (4*siteWidth d) := store_after_pc _ _ _ _

attribute [local irreducible] parentStore advance parentBranch parentEndPC parentBodyPC levelSize

private theorem tick_keeps (h : Compression) (s : MachineState) (d : Fin 24) (p : Nat) (r : Reg)
    (a : Reg.x10 ≠ r) (b : Reg.x12 ≠ r) (c : Reg.x21 ≠ r) (e : Reg.x22 ≠ r) (f : Reg.x20 ≠ r) :
    (parentTick h s d p).getReg r=s.getReg r := by
  by_cases t : p%16=15
  · simp only [parentTick,if_pos t,branch_reg,advance_keeps _ _ c e f,result_keeps _ _ _ _ _ a b]
  · simpa only [parentTick,if_neg t] using result_keeps h s d p r a b

private theorem last_values (h : Compression) (s : MachineState) (d : Fin 24) (p : Nat) (last : p%16=15) :
    let t := parentTick h s d p
    t.getReg .x21=s.getReg .x21+1536 ∧ t.getReg .x22=s.getReg .x22+768 ∧ t.getReg .x20=s.getReg .x20-1 := by
  let r := parentStore h s d p
  obtain ⟨src,dst,count,_⟩ := advance_values r
  change _ ∧ _ ∧ _
  simp only [parentTick,if_pos last,branch_reg]
  exact ⟨src.trans (congrArg (·+1536) (result_keeps _ _ _ _ _ (by decide) (by decide))),
    dst.trans (congrArg (·+768) (result_keeps _ _ _ _ _ (by decide) (by decide))),
    count.trans (congrArg (·-1) (result_keeps _ _ _ _ _ (by decide) (by decide)))⟩

private theorem count_next (size p : Nat) (large : size%16=0) (hi : p<size) (last : p%16=15) :
    BitVec.ofNat 64 (size/16-p/16)-1=BitVec.ofNat 64 (size/16-(p+1)/16) :=
  (BitVec.ofNat_sub_ofNat_of_le (w:=64) (size/16-p/16) 1 (by decide) (by omega)).trans
    (congrArg (BitVec.ofNat 64) (by omega))

private theorem src_next (d p : Nat) (last : p%16=15) :
    BitVec.ofNat 64 (nodeAddress d (2*(16*(p/16))))+1536 = BitVec.ofNat 64 (nodeAddress d (2*(16*((p+1)/16)))) := by
  change BitVec.ofNat 64 _ + BitVec.ofNat 64 1536 = _
  rw [←BitVec.ofNat_add]; apply congrArg (BitVec.ofNat 64);unfold nodeAddress gapOffset;omega

private theorem dst_next (d p : Nat) (last : p%16=15) :
    BitVec.ofNat 64 (nodeAddress d (16*(p/16)))+768 = BitVec.ofNat 64 (nodeAddress d (16*((p+1)/16))) := by
  change BitVec.ofNat 64 _ + BitVec.ofNat 64 768 = _
  rw [←BitVec.ofNat_add]; apply congrArg (BitVec.ofNat 64);unfold nodeAddress gapOffset;omega

private theorem word_pc_add (pc n : Nat) : pcAt pc + BitVec.ofNat 64 (4*n) = pcAt (pc+n) := by
  unfold pcAt;rw [←BitVec.ofNat_add];apply congrArg (BitVec.ofNat 64);omega

private theorem next_pc_plain (d : Fin 24) (p : Nat) (inside : p<levelSize d) (short : p%16≠15) :
    pcAt (parentPC d (p%16))+BitVec.ofNat 64 (4*siteWidth d)=pcAt (parentNextPC d (p+1)) := by
  obtain ⟨_,_,m,e,_⟩ := layout d
  rw [word_pc_add];apply congrArg pcAt
  have hw : siteWidth d = 3 ∨ siteWidth d = 4 := by unfold siteWidth; split <;> simp
  by_cases cont : p+1<levelSize d
  · simp only [parentNextPC,if_pos cont,parentPC]
    rcases hw with hw|hw <;> rw [hw] <;> omega
  · have sm : levelSize d < 16 := by by_contra! le;have := m le;omega
    rw [parentNextPC,if_neg cont,e,if_neg (by omega),Nat.min_eq_right (by omega)]
    unfold parentPC
    rcases hw with hw|hw <;> rw [hw] <;> omega

private theorem last_pc (d : Fin 24) (p : Nat) (inside : p<levelSize d) (last : p%16=15) (s : MachineState)
    (pc : s.pc=pcAt (latchPC d+3)) (cnt : s.getReg .x20=BitVec.ofNat 64 (levelSize d/16-(p+1)/16)) :
    (parentBranch d s).pc=pcAt (parentNextPC d (p+1)) := by
  obtain ⟨_,bnd,m,e,back⟩ := layout d
  have large : 16 ≤ levelSize d := by omega
  rw [branch_is,cnt,pc]
  by_cases cont : p+1<levelSize d
  · have ne : BitVec.ofNat 64 (levelSize d/16-(p+1)/16) ≠ 0 := by
      intro eq; have v := congrArg BitVec.toNat eq
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)] at v; change _=0 at v; have := m large;omega
    rw [if_pos (bne_iff_ne.mpr ne)]
    change pcAt (latchPC d+3)+signExtend13 (latchOffset d) = _
    simpa only [parentNextPC,if_pos cont,show (p+1)%16=0 by omega,parentPC,Nat.mul_zero,Nat.add_zero] using back
  · have z : levelSize d/16-(p+1)/16=0 := by omega
    simp only [z,parentNextPC,if_neg cont]
    change pcAt (latchPC d+3)+4=_
    rw [←pc_succ,e,if_pos large,Nat.min_eq_left large]
    unfold latchPC; apply congrArg pcAt; omega

theorem tick_frame (h : Compression) {s : MachineState} {d : Fin 24} {p : Nat}
    (inside : p<levelSize d) (a : ParentFrame s d p) : ParentFrame (parentTick h s d p) d (p+1) := by
  let r := parentStore h s d p
  have ip : s.pc=pcAt (parentPC d (p%16)) := by simpa only [parentNextPC,if_pos inside] using a.pc
  have keep (k : Reg) (h1 : Reg.x10≠k) (h2 : Reg.x12≠k) (h3 : Reg.x21≠k) (h4 : Reg.x22≠k) (h5 : Reg.x20≠k) :=
    tick_keeps h s d p k h1 h2 h3 h4 h5
  refine ⟨⟨?_,?_,(keep _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans a.mode,
    (keep _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans a.len,
    (keep _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans a.kind⟩,?_,?_,
    (keep _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans a.td,
    (keep _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans a.root⟩
  · by_cases last : p%16=15
    · rw [(last_values h s d p last).1,a.source,src_next d.val p last]
    · simp only [parentTick,if_neg last,show (p+1)/16=p/16 by omega]
      exact (result_keeps _ _ _ _ _ (by decide) (by decide)).trans a.source
  · by_cases last : p%16=15
    · rw [(last_values h s d p last).2.1,a.target,dst_next _ p last]
    · simp only [parentTick,if_neg last,show (p+1)/16=p/16 by omega]
      exact (result_keeps _ _ _ _ _ (by decide) (by decide)).trans a.target
  · by_cases last : p%16=15
    · have large : 16 ≤ levelSize d := by omega
      have count := (advance_values r).2.2.1
      rw [result_keeps _ _ _ _ _ (by decide) (by decide),a.count large,
        count_next _ _ ((layout d).2.2.1 large) inside last] at count
      simp only [parentTick,if_pos last]
      apply last_pc d p inside last _ _ count
      rw [(advance_values r).2.2.2, result_pc,ip,last,BitVec.add_assoc,
        show BitVec.ofNat 64 (4*siteWidth d) + 12 = BitVec.ofNat 64 (4*(siteWidth d+3)) by
          rw [show (12 : Word) = BitVec.ofNat 64 12 from rfl, ←BitVec.ofNat_add]; congr 1,
        word_pc_add]
      unfold parentPC latchPC; apply congrArg pcAt; omega
    · simp only [parentTick,if_neg last,result_pc,ip];exact next_pc_plain _ _ inside last
  · intro large
    by_cases last : p%16=15
    · rw [(last_values h s d p last).2.2,a.count large,count_next _ _ ((layout d).2.2.1 large) inside last]
    · simp only [parentTick,if_neg last,show (p+1)/16=p/16 by omega]
      exact (result_keeps _ _ _ _ _ (by decide) (by decide)).trans (a.count large)

end CommitGolfCandidate.Late
