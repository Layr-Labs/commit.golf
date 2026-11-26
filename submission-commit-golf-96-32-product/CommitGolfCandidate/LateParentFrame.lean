import CommitGolfCandidate.LateParentBody

namespace CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def levelSize (d : Fin 24) := levelCount (d.val+1)
def parentNextPC (d : Fin 24) (p : Nat) := if p<levelSize d then parentPC d (p%32) else parentEndPC d

structure ParentFrame (s : MachineState) (d : Fin 24) (p : Nat) extends ParentRegs s d p : Prop where
  pc : s.pc=pcAt (parentNextPC d p)
  count : 32 ≤ levelSize d → s.getReg .x20=BitVec.ofNat 64 (levelSize d/32-p/32)
  td : s.getReg .x9 = 4294971424
  root : s.getReg .x26 = 4294971392

private theorem branch_is (s : MachineState) : parentBranch s =
    if s.getReg .x20 != 0 then s.setPC (s.pc+signExtend13 7796) else s.setPC (s.pc+4) := rfl

private theorem branch_reg (s : MachineState) (r : Reg) : (parentBranch s).getReg r=s.getReg r := by
  have choose (c : Bool) (yes no : Word) : (if c then s.setPC yes else s.setPC no).getReg r = s.getReg r := by
    cases c <;> exact MachineState.getReg_setPC
  exact choose (s.getReg .x20 != 0) (s.pc+signExtend13 7796) (s.pc+4)

theorem tick_mem (h : Compression) {s : MachineState} {d : Fin 24} {p : Nat} (regs : ParentRegs s d p) (inside : p < levelCount (d.val+1)) :
    (parentTick h s d p).mem = (writeParent h s d p).mem := by
  let r := parentResult h s d p
  have same := parent_result_mem h s d p regs inside
  have adv (q : MachineState) : (advance q).mem=q.mem := rfl
  have br (q : MachineState) : (parentBranch q).mem=q.mem := by
    have choose (c : Bool) (yes no : Word) : (if c then q.setPC yes else q.setPC no).mem=q.mem := by cases c <;> rfl
    exact choose (q.getReg .x20 != 0) (q.pc+signExtend13 7796) (q.pc+4)
  by_cases e : p%32=31
  · simp only [parentTick, if_pos e]
    exact (br _).trans ((adv _).trans same)
  · simpa only [parentTick, if_neg e] using same

private theorem layout : ∀ d : Fin 24,
    0 < levelSize d ∧ levelSize d ≤ 8388608 ∧
    (32 ≤ levelSize d → levelSize d %32=0) ∧
    parentEndPC d = parentBodyPC d + 3*min 32 (levelSize d) + (if 32≤levelSize d then 4 else 0) ∧
    (pcAt (parentBodyPC d+99)) + signExtend13 7796 = pcAt (parentBodyPC d) := by decide


private theorem advance_keeps (s : MachineState) (r : Reg)
    (a : Reg.x21 ≠ r) (b : Reg.x22 ≠ r) (c : Reg.x20 ≠ r) :
    (advance s).getReg r=s.getReg r := by
  simp only [advance,parentUpdates,List.foldl_cons,List.foldl_nil,execInstrBr,MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ a,MachineState.getReg_setReg_ne _ _ _ _ b,MachineState.getReg_setReg_ne _ _ _ _ c]

private theorem advance_values (s : MachineState) :
    (advance s).getReg .x21=s.getReg .x21+s.getReg .x29 ∧ (advance s).getReg .x22=s.getReg .x22+1536 ∧
    (advance s).getReg .x20=s.getReg .x20-1 ∧ (advance s).pc=s.pc+12 := by
  refine ⟨rfl,rfl,?_,?_⟩
  · rw [BitVec.sub_eq_add_neg];rfl
  · change s.pc+4+4+4=s.pc+12;rw [BitVec.add_assoc,BitVec.add_assoc];rfl

private theorem result_keeps (h : Compression) (s : MachineState) (d : Fin 24) (p : Nat) (r : Reg)
    (a : Reg.x10 ≠ r) (b : Reg.x12 ≠ r) : (parentResult h s d p).getReg r=s.getReg r :=
  call_register _ _ _ _ _ _ _ a b

private theorem result_pc (h : Compression) (s : MachineState) (d : Fin 24) (p : Nat) :
    (parentResult h s d p).pc=s.pc+12 := call_pc _ _ _ _ _ _

attribute [local irreducible] parentResult advance parentBranch parentEndPC parentBodyPC levelSize

private theorem tick_keeps (h : Compression) (s : MachineState) (d : Fin 24) (p : Nat) (r : Reg)
    (a : Reg.x10 ≠ r) (b : Reg.x12 ≠ r) (c : Reg.x21 ≠ r) (e : Reg.x22 ≠ r) (f : Reg.x20 ≠ r) :
    (parentTick h s d p).getReg r=s.getReg r := by
  by_cases t : p%32=31
  · simp only [parentTick,if_pos t,branch_reg,advance_keeps _ _ c e f,result_keeps _ _ _ _ _ a b]
  · simpa only [parentTick,if_neg t] using result_keeps h s d p r a b

private theorem last_values (h : Compression) (s : MachineState) (d : Fin 24) (p : Nat) (last : p%32=31) (stride : s.getReg .x29=3072) :
    let t := parentTick h s d p
    t.getReg .x21=s.getReg .x21+3072 ∧ t.getReg .x22=s.getReg .x22+1536 ∧ t.getReg .x20=s.getReg .x20-1 := by
  let r := parentResult h s d p
  obtain ⟨src,dst,count,_⟩ := advance_values r
  change _ ∧ _ ∧ _
  simp only [parentTick,if_pos last,branch_reg]
  exact ⟨by rw [src,result_keeps _ _ _ _ _ (by decide) (by decide),
      result_keeps _ _ _ _ _ (by decide) (by decide),stride],
    dst.trans (congrArg (·+1536) (result_keeps _ _ _ _ _ (by decide) (by decide))),
    count.trans (congrArg (·-1) (result_keeps _ _ _ _ _ (by decide) (by decide)))⟩

private theorem count_next (size p : Nat) (large : size%32=0) (hi : p<size) (last : p%32=31) :
    BitVec.ofNat 64 (size/32-p/32)-1=BitVec.ofNat 64 (size/32-(p+1)/32) :=
  (BitVec.ofNat_sub_ofNat_of_le (w:=64) (size/32-p/32) 1 (by decide) (by omega)).trans
    (congrArg (BitVec.ofNat 64) (by omega))

private theorem src_next (d p : Nat) (last : p%32=31) :
    (BitVec.ofNat 64 (nodeAddress d (2*(32*(p/32)))) + BitVec.ofNat 64 (parentBias d))+3072 =
      BitVec.ofNat 64 (nodeAddress d (2*(32*((p+1)/32)))) + BitVec.ofNat 64 (parentBias d) := by
  change (BitVec.ofNat 64 _ + BitVec.ofNat 64 _) + BitVec.ofNat 64 3072 = _
  rw [←BitVec.ofNat_add,←BitVec.ofNat_add,←BitVec.ofNat_add]; apply congrArg (BitVec.ofNat 64);unfold nodeAddress gapOffset;omega

private theorem dst_next (d p : Nat) (last : p%32=31) :
    BitVec.ofNat 64 (nodeAddress d (32*(p/32)))+1536 = BitVec.ofNat 64 (nodeAddress d (32*((p+1)/32))) := by
  change BitVec.ofNat 64 _ + BitVec.ofNat 64 1536 = _
  rw [←BitVec.ofNat_add]; apply congrArg (BitVec.ofNat 64);unfold nodeAddress gapOffset;omega

private theorem word_pc_add (pc n : Nat) : pcAt pc + BitVec.ofNat 64 (4*n) = pcAt (pc+n) := by
  unfold pcAt;rw [←BitVec.ofNat_add];apply congrArg (BitVec.ofNat 64);omega

private theorem next_pc_plain (d : Fin 24) (p : Nat) (inside : p<levelSize d) (short : p%32≠31) :
    pcAt (parentPC d (p%32))+12=pcAt (parentNextPC d (p+1)) := by
  obtain ⟨_,_,m,e,_⟩ := layout d
  change pcAt _ + BitVec.ofNat 64 (4*3) = _
  rw [word_pc_add];apply congrArg pcAt
  by_cases cont : p+1<levelSize d
  · simp only [parentNextPC,if_pos cont,parentPC];omega
  · have sm : levelSize d < 32 := by by_contra! le;have := m le;omega
    rw [parentNextPC,if_neg cont,e,if_neg (by omega),Nat.min_eq_right (by omega)]
    unfold parentPC;omega

private theorem last_pc (d : Fin 24) (p : Nat) (inside : p<levelSize d) (last : p%32=31) (s : MachineState)
    (pc : s.pc=pcAt (parentBodyPC d+99)) (cnt : s.getReg .x20=BitVec.ofNat 64 (levelSize d/32-(p+1)/32)) :
    (parentBranch s).pc=pcAt (parentNextPC d (p+1)) := by
  obtain ⟨_,bnd,m,e,back⟩ := layout d
  have large : 32 ≤ levelSize d := by omega
  rw [branch_is,cnt,pc]
  by_cases cont : p+1<levelSize d
  · have ne : BitVec.ofNat 64 (levelSize d/32-(p+1)/32) ≠ 0 := by
      intro eq; have v := congrArg BitVec.toNat eq
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)] at v; change _=0 at v; have := m large;omega
    rw [if_pos (bne_iff_ne.mpr ne)]
    change pcAt (parentBodyPC d+99)+signExtend13 7796 = _
    simpa only [parentNextPC,if_pos cont,show (p+1)%32=0 by omega,parentPC,Nat.mul_zero,Nat.add_zero] using back
  · have z : levelSize d/32-(p+1)/32=0 := by omega
    simp only [z,parentNextPC,if_neg cont]
    change pcAt (parentBodyPC d+99)+4=_
    rw [←pc_succ,e,if_pos large,Nat.min_eq_left large]

theorem tick_frame (h : Compression) {s : MachineState} {d : Fin 24} {p : Nat}
    (inside : p<levelSize d) (a : ParentFrame s d p) : ParentFrame (parentTick h s d p) d (p+1) := by
  have stride (last : p%32=31) : s.getReg .x29=3072 := by
    apply a.stride
    have hl : 32 ≤ levelSize d := by omega
    simpa only [levelSize] using hl
  let r := parentResult h s d p
  have ip : s.pc=pcAt (parentPC d (p%32)) := by simpa only [parentNextPC,if_pos inside] using a.pc
  have keep (k : Reg) (h1 : Reg.x10≠k) (h2 : Reg.x12≠k) (h3 : Reg.x21≠k) (h4 : Reg.x22≠k) (h5 : Reg.x20≠k) :=
    tick_keeps h s d p k h1 h2 h3 h4 h5
  refine ⟨⟨?_,?_,?_,(keep _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans a.mode,
    (keep _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans a.len,
    (keep _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans a.kind⟩,?_,?_,
    (keep _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans a.td,
    (keep _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans a.root⟩
  · by_cases last : p%32=31
    · rw [(last_values h s d p last (stride last)).1,a.source,src_next d.val p last]
    · simp only [parentTick,if_neg last,show (p+1)/32=p/32 by omega]
      exact (result_keeps _ _ _ _ _ (by decide) (by decide)).trans a.source
  · by_cases last : p%32=31
    · rw [(last_values h s d p last (stride last)).2.1,a.target,dst_next _ p last]
    · simp only [parentTick,if_neg last,show (p+1)/32=p/32 by omega]
      exact (result_keeps _ _ _ _ _ (by decide) (by decide)).trans a.target
  · intro large
    exact (keep _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans (a.stride large)
  · by_cases last : p%32=31
    · have large : 32 ≤ levelSize d := by omega
      have count := (advance_values r).2.2.1
      rw [result_keeps _ _ _ _ _ (by decide) (by decide),a.count large,
        count_next _ _ ((layout d).2.2.1 large) inside last] at count
      simp only [parentTick,if_pos last]
      apply last_pc d p inside last _ _ count
      rw [(advance_values r).2.2.2, result_pc,ip,last]
      change (pcAt (parentBodyPC d+93) + 12) + 12 = _
      rw [BitVec.add_assoc];exact word_pc_add (parentBodyPC d+93) 6
    · simp only [parentTick,if_neg last,result_pc,ip];exact next_pc_plain _ _ inside last
  · intro large
    by_cases last : p%32=31
    · rw [(last_values h s d p last (stride last)).2.2,a.count large,count_next _ _ ((layout d).2.2.1 large) inside last]
    · simp only [parentTick,if_neg last,show (p+1)/32=p/32 by omega]
      exact (result_keeps _ _ _ _ _ (by decide) (by decide)).trans (a.count large)

end CommitGolfCandidate.Late
