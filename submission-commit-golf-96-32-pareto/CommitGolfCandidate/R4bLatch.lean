import CommitGolfCandidate.R4bRows
import CommitGolfCandidate.S4BranchRun
namespace CommitGolfCandidate.R4b
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open CommitGolfCandidate.S4
open Machine (W Runs proofBase indexBase)
open Late (pcAt)
def nextSite (t : Nat) := if t=32 then 4892 else 16401

private theorem fixedOther (t : Nat) (r : Reg) (h : r≠.x13) : fixed t r=fixed (t+1) r := by
  cases r <;> first | exact False.elim (h rfl) | rfl

theorem latch (td : Late.Trapdoor) (ps : Positions) (t : Nat) (bt : t<32) (s : MachineState)
    (ip : s.pc=pcAt 17850) (f : Frame td ps t 4 s) :
    ∃ z,Runs .opening s z 5 5 ∧ z.pc=pcAt (nextSite (t+1)) ∧ Frame td ps (t+1) 0 z := by
  let u:=execInstrBr s (.ADDI .x13 .x13 32)
  let v:=execInstrBr u (.ADDI .x19 .x19 2040)
  let w:=execInstrBr v (.ADDI .x9 .x9 4095)
  let z:=w.setPC (pcAt (nextSite (t+1)))
  have a:=Machine.stepAdd .opening s 17850 .x13 .x13 32 (by decide) ip (by rfl)
  have iu : u.pc=pcAt 17851:=Machine.addPC _ _ _ ip
  have b:=Machine.stepAdd .opening u 17851 .x19 .x19 2040 (by decide) iu (by rfl)
  have iv : v.pc=pcAt 17852:=Machine.addPC _ _ _ iu
  have c:=Machine.stepAdd .opening v 17852 .x9 .x9 4095 (by decide) iv (by rfl)
  have iw : w.pc=pcAt 17853:=Machine.addPC _ _ _ iv
  have out : v.getReg .x19=W (proofBase+2040*(t+1)):=by
    have h:=Machine.getAfterAdd u .x19 .x19 2040 (by decide)
    rw [Machine.keepAdd s .x13 .x13 .x19 32 (by decide),f.out] at h
    exact h.trans ((BitVec.ofNat_add (proofBase+2040*t) 2040).symm.trans (congrArg W (by omega)))
  have ix : u.getReg .x13=W (indexBase+32*(t+1)):=by
    have h:=Machine.getAfterAdd s .x13 .x13 32 (by decide)
    rw [f.consts .x13 (indexBase+32*t) rfl] at h
    exact h.trans ((BitVec.ofNat_add (indexBase+32*t) 32).symm.trans (congrArg W (by omega)))
  have cnt : w.getReg .x9=W (32-(t+1)):=by
    have h:=Machine.getAfterAdd v .x9 .x9 4095 (by decide)
    rw [Machine.keepAdd u .x19 .x19 .x9 2040 (by decide),Machine.keepAdd s .x13 .x13 .x9 32 (by decide),f.count] at h
    exact h.trans ((Machine.prev (32-t) (by omega)).trans (congrArg W (by omega)))
  have branch:=Machine.alternate .opening 17853 17855 16401 .x9 .x0 true (by decide) (by decide) rfl w iw
  have test : ((w.getReg .x9==w.getReg .x0)==true)=decide (32-(t+1)=0):=by
    rw [cnt];change ((W _==W 0)==true)=_;rw [Machine.eqNatural _ _ (by omega) (by decide)];simp
  rw [test] at branch
  have last : Runs .opening w z 2 2:=by
    by_cases endTile:t+1=32
    · rw [decide_eq_true (by omega : 32-(t+1)=0)] at branch
      simp only [ite_true] at branch
      have jump:=Machine.jump .opening 17855 4892 (w.setPC (pcAt 17855)) rfl (by decide)
      simpa only [z,nextSite,if_pos endTile,MachineState.setPC] using branch.trans jump
    · rw [decide_eq_false (by omega : ¬32-(t+1)=0)] at branch
      simpa only [z,nextSite,if_neg endTile,Bool.false_eq_true,ite_false] using branch
  have same : z.mem=s.mem:=rfl
  have keep (r : Reg) (i : .x13≠r) (o : .x19≠r) (c : .x9≠r) : z.getReg r=s.getReg r:=
    MachineState.getReg_setPC.trans ((Machine.keepAdd v .x9 .x9 r 4095 c).trans
      ((Machine.keepAdd u .x19 .x19 r 2040 o).trans (Machine.keepAdd s .x13 .x13 r 32 i)))
  have constants : Agree (fixed (t+1)) z:=by
    intro r n e
    by_cases i:r=.x13
    · subst r;cases e
      exact MachineState.getReg_setPC.trans ((Machine.keepAdd v .x9 .x9 .x13 4095 (by decide)).trans
        ((Machine.keepAdd u .x19 .x19 .x13 2040 (by decide)).trans ix))
    · have o : r≠.x19:=by rintro rfl;cases e
      have c : r≠.x9:=by rintro rfl;cases e
      have eq:=fixedOther t r i
      exact (keep r (Ne.symm i) (Ne.symm o) (Ne.symm c)).trans (f.consts _ _ (eq.trans e))
  have rr : 4*(t+1)+0=4*t+4:=by omega
  refine ⟨z,((a.trans b).trans c).trans last,rfl,⟨constants,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩⟩
  · exact MachineState.getReg_setPC.trans ((Machine.keepAdd v .x9 .x9 .x19 4095 (by decide)).trans out)
  · exact MachineState.getReg_setPC.trans cnt
  · exact (keep _ (by decide) (by decide) (by decide)).trans f.flagBase
  · exact (keep _ (by decide) (by decide) (by decide)).trans f.one
  · exact (keep _ (by decide) (by decide) (by decide)).trans f.buffer
  · exact f.sources.sameMem same
  · exact (Protect.ofMem same).table f.table
  · rw [rr];exact protectMarks (Protect.ofMem same) f.flags
  · rw [rr];exact f.cursor.mem same (keep _ (by decide) (by decide) (by decide))
end CommitGolfCandidate.R4b
