import CommitGolfCandidate.Layout2QuartetCtlDispatch
import CommitGolfCandidate.Layout2QuartetCtlTail
import CommitGolfCandidate.Layout2QuartetCtlGuard
import CommitGolfCandidate.Layout2Superblock

namespace CommitGolfCandidate.Layout2.Quartet
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxHeartbeats 900000
set_option maxRecDepth 10000

def dispatchCost (q : Fin 4) := if q.val=3 then 9 else 3+2*q.val

theorem dispatch (s : MachineState) (q : Fin 4) (here : s.pc=pc 795)
    (valid : accessValid (s.getReg .x9) 8=true) (select : s.getMem (s.getReg .x9) &&& 3#64=addr q.val) :
    ∃ t, Runs checkImage s t (dispatchCost q) (dispatchCost q) ∧ t.pc=pc (body q) ∧
      t.mem=s.mem ∧ ∀ r, r≠.x5 → t.getReg r=s.getReg r := by
  obtain ⟨a,runA,pcA,memA,regA⟩:=ctl_dispatch s here valid
  simp only [select] at pcA regA
  fin_cases q
  · have branch : a.pc=pc 804 := pcA
    refine ⟨a,runA,branch,memA,?_⟩
    intro r h;simpa only [regA,if_neg (Ne.symm h)]
  · have branch : a.pc=pc 798 := pcA
    obtain ⟨b,runb,pcb,memb,regb⟩:=ctl_dec798 a branch
    simp only [regA,ite_true] at pcb
    have branch : b.pc=pc 851 := pcb
    refine ⟨b,(runA.thenDo runb),branch,(memb.trans memA),?_⟩
    intro r h;simpa only [regb,regA,if_neg (Ne.symm h)]
  · have branch : a.pc=pc 798 := pcA
    obtain ⟨b,runb,pcb,memb,regb⟩:=ctl_dec798 a branch
    simp only [regA,ite_true] at pcb
    have branch : b.pc=pc 800 := pcb
    obtain ⟨c,runc,pcc,memc,regc⟩:=ctl_dec800 b branch
    simp only [regb,regA,ite_true] at pcc
    have branch : c.pc=pc 898 := pcc
    refine ⟨c,((runA.thenDo runb).thenDo runc),branch,(memc.trans (memb.trans memA)),?_⟩
    intro r h;simpa only [regc,regb,regA,if_neg (Ne.symm h)]
  · have branch : a.pc=pc 798 := pcA
    obtain ⟨b,runb,pcb,memb,regb⟩:=ctl_dec798 a branch
    simp only [regA,ite_true] at pcb
    have branch : b.pc=pc 800 := pcb
    obtain ⟨c,runc,pcc,memc,regc⟩:=ctl_dec800 b branch
    simp only [regb,regA,ite_true] at pcc
    have branch : c.pc=pc 802 := pcc
    obtain ⟨f,runf,pcf,memf,regf⟩:=ctl_lastQ c branch
    have branch : f.pc=pc 945 := pcf
    refine ⟨f,(((runA.thenDo runb).thenDo runc).thenDo runf),branch,(memf.trans (memc.trans (memb.trans memA))),?_⟩
    intro r h;simpa only [regf,regc,regb,regA,if_neg (Ne.symm h)]

theorem jumpTail (s : MachineState) (q : Fin 4) (here : s.pc=pc (body q+46)) :
    ∃ t, Runs checkImage s t 1 1 ∧ t.pc=pc 992 ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=s.getReg r := by
  fin_cases q
  · exact ctl_jump0 s here
  · exact ctl_jump1 s here
  · exact ctl_jump2 s here
  · exact ctl_jump3 s here

end CommitGolfCandidate.Layout2.Quartet
