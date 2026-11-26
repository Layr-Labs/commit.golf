import CommitGolfCandidate.S4OpenEntry
namespace CommitGolfCandidate.S4.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Machine (W Runs indexBase)
open Late (pcAt pc_succ)

def normalEndPC (k r : Nat) := if r<k then 5281 else 5872
def counts (s : MachineState) := execInstrBr (execInstrBr s (.ADDI .x21 .x21 8)) (.ADDI .x20 .x20 4095)
def normalTail (s : MachineState) (k r : Nat) := (counts s).setPC (pcAt (normalEndPC k (r+1)))
def latchPrice (k r : Nat) := if r+1<k then 4 else 3

theorem normalLatch (s : MachineState) (k r : Nat) (br : r<k) (bk : k≤16777216)
    (pc : s.pc=pcAt 5868) (ix : s.getReg .x21=W (indexBase+8*r)) (left : s.getReg .x20=W (k-r)) :
    let t:=normalTail s k r
    Runs .opening s t (latchPrice k r) (latchPrice k r) ∧ t.pc=pcAt (normalEndPC k (r+1)) ∧
    t.getReg .x21=W (indexBase+8*(r+1)) ∧ t.getReg .x20=W (k-(r+1)) ∧
    t.mem=s.mem ∧ ∀ j,j≠.x21 → j≠.x20 → t.getReg j=s.getReg j := by
  let u:=execInstrBr s (.ADDI .x21 .x21 8)
  have a:=Machine.stepAdd .opening s 5868 .x21 .x21 8 (by decide) pc (by rfl)
  have b:=Machine.stepAdd .opening u 5869 .x20 .x20 4095 (by decide) (Machine.addPC _ _ _ pc) (by rfl)
  let t:=counts s
  have atBranch : t.pc=pcAt 5870:=Machine.addPC _ _ _ (Machine.addPC _ _ _ pc)
  have idx : t.getReg .x21=W (indexBase+8*(r+1)):=by
    rw [show t.getReg .x21=u.getReg .x21 from Machine.keepAdd u .x20 .x20 .x21 4095 (by decide)]
    have h:=Machine.getAfterAdd s .x21 .x21 8 (by decide)
    change u.getReg .x21=_ at h;rw [h,ix]
    change W _+W 8=_
    exact (BitVec.ofNat_add ..).symm.trans (congrArg W (by omega))
  have rem : t.getReg .x20=W (k-(r+1)):=by
    have h:=Machine.getAfterAdd u .x20 .x20 4095 (by decide)
    change t.getReg .x20=_ at h
    rw [h,show u.getReg .x20=s.getReg .x20 from Machine.keepAdd s .x21 .x21 .x20 8 (by decide),left]
    exact (Machine.prev (k-r) (by omega)).trans (congrArg W (by omega))
  have edge:=Machine.alternate .opening 5870 5872 5281 .x20 .x0 true (by decide) (by decide) rfl t atBranch
  have test : ((t.getReg .x20==t.getReg .x0)==true)=decide (k-(r+1)=0):=by
    rw [rem];change ((W _==W 0)==true)=_;rw [Machine.eqNatural _ _ (by omega) (by decide)];simp
  rw [test] at edge
  refine ⟨?_,rfl,idx,rem,rfl,?_⟩
  · by_cases more : r+1<k
    · rw [decide_eq_false (by omega : ¬k-(r+1)=0)] at edge
      simp only [normalTail,normalEndPC,latchPrice,if_pos more];exact (a.trans b).trans edge
    · rw [decide_eq_true (by omega : k-(r+1)=0)] at edge
      simp only [normalTail,normalEndPC,latchPrice,if_neg more];exact (a.trans b).trans edge
  · intro j f g
    exact MachineState.getReg_setPC.trans ((Machine.keepAdd u .x20 .x20 j 4095 (Ne.symm g)).trans
      (Machine.keepAdd s .x21 .x21 j 8 (Ne.symm f)))
end CommitGolfCandidate.S4.Open
