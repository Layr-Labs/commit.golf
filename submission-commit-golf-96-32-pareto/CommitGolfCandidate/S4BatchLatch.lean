import CommitGolfCandidate.S4Marks
namespace CommitGolfCandidate.S4.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Machine (W Runs indexBase)
open Late (pcAt)

def tileBranch (s : MachineState) := execInstrBr (execInstrBr s (.ADDI .x13 .x13 64)) (.ADDI .x9 .x9 4095)
def tileDest (tile : Nat) := if tile+1=16 then 4892 else 8
def tileEnd (s : MachineState) (tile : Nat) := (tileBranch s).setPC (pcAt (tileDest tile))
def tileSteps (tile : Nat) := if tile+1=16 then 3 else 4

theorem tileLatch (t : Nat) (bt : t<16) (s : MachineState) (pc : s.pc=pcAt 4888)
    (ix : s.getReg .x13=W (indexBase+64*t)) (left : s.getReg .x9=W (16-t)) :
    let z:=tileEnd s t
    Runs .opening s z (tileSteps t) (tileSteps t) ∧ z.pc=pcAt (tileDest t) ∧
      z.getReg .x13=W (indexBase+64*(t+1)) ∧ z.getReg .x9=W (16-(t+1)) ∧
      z.mem=s.mem ∧ ∀ r,r≠.x13 → r≠.x9 → z.getReg r=s.getReg r := by
  let u:=execInstrBr s (.ADDI .x13 .x13 64)
  let v:=tileBranch s
  have a:=Machine.stepAdd .opening s 4888 .x13 .x13 64 (by decide) pc (by rfl)
  have b:=Machine.stepAdd .opening u 4889 .x9 .x9 4095 (by decide) (Machine.addPC _ _ _ pc) (by rfl)
  have endPC : v.pc=pcAt 4890:=Machine.addPC _ _ _ (Machine.addPC _ _ _ pc)
  have idx : v.getReg .x13=W (indexBase+64*(t+1)):=by
    rw [show v.getReg .x13=u.getReg .x13 from Machine.keepAdd u .x9 .x9 .x13 4095 (by decide)]
    have w:=Machine.getAfterAdd s .x13 .x13 64 (by decide)
    change u.getReg .x13=_ at w;rw [w,ix];change W _+W 64=_
    exact (BitVec.ofNat_add ..).symm.trans (congrArg W (by omega))
  have rem : v.getReg .x9=W (16-(t+1)):=by
    have w:=Machine.getAfterAdd u .x9 .x9 4095 (by decide)
    change v.getReg .x9=_ at w
    rw [w,show u.getReg .x9=s.getReg .x9 from Machine.keepAdd s .x13 .x13 .x9 64 (by decide),left]
    exact (Machine.prev (16-t) (by omega)).trans (congrArg W (by omega))
  have control:=Machine.alternate .opening 4890 4892 8 .x9 .x0 true (by decide) (by decide) rfl v endPC
  have test : ((v.getReg .x9==v.getReg .x0)==true)=decide (16-(t+1)=0):=by
    rw [rem];change ((W _==W 0)==true)=_;rw [Machine.eqNatural _ _ (by omega) (by decide)];simp
  rw [test] at control
  refine ⟨?_,rfl,idx,rem,rfl,?_⟩
  · by_cases last : t+1=16
    · rw [decide_eq_true (by omega : 16-(t+1)=0)] at control
      simp only [tileEnd,tileDest,tileSteps,if_pos last];exact (a.trans b).trans control
    · rw [decide_eq_false (by omega : ¬16-(t+1)=0)] at control
      simp only [tileEnd,tileDest,tileSteps,if_neg last];exact (a.trans b).trans control
  · intro r f g
    exact MachineState.getReg_setPC.trans ((Machine.keepAdd u .x9 .x9 r 4095 (Ne.symm g)).trans
      (Machine.keepAdd s .x13 .x13 r 64 (Ne.symm f)))
end CommitGolfCandidate.S4.Open
