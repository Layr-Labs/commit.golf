import CommitGolfCandidate.S5BatchFrame
namespace CommitGolfCandidate.S5Machine.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
def capLatch : PathCode := [(379,.ADDI .x22 .x22 1),(380,.BLTU .x22 .x9 8092)]

theorem cap_latch (s : MachineState) (p : Nat) (hp : p<171) (pc : s.pc=pcAt 379) (ctr : s.getReg .x22=W p)
    (ub : s.getReg .x9=W 171) :
    let t:=pathEnd s capLatch
    Runs s t 2 2 ∧ t.pc=pcAt (if p+1<171 then 355 else 381) ∧ t.getReg .x22=W (p+1) ∧ t.mem=s.mem ∧
      ∀ q,q≠.x22→t.getReg q=s.getReg q := by
  let u:=execInstrBr s (.ADDI .x22 .x22 1)
  have ip : u.pc=pcAt 380:=by change s.pc+4=_;rw [pc];rfl
  have inc : u.getReg .x22=W (p+1):=(congrArg (·+signExtend12 1) ctr).trans (BitVec.ofNat_add p 1).symm
  have limit : u.getReg .x9=W 171:=ub
  have branch : (u.getReg .x22).toNat < (u.getReg .x9).toNat ↔ p+1<171 := by
    rw [inc,limit];change (W (p+1)).toNat<(W 171).toNat ↔ _
    simp only [W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show p+1<2^64 by omega),Nat.mod_eq_of_lt (show 171<2^64 by decide)]
  have test : BitVec.ult (u.getReg .x22) (u.getReg .x9)=decide (p+1<171) := by
    apply Bool.eq_iff_iff.mpr
    simpa only [BitVec.ult,decide_eq_true_eq] using branch
  have last : pathEnd s capLatch=u.setPC (pcAt (if p+1<171 then 355 else 381)) := by
    change (if BitVec.ult (u.getReg .x22) (u.getReg .x9) then u.setPC (u.pc+signExtend13 8092) else u.setPC (u.pc+4))=_
    rw [test,ip];by_cases b : p+1<171 <;> simp only [b,decide_true,decide_false,Bool.false_eq_true,ite_true,ite_false] <;> rfl
  have ready : pathReady s capLatch:=⟨pc,rfl,rfl,ip,rfl,rfl,True.intro⟩
  refine ⟨path_run _ true _ _ (by decide +kernel) ready,?_,?_,?_,?_⟩
  · rw [last];rfl
  · rw [last];exact inc
  · rw [last];rfl
  · intro q diff;rw [last];exact MachineState.getReg_setPC.trans (MachineState.getReg_setPC.trans (MachineState.getReg_setReg_ne _ _ _ _ diff.symm))
end CommitGolfCandidate.S5Machine.Open
