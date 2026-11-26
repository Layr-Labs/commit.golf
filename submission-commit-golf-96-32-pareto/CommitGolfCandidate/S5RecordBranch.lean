import CommitGolfCandidate.S5Mark
namespace CommitGolfCandidate.S5Machine.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open CommitGolfCandidate.Late (Levels SaltTape record)

def batchLatchPath : PathCode := [(349,.ADDI .x22 .x22 4095),(350,.BNE .x22 .x0 7368)]
def batchAfterLatch (s : MachineState) := pathEnd s batchLatchPath

theorem batch_latch (s : MachineState) (left : Nat) (limit : left<LENGTH) (pc : s.pc=pcAt 349)
    (count : s.getReg .x22=W (left+1)) :
    Runs s (batchAfterLatch s) 2 2 ∧ (batchAfterLatch s).pc=pcAt (if 0<left then 144 else 351) ∧
      (batchAfterLatch s).getReg .x22=W left ∧ (batchAfterLatch s).mem=s.mem ∧
      ∀ r,r≠.x22→(batchAfterLatch s).getReg r=s.getReg r := by
  have less : left<18446744073709551616 := by change left<16777216 at limit;omega
  have dec : s.regs .x22+18446744073709551615#64=W left := by
    change s.getReg .x22+(-1#64)=_
    rw [count,←BitVec.sub_eq_add_neg];exact BitVec.ofNat_sub_ofNat_of_le _ 1 (by decide) (by omega)
  have nonzero (h : 0<left) : W left≠0#64 := by intro eq;have e:=congrArg BitVec.toNat eq;simp [W,Nat.mod_eq_of_lt less] at e;omega
  let u:=execInstrBr s (.ADDI .x22 .x22 4095)
  have ip : u.pc=pcAt 350 := by change s.pc+4=_;rw [pc];rfl
  have value : u.getReg .x22=W left := dec
  have flag : (u.getReg .x22 != u.getReg .x0)=decide (0<left) := by
    change (u.getReg .x22 != 0#64)=_
    rw [value]
    by_cases h : 0<left
    · simpa only [h,decide_true] using bne_iff_ne.mpr (nonzero h)
    · rw [show left=0 by omega];decide
  have last : batchAfterLatch s=u.setPC (pcAt (if 0<left then 144 else 351)) := by
    change (if u.getReg .x22 != u.getReg .x0 then u.setPC (u.pc+signExtend13 7368) else u.setPC (u.pc+4))=_
    rw [flag,ip];by_cases h : 0<left <;> simp only [h,decide_true,decide_false,Bool.false_eq_true,ite_true,ite_false] <;> rfl
  have ready : pathReady s batchLatchPath := ⟨pc,rfl,rfl,ip,rfl,rfl,True.intro⟩
  refine ⟨path_run _ true _ _ (by decide +kernel) ready,?_,?_,?_,?_⟩
  · rw [last];rfl
  · rw [last];exact value
  · rw [last];rfl
  intro r ne;rw [last]
  exact MachineState.getReg_setPC.trans (MachineState.getReg_setPC.trans (MachineState.getReg_setReg_ne _ _ _ _ ne.symm))


def markPath : PathCode := [(347,.ADD .x6 .x21 .x14),(348,.SB .x6 .x26 0)]
theorem mark_run (s : MachineState) (j : Nat) (bound : j<342) (pc : s.pc=pcAt 347)
    (base : s.getReg .x21=W 1024) (idx : s.getReg .x14=W j) (one : s.getReg .x26=1) :
    let t:=pathEnd s markPath
    Runs s t 2 2 ∧ t.pc=pcAt 349 ∧ t.mem=(withMark s j).mem ∧ ∀ r,r≠.x6 → t.getReg r=s.getReg r := by
  let u:=execInstrBr s (.ADD .x6 .x21 .x14)
  have ip : u.pc=pcAt 348 := by change s.pc+4=_;rw [pc];rfl
  have dst : u.getReg .x6+0#64=W (1024+j) := by
    change s.getReg .x21+s.getReg .x14+0#64=_;rw [base,idx,BitVec.add_zero];exact (BitVec.ofNat_add ..).symm
  have ok : memoryArgumentsValid u (.SB .x6 .x26 0)=true := by
    change accessValid (u.getReg .x6+0#64) 1=true;rw [dst]
    apply access_ok <;> first | omega | (change _≤2^36;omega)
  have store : ordinaryStep u (.base (.SB .x6 .x26 0))=some (execInstrBr u (.SB .x6 .x26 0)) := by
    simp only [ordinaryStep,ok,↓reduceIte]
  have ready : pathReady s markPath:=⟨pc,rfl,rfl,ip,store,rfl,True.intro⟩
  refine ⟨path_run _ true _ _ (by decide +kernel) ready,?_,?_,?_⟩
  · change u.pc+4=_;rw [ip];rfl
  · change (u.setByte (u.getReg .x6+0#64) ((s.getReg .x26).truncate 8)).mem=_
    rw [dst,one];rfl
  · intro r ne
    exact (MachineState.getReg_setPC.trans (show (u.setByte _ _).getReg r=u.getReg r from rfl)).trans
      (MachineState.getReg_setPC.trans (MachineState.getReg_setReg_ne _ _ _ _ ne.symm))
end CommitGolfCandidate.S5Machine.Open
