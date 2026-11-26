import CommitGolfCandidate.S5OrdinaryRecord
namespace CommitGolfCandidate.S5Machine.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open CommitGolfCandidate.Late (Levels SaltTape record)

def latchPath : PathCode := [(987,.ADDI .x22 .x22 4095),(988,.BNE .x22 .x0 6244)]
def afterLatch (s : MachineState) := pathEnd s latchPath

theorem latch (s : MachineState) (left : Nat) (limit : left<LENGTH) (pc : s.pc=pcAt 987)
    (count : s.getReg .x22=W (left+1)) :
    Runs s (afterLatch s) 2 2 ∧ (afterLatch s).pc=pcAt (if 0<left then 501 else 989) ∧
      (afterLatch s).getReg .x22=W left ∧ (afterLatch s).mem=s.mem ∧
      ∀ r,r≠.x22→(afterLatch s).getReg r=s.getReg r := by
  have less : left<18446744073709551616 := by change left<16777216 at limit;omega
  have dec : s.regs .x22+18446744073709551615#64=W left := by
    change s.getReg .x22+(-1#64)=_
    rw [count,←BitVec.sub_eq_add_neg];exact BitVec.ofNat_sub_ofNat_of_le _ 1 (by decide) (by omega)
  have nonzero (h : 0<left) : W left≠0#64 := by intro eq;have e:=congrArg BitVec.toNat eq;simp [W,Nat.mod_eq_of_lt less] at e;omega
  let u:=execInstrBr s (.ADDI .x22 .x22 4095)
  have ip : u.pc=pcAt 988 := by change s.pc+4=_;rw [pc];rfl
  have value : u.getReg .x22=W left := dec
  have flag : (u.getReg .x22 != u.getReg .x0)=decide (0<left) := by
    change (u.getReg .x22 != 0#64)=_
    rw [value]
    by_cases h : 0<left
    · simpa only [h,decide_true] using bne_iff_ne.mpr (nonzero h)
    · rw [show left=0 by omega];decide
  have last : afterLatch s=u.setPC (pcAt (if 0<left then 501 else 989)) := by
    change (if u.getReg .x22 != u.getReg .x0 then u.setPC (u.pc+signExtend13 6244) else u.setPC (u.pc+4))=_
    rw [flag,ip];by_cases h : 0<left <;> simp only [h,decide_true,decide_false,Bool.false_eq_true,ite_true,ite_false] <;> rfl
  have ready : pathReady s latchPath := ⟨pc,rfl,rfl,ip,rfl,rfl,True.intro⟩
  refine ⟨path_run _ true _ _ (by decide +kernel) ready,?_,?_,?_,?_⟩
  · rw [last];rfl
  · rw [last];exact value
  · rw [last];rfl
  intro r ne;rw [last]
  exact MachineState.getReg_setPC.trans (MachineState.getReg_setPC.trans (MachineState.getReg_setReg_ne _ _ _ _ ne.symm))

def records (xs : List Index) (tree : Levels) (s : SaltTape) : Nat→Nat→Proof
  | _,0=>[]
  | r,n+1=>normalBytes tree s (ix xs r)++records xs tree s (r+1) n

theorem record_length (t s i) : (normalBytes t s i).length=824 := normal_length ..

theorem records_length (xs t s r n) : (records xs t s r n).length=824*n := by
  induction n generalizing r with
  | zero=>rfl
  | succ n ih=>rw [records,List.length_append,record_length,ih];omega

theorem records_eq (xs : List Index) (tree : Levels) (s : SaltTape) (r n : Nat) (bound : r+n≤xs.length) :
    records xs tree s r n=((xs.drop r).take n).flatMap (normalBytes tree s) := by
  induction n generalizing r with
  | zero=>simp [records]
  | succ n ih=>
    have hr : r<xs.length := by omega
    have hd : xs.drop r=ix xs r :: xs.drop (r+1) := by
      rw [List.drop_eq_getElem_cons hr];simp [ix,List.getElem?_eq_getElem hr]
    rw [records,hd,List.take_succ_cons,List.flatMap_cons,ih (r+1) (by omega)]

end CommitGolfCandidate.S5Machine.Open
