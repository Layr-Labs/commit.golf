import CommitGolfCandidate.S5ReadCursor
namespace CommitGolfCandidate.S5Machine.Reader
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W)
open Check (Flow)
inductive Select | word | chunk deriving DecidableEq
instance : Fintype Select:=⟨{.word,.chunk},by intro x;cases x <;> decide⟩
def Select.pc : Select→Nat | .word=>27 | .chunk=>34
def Select.stop : Select→Nat | .word=>61 | .chunk=>58
def Select.limit : Select→Nat | .word=>64 | .chunk=>32
def Select.src : Select→Reg | .word=>.x13 | .chunk=>.x31
def Select.dst : Select→Reg | .word=>.x31 | .chunk=>.x6
def Select.branch (p : Select) := Instr.BEQ p.src .x0 (BitVec.ofNat 13 (4*(p.stop-p.pc)))
def Select.code (p : Select) (short : Bool) : PathCode :=
  [(p.pc,p.branch),(p.pc+1,.ADDI p.dst .x0 (BitVec.ofNat 12 p.limit)),(p.pc+2,.BGEU p.src p.dst 8)]++
    if short then [(p.pc+3,.ADDI p.dst p.src 0)] else []
private theorem select_sites : ∀ p : Select,∀ b : Bool,(p.code b).all (matchesWord .check) := by decide +kernel

theorem select_zero (o : Oracle) (p : Select) (s : MachineState) (pc : s.pc=pcAt p.pc) (zero : s.getReg p.src=0) :
    Flow o s (s.setPC (pcAt p.stop)) 1 0 := by
  apply Check.one_flow o pc (Check.known ((by decide +kernel : ∀ r : Select,matchesWord .check (r.pc,r.branch)) p))
  change some (if s.getReg p.src == 0#64 then s.setPC (s.pc+signExtend13 (BitVec.ofNat 13 (4*(p.stop-p.pc)))) else s.setPC (s.pc+4))=_
  rw [zero,pc];cases p <;> rfl

theorem select_size (o : Oracle) (p : Select) (s : MachineState) (n : Nat) (pos : 0<n) (small : n<2^64)
    (pc : s.pc=pcAt p.pc) (count : s.getReg p.src=W n) :
    let short:=decide (n<p.limit)
    let t:=pathEnd s (p.code short)
    Flow o s t (if short then 4 else 3) 0 ∧ t.pc=pcAt (p.pc+4) ∧ t.getReg p.dst=W (min n p.limit) ∧ t.mem=s.mem ∧
      ∀ q,q≠p.dst→t.getReg q=s.getReg q := by
  let short:=decide (n<p.limit)
  let u:=s.setPC (pcAt (p.pc+1))
  let a:=execInstrBr u (.ADDI p.dst .x0 (BitVec.ofNat 12 p.limit))
  let b:=a.setPC (pcAt (if short then p.pc+3 else p.pc+4))
  have notz : s.getReg p.src ≠0#64 := by
    rw [count];intro v;have eq:=congrArg BitVec.toNat v;simp only [W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small,BitVec.toNat_zero] at eq;omega
  have after : execInstrBr s p.branch=u := by
    change (if s.getReg p.src == 0#64 then _ else s.setPC (s.pc+4))=_
    rw [beq_eq_false_iff_ne.mpr notz,pc,pc_succ];rfl
  have apc : a.pc=pcAt (p.pc+2):=by change pcAt (p.pc+1)+4=_;rw [pc_succ]
  have m : a.getReg p.dst=W p.limit := by cases p <;> rfl
  have unchanged (q : Reg) (ne : q≠p.dst) : a.getReg q=s.getReg q :=
    MachineState.getReg_setPC.trans ((MachineState.getReg_setReg_ne _ _ _ _ ne.symm).trans MachineState.getReg_setPC)
  have src : a.getReg p.src=W n:=(unchanged _ (by cases p <;> decide)).trans count
  have compare : (a.getReg p.src).ult (a.getReg p.dst)=short:=by
    rw [src,m];simp only [BitVec.ult,W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small,
      Nat.mod_eq_of_lt (show p.limit<2^64 by cases p <;> decide),short]
  have land : execInstrBr a (.BGEU p.src p.dst 8)=b:=by
    change (if ¬(a.getReg p.src).ult (a.getReg p.dst) then a.setPC (a.pc+signExtend13 8) else a.setPC (a.pc+4))=_
    rw [compare,apc];unfold b;cases p <;> cases short <;> rfl
  let fixedCode : PathCode := [(p.pc,p.branch),(p.pc+1,.ADDI p.dst .x0 (BitVec.ofNat 12 p.limit)),(p.pc+2,.BGEU p.src p.dst 8)]
  have work : pathReady s fixedCode:=by
    refine ⟨pc,?_,?_,?_,?_,?_,?_,?_,?_,True.intro⟩
    · cases p <;> rfl
    · cases p <;> rfl
    · rw [after];rfl
    · rfl
    · rfl
    · rw [after];exact apc
    · rfl
    · rfl
  have ending : pathEnd s (p.code false)=b := by
    simp only [Select.code,Bool.false_eq_true,ite_false,List.append_nil,pathEnd]
    rw [after]
    exact land
  have endingKeep : pathEnd s (p.code true)=execInstrBr b (.ADDI p.dst p.src 0) := by
    simp only [Select.code,ite_true,List.cons_append,List.nil_append,pathEnd]
    rw [after];exact congrArg (fun z=>execInstrBr z (.ADDI p.dst p.src 0)) land
  have pr : Flow o s b 3 0 := by
    have flow:=Check.path_flow o ((by decide +kernel : ∀ r : Select,(r.code false).all (matchesWord .check)) p) (show pathReady s (p.code false) from work)
    rw [ending] at flow;exact flow
  have bp : b.pc=pcAt (if short then p.pc+3 else p.pc+4):=rfl
  have frame (q : Reg) (ne : q≠p.dst) : b.getReg q=s.getReg q:=MachineState.getReg_setPC.trans (unchanged q ne)
  by_cases lower : n<p.limit
  · have yes : short=true:=decide_eq_true lower
    simp only [yes,decide_eq_true lower,ite_true] at bp ⊢
    let t:=execInstrBr b (.ADDI p.dst p.src 0)
    rw [endingKeep]
    have mov:=Check.one_flow o (t:=t) bp (Check.known ((by decide +kernel : ∀ r : Select,matchesWord .check (r.pc+3,.ADDI r.dst r.src 0)) p)) rfl
    refine ⟨pr.trans mov,?_,?_,?_,?_⟩
    · change b.pc+4=_;rw [bp,pc_succ]
    · have neq : p.dst≠.x0:=by cases p <;> decide
      simp only [t,execInstrBr,MachineState.getReg_setPC,MachineState.getReg_setReg_eq neq,show signExtend12 0=0#64 by rfl,
        BitVec.add_zero,Nat.min_eq_left lower.le];exact MachineState.getReg_setPC.trans src
    · cases p <;> rfl
    · intro q ne;exact MachineState.getReg_setPC.trans ((MachineState.getReg_setReg_ne _ _ _ _ ne.symm).trans (frame q ne))
  · have no : short=false:=decide_eq_false lower
    simp only [no,decide_eq_false lower,Bool.false_eq_true,ite_false] at bp ⊢
    rw [ending];exact ⟨pr,bp,by rw [Nat.min_eq_right (by omega)];exact MachineState.getReg_setPC.trans m,by cases p <;> rfl,frame⟩
end CommitGolfCandidate.S5Machine.Reader
