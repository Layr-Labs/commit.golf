import CommitGolfCandidate.LateCheckMicro
import CommitGolfCandidate.LateOpenExpressions
namespace CommitGolfCandidate.Late.Check.Micro
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open CommitGolfCandidate.Late.Open (Calc Bin Expr mkOp eval_mkOp live bump original requirements evaluated price)

private theorem finite_sh (n : BitVec 6) : (BitVec.ofNat 64 n.toNat).toNat=n.toNat := by
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt];have h:=n.isLt;omega

private theorem instruction_state (c : Calc) (s origin : MachineState) (f : Reg → Expr)
    (regs : live origin s f) (mem : s.mem=origin.mem) :
    execInstrBr s c.instr = (s.setReg c.dst ((c.value f).eval origin)).setPC (s.pc+4) := by
  have read (r : Reg) : s.getReg r=(f r).eval origin := regs r
  cases c <;> simp only [Calc.instr,Calc.value,Calc.dst,execInstrBr,eval_mkOp,Bin.apply,Expr.eval,finite_sh,read,MachineState.getMem,mem]

private theorem step_regs (c : Calc) (s origin : MachineState) (f : Reg → Expr)
    (regs : live origin s f) (mem : s.mem=origin.mem) (nz : c.dst≠.x0) :
    live origin (execInstrBr s c.instr) (bump f c) := by
  intro r
  rw [instruction_state c s origin f regs mem,MachineState.getReg_setPC]
  by_cases same : c.dst=r
  · subst r; simp only [bump,if_pos rfl,if_true,MachineState.getReg_setReg_eq nz]
  · rw [MachineState.getReg_setReg_ne _ _ _ _ same];simpa only [bump,if_neg same] using regs r

private theorem calc_access (c : Calc) (s origin : MachineState) (f : Reg → Expr) (regs : live origin s f)
    (safe : ∀ a ∈ c.reads f, accessValid (a.eval origin) 8=true) :
    ordinaryStep s (.base c.instr) = some (execInstrBr s c.instr) := by
  cases c <;> try rfl
  rename_i d r i
  have ok := safe _ (List.mem_cons_self ..)
  have addr : memoryArgumentsValid s (.LD d r i)=true := by
    change accessValid (s.getReg r+signExtend12 i) 8=true
    rw [regs r];simpa only [eval_mkOp,Bin.apply,Expr.eval] using ok
  simp only [Calc.instr,ordinaryStep,addr,↓reduceIte]

theorem evaluate_block (cs : List Calc) (start : Nat) (s origin : MachineState) (f : Reg → Expr)
    (regs : live origin s f) (mem : s.mem=origin.mem) (pc : s.pc=pcAt start)
    (bound : start+cs.length≤433) (nz : ∀ c ∈ cs, c.dst≠.x0)
    (valid : ∀ a ∈ requirements f cs, accessValid (a.eval origin) 8=true)
    (code : ∀ j (hj : j<cs.length), decodeInstruction (checkWord (start+j))=some (.base cs[j].instr)) :
    let t := evaluated cs s
    Runs s t cs.length (price cs) ∧ live origin t (cs.foldl bump f) ∧ t.mem=s.mem ∧ t.pc=pcAt (start+cs.length) := by
  induction cs generalizing start s f with
  | nil => exact ⟨Runs.refl s,regs,rfl,by simpa [evaluated] using pc⟩
  | cons c cs ih =>
    let t := execInstrBr s c.instr
    have state := instruction_state c s origin f regs mem
    have preserve : t.mem=s.mem := by
      change (execInstrBr s c.instr).mem=_;rw [state];cases c.dst <;> rfl
    have nextPC : t.pc=pcAt (start+1) := by change (execInstrBr s c.instr).pc=_;rw [state,pc,pc_succ];rfl
    have step := one start (by simp only [List.length_cons] at bound;omega) c.instr
      (code 0 (by simp)) s t pc (calc_access c s origin f regs (fun a h => valid a (List.mem_append_left _ h)))
    have tail := ih (start+1) t (bump f c) (step_regs c s origin f regs mem (nz c (by simp)))
      (preserve.trans mem) nextPC (by simp only [List.length_cons] at bound;omega)
      (fun x h => nz x (List.mem_cons_of_mem _ h)) (fun a h => valid a (List.mem_append_right _ h))
      (fun j hj => by rw [show start+1+j=start+(j+1) by omega]; exact code (j+1) (by simp;omega))
    refine ⟨?_,tail.2.1,tail.2.2.1.trans preserve,?_⟩
    · simpa only [evaluated,List.map_cons,List.foldl_cons,price,List.sum_cons,List.length_cons,
        Nat.add_comm 1 cs.length] using step.trans tail.1
    · exact tail.2.2.2.trans (congrArg pcAt (by simp only [List.length_cons];omega))

end CommitGolfCandidate.Late.Check.Micro
