import CommitGolfCandidate.LateOpenCode

namespace CommitGolfCandidate.Late.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

inductive Bin where | add | mul | and | xor | shl | shr | sub deriving DecidableEq

def Bin.apply : Bin → Word → Word → Word
  | .add,a,b => a+b | .mul,a,b => a*b | .and,a,b => a &&& b | .xor,a,b => a ^^^ b
  | .shl,a,b => a <<< b.toNat | .shr,a,b => a >>> b.toNat | .sub,a,b => a-b

inductive Expr where
  | reg (r : Reg) | lit (w : Word) | op (b : Bin) (x y : Expr) | load (addr : Expr)
deriving DecidableEq

def Expr.eval (s : MachineState) : Expr → Word
  | .reg r => s.getReg r | .lit w => w | .op b x y => b.apply (x.eval s) (y.eval s)
  | .load a => s.getMem (a.eval s)

def mkOp (b : Bin) : Expr → Expr → Expr
  | .lit a,.lit c => .lit (b.apply a c)
  | x,y => .op b x y

theorem eval_mkOp (s : MachineState) (b : Bin) (x y : Expr) :
    (mkOp b x y).eval s = b.apply (x.eval s) (y.eval s) := by cases x <;> cases y <;> rfl

inductive Calc where
  | addi (d r : Reg) (i : BitVec 12) | andi (d r : Reg) (i : BitVec 12) | xori (d r : Reg) (i : BitVec 12)
  | slli (d r : Reg) (i : BitVec 6) | srli (d r : Reg) (i : BitVec 6)
  | add (d a b : Reg) | mul (d a b : Reg) | ld (d r : Reg) (i : BitVec 12) | sub (d a b : Reg)
deriving DecidableEq

def Calc.instr : Calc → Instr
  | .addi d r i => .ADDI d r i | .andi d r i => .ANDI d r i | .xori d r i => .XORI d r i
  | .slli d r i => .SLLI d r i | .srli d r i => .SRLI d r i | .add d a b => .ADD d a b
  | .mul d a b => .MUL d a b | .ld d r i => .LD d r i | .sub d a b => .SUB d a b

def Calc.dst : Calc → Reg
  | .addi d .. | .andi d .. | .xori d .. | .slli d .. | .srli d .. | .add d .. | .mul d .. | .ld d .. | .sub d .. => d

def Calc.value (f : Reg → Expr) : Calc → Expr
  | .addi _ r i => mkOp .add (f r) (.lit (signExtend12 i))
  | .andi _ r i => mkOp .and (f r) (.lit (signExtend12 i))
  | .xori _ r i => mkOp .xor (f r) (.lit (signExtend12 i))
  | .slli _ r i => mkOp .shl (f r) (.lit (BitVec.ofNat 64 i.toNat))
  | .srli _ r i => mkOp .shr (f r) (.lit (BitVec.ofNat 64 i.toNat))
  | .add _ a b => mkOp .add (f a) (f b) | .mul _ a b => mkOp .mul (f a) (f b) | .sub _ a b => mkOp .sub (f a) (f b)
  | .ld _ r i => .load (mkOp .add (f r) (.lit (signExtend12 i)))

def Calc.reads (f : Reg → Expr) : Calc → List Expr
  | .ld _ r i => [mkOp .add (f r) (.lit (signExtend12 i))]
  | _ => []

def bump (f : Reg → Expr) (c : Calc) := fun r => if c.dst=r then c.value f else f r
def original : Reg → Expr := fun r => if r=.x0 then .lit 0 else .reg r

def requirements (f : Reg → Expr) : List Calc → List Expr
  | [] => [] | c::cs => c.reads f ++ requirements (bump f c) cs

def live (origin s : MachineState) (f : Reg → Expr) := ∀ r, s.getReg r=(f r).eval origin

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

def evaluated (cs : List Calc) (s : MachineState) := (cs.map Calc.instr).foldl execInstrBr s
def price (cs : List Calc) := (cs.map fun c => instructionCycles (.base c.instr)).sum

theorem evaluate_block (cs : List Calc) (start : Nat) (s origin : MachineState) (f : Reg → Expr)
    (regs : live origin s f) (mem : s.mem=origin.mem) (pc : s.pc=pcAt start)
    (bound : start+cs.length≤406) (nz : ∀ c ∈ cs, c.dst≠.x0)
    (valid : ∀ a ∈ requirements f cs, accessValid (a.eval origin) 8=true)
    (code : ∀ j (hj : j<cs.length), decodeInstruction (openWord (start+j))=some (.base cs[j].instr)) :
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

end CommitGolfCandidate.Late.Open
