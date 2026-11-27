import CommitGolfCandidate.R1bMachine

namespace CommitGolfCandidate.R1b.Machine.Sym
open CommitGolfCandidate.R1bPC (pcAt pc_succ)
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

inductive Bin where | add | mul | and | xor | shl | shr | sub | bor | divu | remu deriving DecidableEq

def Bin.apply : Bin → Word → Word → Word
  | .add,a,b => a+b | .mul,a,b => a*b | .and,a,b => a &&& b | .xor,a,b => a ^^^ b
  | .sub,a,b=>a-b | .bor,a,b=>a ||| b | .divu,a,b=>rv64_divu a b | .remu,a,b=>rv64_remu a b
  | .shl,a,b => a <<< b.toNat | .shr,a,b => a >>> b.toNat

inductive Expr where
  | reg (r : Reg) | lit (w : Word) | op (b : Bin) (x y : Expr) | load (addr : Expr) | byteLoad (addr : Expr)
deriving DecidableEq

def Expr.eval (s : MachineState) : Expr → Word
  | .reg r => s.getReg r | .lit w => w | .op b x y => b.apply (x.eval s) (y.eval s)
  | .load a => s.getMem (a.eval s)
  | .byteLoad a => (s.getByte (a.eval s)).zeroExtend 64

def mkOp (b : Bin) : Expr → Expr → Expr
  | .lit a,.lit c => .lit (b.apply a c)
  | x,y => .op b x y

theorem eval_mkOp (s : MachineState) (b : Bin) (x y : Expr) :
    (mkOp b x y).eval s = b.apply (x.eval s) (y.eval s) := by cases x <;> cases y <;> rfl

inductive Calc where
  | addi (d r : Reg) (i : BitVec 12) | andi (d r : Reg) (i : BitVec 12) | xori (d r : Reg) (i : BitVec 12)
  | slli (d r : Reg) (i : BitVec 6) | srli (d r : Reg) (i : BitVec 6)
  | sub (d a b : Reg) | bor (d a b : Reg) | band (d a b : Reg) | bxor (d a b : Reg)
  | divu (d a b : Reg) | remu (d a b : Reg) | lbu (d r : Reg) (i : BitVec 12)
  | add (d a b : Reg) | mul (d a b : Reg) | ld (d r : Reg) (i : BitVec 12)
deriving DecidableEq

def Calc.instr : Calc → Instr
  | .sub d a b=>.SUB d a b | .bor d a b=>.OR d a b | .band d a b=>.AND d a b | .bxor d a b=>.XOR d a b
  | .divu d a b=>.DIVU d a b | .remu d a b=>.REMU d a b | .lbu d r i=>.LBU d r i
  | .addi d r i => .ADDI d r i | .andi d r i => .ANDI d r i | .xori d r i => .XORI d r i
  | .slli d r i => .SLLI d r i | .srli d r i => .SRLI d r i | .add d a b => .ADD d a b
  | .mul d a b => .MUL d a b | .ld d r i => .LD d r i

def Calc.dst : Calc → Reg
  | .addi d .. | .andi d .. | .xori d .. | .slli d .. | .srli d .. | .add d .. | .mul d .. | .ld d .. | .sub d .. | .bor d .. | .band d .. | .bxor d .. | .divu d .. | .remu d .. | .lbu d .. => d

def Calc.value (f : Reg → Expr) : Calc → Expr
  | .sub _ a b=>mkOp .sub (f a) (f b) | .bor _ a b=>mkOp .bor (f a) (f b)
  | .band _ a b=>mkOp .and (f a) (f b) | .bxor _ a b=>mkOp .xor (f a) (f b)
  | .divu _ a b=>mkOp .divu (f a) (f b) | .remu _ a b=>mkOp .remu (f a) (f b)
  | .lbu _ r i=>.byteLoad (mkOp .add (f r) (.lit (signExtend12 i)))
  | .addi _ r i => mkOp .add (f r) (.lit (signExtend12 i))
  | .andi _ r i => mkOp .and (f r) (.lit (signExtend12 i))
  | .xori _ r i => mkOp .xor (f r) (.lit (signExtend12 i))
  | .slli _ r i => mkOp .shl (f r) (.lit (BitVec.ofNat 64 i.toNat))
  | .srli _ r i => mkOp .shr (f r) (.lit (BitVec.ofNat 64 i.toNat))
  | .add _ a b => mkOp .add (f a) (f b) | .mul _ a b => mkOp .mul (f a) (f b)
  | .ld _ r i => .load (mkOp .add (f r) (.lit (signExtend12 i)))

def Calc.reads (f : Reg → Expr) : Calc → List (Expr×Nat)
  | .ld _ r i => [(mkOp .add (f r) (.lit (signExtend12 i)),8)]
  | .lbu _ r i => [(mkOp .add (f r) (.lit (signExtend12 i)),1)]
  | _ => []

def bump (f : Reg → Expr) (c : Calc) := fun r => if c.dst=r then c.value f else f r
def original : Reg → Expr := fun r => if r=.x0 then .lit 0 else .reg r

def requirements (f : Reg → Expr) : List Calc → List (Expr×Nat)
  | [] => [] | c::cs => c.reads f ++ requirements (bump f c) cs

def live (origin s : MachineState) (f : Reg → Expr) := ∀ r, s.getReg r=(f r).eval origin

private theorem finite_sh (n : BitVec 6) : (BitVec.ofNat 64 n.toNat).toNat=n.toNat := by
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt];have h:=n.isLt;omega

private theorem instruction_state (c : Calc) (s origin : MachineState) (f : Reg → Expr)
    (regs : live origin s f) (mem : s.mem=origin.mem) :
    execInstrBr s c.instr = (s.setReg c.dst ((c.value f).eval origin)).setPC (s.pc+4) := by
  have read (r : Reg) : s.getReg r=(f r).eval origin := regs r
  cases c <;> simp only [Calc.instr,Calc.value,Calc.dst,execInstrBr,eval_mkOp,Bin.apply,Expr.eval,finite_sh,read,MachineState.getByte,MachineState.getMem,mem]

private theorem step_regs (c : Calc) (s origin : MachineState) (f : Reg → Expr)
    (regs : live origin s f) (mem : s.mem=origin.mem) (nz : c.dst≠.x0) :
    live origin (execInstrBr s c.instr) (bump f c) := by
  intro r
  rw [instruction_state c s origin f regs mem,MachineState.getReg_setPC]
  by_cases same : c.dst=r
  · subst r; simp only [bump,if_pos rfl,if_true,MachineState.getReg_setReg_eq nz]
  · rw [MachineState.getReg_setReg_ne _ _ _ _ same];simpa only [bump,if_neg same] using regs r

private theorem calc_access (c : Calc) (s origin : MachineState) (f : Reg → Expr) (regs : live origin s f)
    (safe : ∀ a ∈ c.reads f, accessValid (a.1.eval origin) a.2=true) :
    ordinaryStep s (.base c.instr) = some (execInstrBr s c.instr) := by
  cases c <;> try rfl
  all_goals
    rename_i d r i
    have ok := safe _ (List.mem_cons_self ..)
    first
    | have addr : memoryArgumentsValid s (.LD d r i)=true := by
        change accessValid (s.getReg r+signExtend12 i) 8=true
        rw [regs r];simpa only [eval_mkOp,Bin.apply,Expr.eval] using ok
      simp only [Calc.instr,ordinaryStep,addr,↓reduceIte]
    | have addr : memoryArgumentsValid s (.LBU d r i)=true := by
        change accessValid (s.getReg r+signExtend12 i) 1=true
        rw [regs r];simpa only [eval_mkOp,Bin.apply,Expr.eval] using ok
      simp only [Calc.instr,ordinaryStep,addr,↓reduceIte]

def evaluated (cs : List Calc) (s : MachineState) := (cs.map Calc.instr).foldl execInstrBr s
def price (cs : List Calc) := (cs.map fun c => instructionCycles (.base c.instr)).sum

theorem evaluate_block (img : Code) (cs : List Calc) (start : Nat) (s origin : MachineState) (f : Reg → Expr)
    (regs : live origin s f) (mem : s.mem=origin.mem) (pc : s.pc=pcAt start)
    (bound : start+cs.length ≤ img.count) (nz : ∀ c ∈ cs, c.dst≠.x0)
    (valid : ∀ a ∈ requirements f cs, accessValid (a.1.eval origin) a.2=true)
    (code : ∀ j (hj : j<cs.length), decodeInstruction (img.word (start+j))=some (.base cs[j].instr)) :
    let t := evaluated cs s
    Runs img s t cs.length (price cs) ∧ live origin t (cs.foldl bump f) ∧ t.mem=s.mem ∧ t.pc=pcAt (start+cs.length) := by
  induction cs generalizing start s f with
  | nil => exact ⟨Runs.refl img s,regs,rfl,by simpa [evaluated] using pc⟩
  | cons c cs ih =>
    let t := execInstrBr s c.instr
    have state := instruction_state c s origin f regs mem
    have preserve : t.mem=s.mem := by
      change (execInstrBr s c.instr).mem=_;rw [state];cases c.dst <;> rfl
    have nextPC : t.pc=pcAt (start+1) := by change (execInstrBr s c.instr).pc=_;rw [state,pc,pc_succ];rfl
    have step := one (c:=img) (by simp only [List.length_cons] at bound;omega) pc c.instr
      (code 0 (by simp)) (calc_access c s origin f regs (fun a h => valid a (List.mem_append_left _ h)))

    have tail := ih (start+1) t (bump f c) (step_regs c s origin f regs mem (nz c (by simp)))
      (preserve.trans mem) nextPC (by simp only [List.length_cons] at bound;omega)
      (fun x h => nz x (List.mem_cons_of_mem _ h)) (fun a h => valid a (List.mem_append_right _ h))
      (fun j hj => by rw [show start+1+j=start+(j+1) by omega]; exact code (j+1) (by simp;omega))
    refine ⟨?_,tail.2.1,tail.2.2.1.trans preserve,?_⟩
    · simpa only [evaluated,List.map_cons,List.foldl_cons,price,List.sum_cons,List.length_cons,
        Nat.add_comm 1 cs.length] using step.trans tail.1
    · exact tail.2.2.2.trans (congrArg pcAt (by simp only [List.length_cons];omega))

end CommitGolfCandidate.R1b.Machine.Sym
