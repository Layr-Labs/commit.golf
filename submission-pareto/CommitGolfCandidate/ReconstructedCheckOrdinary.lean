import CommitGolfCandidate.ReconstructedCheckValues

namespace CommitGolfCandidate.Reconstruction.CheckOrdinary
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding Binding.Machine CheckValues CheckRecorded
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

inductive Arith where
  | rr (kind : Bin) (dst a b : Reg)
  | addi (dst a : Reg) (imm : BitVec 12)
  | addiw (dst a : Reg) (imm : BitVec 12)
  | slli (dst a : Reg) (imm : BitVec 6)
  | srli (dst a : Reg) (imm : BitVec 6)
  | lui (dst : Reg) (imm : BitVec 20)
  deriving Repr

def arithOp : Arith→Instruction
  | .rr .add rd a b => .base (.ADD rd a b)
  | .rr .bitOr rd a b => .base (.OR rd a b)
  | .rr .bitAnd rd a b => .base (.AND rd a b)
  | .rr .bitXor rd a b => .base (.XOR rd a b)
  | .rr .shl rd a b => .base (.SLL rd a b)
  | .rr .shr rd a b => .base (.SRL rd a b)
  | .rr .add32 rd a b => .word .add rd a b
  | .rr .sub32 rd a b => .word .sub rd a b
  | .rr .remu rd a b => .base (.REMU rd a b)
  | .addi rd a i => .base (.ADDI rd a i)
  | .addiw rd a i => .base (.ADDIW rd a i)
  | .slli rd a i => .base (.SLLI rd a i)
  | .srli rd a i => .base (.SRLI rd a i)
  | .lui rd i => .base (.LUI rd i)

def assignment (m : State) : Arith→Reg×Term
  | .rr op r a b => (r,applyOp op (m.get a) (m.get b))
  | .addi r a i => (r,applyOp .add (m.get a) (.lit (signExtend12 i)))
  | .addiw r a i => (r,applyOp .add32 (m.get a) (.lit (signExtend12 i)))
  | .slli r a i => (r,applyOp .shl (m.get a) (.lit (i.zeroExtend 64)))
  | .srli r a i => (r,applyOp .shr (m.get a) (.lit (i.zeroExtend 64)))
  | .lui r i => (r,.lit (((i.zeroExtend 32) <<< 12).signExtend 64))

private theorem small_shift (i : BitVec 6) : (i.zeroExtend 64).toNat %64=i.toNat := by
  have small := i.isLt
  change i.toNat <64 at small
  simp [BitVec.toNat_setWidth,Nat.mod_eq_of_lt small,Nat.mod_eq_of_lt (show i.toNat<2^64 by omega)]

theorem assigned (env : Env) (m : State) (s : MachineState) (h : Matches env m s) (op : Arith) :
    let result := assignment m op
    ordinaryStep s (arithOp op) = some ((s.setReg result.1 (result.2.val env)).setPC (m.pc+4)) := by
  cases op with
  | rr bin rd a b =>
    simp only [assignment,op_sound,←h.regs,←h.pc]
    cases bin <;> rfl
  | addi rd a i | addiw rd a i | slli rd a i | srli rd a i =>
    simp only [assignment,op_sound,←h.regs,←h.pc,Term.val,Bin.run,small_shift]
    rfl
  | lui rd i => rw [←h.pc];rfl

inductive Cond where | eq | ne | lt | ge deriving Repr

def Cond.test : Cond→Word→Word→Bool
  | .eq,a,b=>a==b
  | .ne,a,b=>a != b
  | .lt,a,b=>a.ult b
  | .ge,a,b=>!(a.ult b)

inductive Op where
  | arith (a : Arith)
  | ld (rd rs : Reg) (imm : BitVec 12)
  | sd (rs rt : Reg) (imm : BitVec 12)
  | branch (c : Cond) (a b : Reg) (off : BitVec 13)
  | jal (rd : Reg) (off : BitVec 21)
  deriving Repr

def Op.instr : Op→Instruction
  | .arith a => arithOp a
  | .ld rd rs i=>.base (.LD rd rs i)
  | .sd rs rt i=>.base (.SD rs rt i)
  | .branch .eq a b off=>.base (.BEQ a b off)
  | .branch .ne a b off=>.base (.BNE a b off)
  | .branch .lt a b off=>.base (.BLTU a b off)
  | .branch .ge a b off=>.base (.BGEU a b off)
  | .jal rd off=>.base (.JAL rd off)

def operand (m : State) (r : Reg) (i : BitVec 12) := applyOp .add (m.get r) (.lit (signExtend12 i))
def literal : Term→Option Word | .lit x=>some x | _=>none

def step (tab : Tables) (m : State) : Op→Option State
  | .arith a =>
    let v := assignment m a
    some {m.set v.1 v.2 with pc:=m.pc+4}
  | .ld rd rs i=>do
    let a ← address (operand m rs i)
    guard (tab.allowed a)
    return {m.set rd (look tab a m.writes) with pc:=m.pc+4}
  | .sd rs rt i=>do
    let a ← address (operand m rs i)
    guard (tab.allowed a)
    return {m with writes:=(a,m.get rt)::m.writes,pc:=m.pc+4}
  | .branch c a b off=>do
    let x ← literal (m.get a)
    let y ← literal (m.get b)
    return {m with pc:=if c.test x y then m.pc+signExtend13 off else m.pc+4}
  | .jal rd off=>some {m.set rd (.lit (m.pc+4)) with pc:=m.pc+signExtend21 off}

private theorem lit_val {t : Term} {v : Word} (env : Env) (eq : literal t=some v) : t.val env=v := by
  cases t <;> simp_all [literal,Term.val]

private theorem op_addr (env : Env) (m : State) (s : MachineState) (h : Matches env m s)
    (rs : Reg) (off : BitVec 12) {a : Loc} (eq : address (operand m rs off)=some a) :
    s.getReg rs+signExtend12 off=physical env a := by
  rw [address_sound env eq,operand,op_sound];change _=(m.get rs).val env+signExtend12 off
  rw [h.regs]

private theorem branch_effect (s : MachineState) (c : Cond) (a b : Reg) (off : BitVec 13) :
    ordinaryStep s (Op.branch c a b off).instr = some (s.setPC
      (if c.test (s.getReg a) (s.getReg b) then s.pc+signExtend13 off else s.pc+4)) := by
  cases c <;> simp [Op.instr,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,Cond.test] <;> split <;> simp_all

theorem sound (o : Oracle) (env : Env) (tab : Tables) (layout : Layout env tab)
    (m n : State) (s : MachineState) (h : Matches env m s) (safe : Safe tab m.writes)
    (op : Op) (found : fetch image s=some op.instr) (next : step tab m op=some n) :
    ∃ t, Segment o 1 s t [] ∧ Matches env n t ∧ Safe tab n.writes := by
  cases op with
  | arith a =>
    simp only [step,Option.some.injEq] at next
    subst n
    exact ⟨_,plain o _ _ _ found (assigned env m s h a),set_value env m s h _ _ _,safe⟩
  | jal rd off =>
    simp only [step,Option.some.injEq] at next
    subst n
    have run : ordinaryStep s (Op.jal rd off).instr =
        some ((s.setReg rd (m.pc+4)).setPC (m.pc+signExtend21 off)) := by rw [←h.pc];rfl
    exact ⟨_,plain o _ _ _ found run,set_value env m s h rd (.lit _) _,safe⟩
  | ld rd rs i =>
    cases eq : address (operand m rs i) with
    | none => simp [step,eq] at next
    | some a =>
      by_cases valid : tab.allowed a=true
      · simp [step,eq,valid] at next
        subst n
        have addr := op_addr env m s h rs i eq
        have value := look_sound env tab layout m.writes a valid safe
        have run : ordinaryStep s (Op.ld rd rs i).instr = some ((s.setReg rd ((look tab a m.writes).val env)).setPC (m.pc+4)) := by
          simp [Op.instr,ordinaryStep,memoryArgumentsValid,memAccess,addr,layout.safe _ valid,
            execInstrBr,h.pc,h.mem,value]
        exact ⟨_,plain o _ _ _ found run,set_value env m s h _ _ _,safe⟩
      · simp [step,eq,valid] at next
  | sd rs rt i =>
    cases eq : address (operand m rs i) with
    | none => simp [step,eq] at next
    | some a =>
      by_cases valid : tab.allowed a=true
      · simp [step,eq,valid] at next
        subst n
        have addr := op_addr env m s h rs i eq
        have run : ordinaryStep s (Op.sd rs rt i).instr = some ((s.setMem (physical env a) ((m.get rt).val env)).setPC (m.pc+4)) := by
          simp [Op.instr,ordinaryStep,memoryArgumentsValid,memAccess,addr,layout.safe _ valid,execInstrBr,h.pc,h.regs rt]
        refine ⟨_,plain o _ _ _ found run,set_word env m s h _ _ _,?_⟩
        intro p hp;rcases List.mem_cons.1 hp with rfl|rest
        · exact valid
        · exact safe _ rest
      · simp [step,eq,valid] at next
  | branch c a b off =>
    cases xa : literal (m.get a) with
    | none => simp [step,xa] at next
    | some x =>
      cases yb : literal (m.get b) with
      | none => simp [step,xa,yb] at next
      | some y =>
        simp [step,xa,yb] at next;subst n
        have run := branch_effect s c a b off
        rw [h.regs a,h.regs b,lit_val env xa,lit_val env yb,h.pc] at run
        exact ⟨_,plain o _ _ _ found run,set_pc env m s h _,safe⟩

end CommitGolfCandidate.Reconstruction.CheckOrdinary
