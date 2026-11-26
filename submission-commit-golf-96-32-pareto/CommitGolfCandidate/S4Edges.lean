import CommitGolfCandidate.S4Machine
namespace CommitGolfCandidate.S4.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (pcAt pc_succ)

def stands (c : Code) (n : Nat) (op : Instr) : Bool :=
  match decodeInstruction (c.word n) with | some (.base actual)=>decide (actual=op) | _=>false
theorem stood {c : Code} {n : Nat} {op : Instr} (h : stands c n op) : decodeInstruction (c.word n)=some (.base op) := by
  unfold stands at h;split at h
  · next actual e=>rw [e,of_decide_eq_true h]
  · contradiction

inductive Edge | jump | eqv | neq deriving DecidableEq
structure Control where
  pc : Nat
  target : Nat
  kind : Edge
  lhs : Reg:=.x0
  rhs : Reg:=.x0
deriving DecidableEq

def Control.off (e : Control) (width : Nat) := BitVec.ofInt width (4*((e.target : Int)-(e.pc : Int)))
def Control.instr (e : Control) : Instr := match e.kind with
  | .jump=>.JAL .x0 (e.off 21) | .eqv=>.BEQ e.lhs e.rhs (e.off 13) | .neq=>.BNE e.lhs e.rhs (e.off 13)
def Control.taken (e : Control) (s : MachineState) : Bool := match e.kind with
  | .jump=>true | .eqv=>s.getReg e.lhs==s.getReg e.rhs | .neq=>s.getReg e.lhs != s.getReg e.rhs
def Control.dest (e : Control) (s : MachineState) := if e.taken s then e.target else e.pc+1

def Control.valid (c : Code) (e : Control) := e.pc<c.count ∧ stands c e.pc e.instr ∧
  (match e.kind with | .jump=>pcAt e.pc+signExtend21 (e.off 21) | _=>pcAt e.pc+signExtend13 (e.off 13))=pcAt e.target
instance (c : Code) (e : Control) : Decidable (e.valid c) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem Control.run (e : Control) (c : Code) (s : MachineState) (pc : s.pc=pcAt e.pc) (valid : e.valid c) :
    Runs c s (s.setPC (pcAt (e.dest s))) 1 1 := by
  obtain ⟨hn,enc,target⟩:=valid
  have price : instructionCycles (.base e.instr)=1:=by unfold Control.instr;cases e.kind <;> rfl
  suffices h : Runs c s (s.setPC (pcAt (e.dest s))) 1 (instructionCycles (.base e.instr)) by simpa only [price] using h
  apply one hn pc _ (stood enc)
  unfold Control.dest Control.taken Control.instr
  cases ek : e.kind <;> simp only [ek] at target
  · simp only [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,pc,target,ite_true];rfl
  · change some (if s.getReg e.lhs==s.getReg e.rhs then s.setPC (s.pc+signExtend13 (e.off 13)) else s.setPC (s.pc+4))=_
    rw [pc,target,←pc_succ];split <;> rfl
  · change some (if s.getReg e.lhs != s.getReg e.rhs then s.setPC (s.pc+signExtend13 (e.off 13)) else s.setPC (s.pc+4))=_
    rw [pc,target,←pc_succ];split <;> rfl
end CommitGolfCandidate.S4.Machine
