import CommitGolfCandidate.S5CheckFlow
import CommitGolfCandidate.S5Gates
namespace CommitGolfCandidate.S5Machine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
inductive Rel | eq | ne | lt | ge deriving DecidableEq
def Rel.op (rel : Rel) (r t : Reg) (off : BitVec 13) : Instr:=match rel with
  | .eq=>.BEQ r t off | .ne=>.BNE r t off | .lt=>.BLTU r t off | .ge=>.BGEU r t off
def Rel.test (rel : Rel) (a b : Word) : Bool :=match rel with
  | .eq=>a==b | .ne=>a != b | .lt=>a.ult b | .ge=> !(a.ult b)
def offset13 (pc dest : Nat) :=BitVec.ofInt 13 (4*((dest:Int)-(pc:Int)))
def offset21 (pc dest : Nat) :=BitVec.ofInt 21 (4*((dest:Int)-(pc:Int)))
def BranchSite (pc dest : Nat) (rel : Rel) (r t : Reg) :=
  matchesWord .check (pc,rel.op r t (offset13 pc dest)) ∧ pcAt pc+signExtend13 (offset13 pc dest)=pcAt dest
instance (pc dest : Nat) (rel : Rel) (r t : Reg) : Decidable (BranchSite pc dest rel r t):=inferInstanceAs (Decidable (_∧_))

theorem branch (o : Oracle) (s : MachineState) (n dest : Nat) (rel : Rel) (r t : Reg) (valid : BranchSite n dest rel r t)
    (pc : s.pc=pcAt n) (b : Bool) (test : rel.test (s.getReg r) (s.getReg t)=b) :
    Flow o s (s.setPC (pcAt (if b then dest else n+1))) 1 0 := by
  obtain ⟨op,land⟩:=valid
  apply one_flow o pc (known op)
  cases rel <;> cases b <;> simp only [Rel.test] at test
  all_goals simp only [Rel.op,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,pc,pc_succ,land,ite_true,ite_false,Bool.false_eq_true] <;>
    try simp_all only [Bool.not_eq_true',Bool.not_eq_false',ite_true,ite_false,Bool.false_eq_true,not_true_eq_false,not_false_eq_true]

def JumpSite (pc target : Nat) (rd : Reg) := matchesWord .check (pc,.JAL rd (offset21 pc target)) ∧
  pcAt pc+signExtend21 (offset21 pc target)=pcAt target
instance (pc target : Nat) (rd : Reg) : Decidable (JumpSite pc target rd):=inferInstanceAs (Decidable (_∧_))
theorem jump (o : Oracle) (s : MachineState) (n dest : Nat) (r : Reg) (valid : JumpSite n dest r) (pc : s.pc=pcAt n) :
    Flow o s ((s.setReg r (pcAt (n+1))).setPC (pcAt dest)) 1 0 := by
  apply one_flow o pc (known valid.1)
  change some ((s.setReg r (s.pc+4)).setPC (s.pc+signExtend21 (offset21 n dest)))=_
  rw [pc,pc_succ,valid.2]

theorem imm_step (o : Oracle) (s : MachineState) (n : Nat) (d r : Reg) (imm : BitVec 12) (a : Word)
    (pc : s.pc=pcAt n) (op : Site .check n (.ADDI d r imm)) (eq : s.getReg r+signExtend12 imm=a) :
    Flow o s ((s.setReg d a).setPC (pcAt (n+1))) 1 0 := by
  apply one_flow o pc op;change some ((s.setReg d _).setPC (s.pc+4))=_;rw [pc,eq,pc_succ]
end CommitGolfCandidate.S5Machine.Check
