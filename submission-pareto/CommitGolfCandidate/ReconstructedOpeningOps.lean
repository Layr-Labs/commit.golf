import CommitGolfCandidate.ReconstructedOpeningTrap
import CommitGolfCandidate.ReconstructedLeafModel

namespace CommitGolfCandidate.Reconstruction.OpeningOps
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel LeafSteps TwoPermutationPrototype.RV64
set_option maxRecDepth 8192
attribute [local irreducible] ArtifactEncoding.decode execute

/-- Register expressions of the straight-line sections of the linked encoder. -/
inductive Expr where
  | lui (imm : BitVec 20)
  | addi (a : Reg) (imm : BitVec 12)
  | andi (a : Reg) (imm : BitVec 12)
  | slli (a : Reg) (k : BitVec 6)
  | srli (a : Reg) (k : BitVec 6)
  | add (a b : Reg)
  | sub (a b : Reg)
  | subw (a b : Reg)
  | and (a b : Reg)
  | or (a b : Reg)
  | xor (a b : Reg)
  | sll (a b : Reg)
  | srl (a b : Reg)
  | mul (a b : Reg)
  | mulhu (a b : Reg)
  | xori (a : Reg) (imm : BitVec 12)
  | sltu (a b : Reg)

def Expr.instr (rd : Reg) : Expr → Instr
  | .lui i => .LUI rd i
  | .addi a i => .ADDI rd a i
  | .andi a i => .ANDI rd a i
  | .slli a k => .SLLI rd a k
  | .srli a k => .SRLI rd a k
  | .add a b => .ADD rd a b
  | .sub a b => .SUB rd a b
  | .subw a b => .SUBW rd a b
  | .and a b => .AND rd a b
  | .or a b => .OR rd a b
  | .xor a b => .XOR rd a b
  | .sll a b => .SLL rd a b
  | .srl a b => .SRL rd a b
  | .mul a b => .MUL rd a b
  | .mulhu a b => .MULHU rd a b
  | .xori a i => .XORI rd a i
  | .sltu a b => .SLTU rd a b

def Expr.eval (r : Reg → Word) : Expr → Word
  | .lui i => ((i.zeroExtend 32 <<< 12).signExtend 64)
  | .addi a i => r a + signExtend12 i
  | .andi a i => r a &&& signExtend12 i
  | .slli a k => r a <<< k.toNat
  | .srli a k => r a >>> k.toNat
  | .add a b => r a + r b
  | .sub a b => r a - r b
  | .subw a b => ((r a).truncate 32 - (r b).truncate 32).signExtend 64
  | .and a b => r a &&& r b
  | .or a b => r a ||| r b
  | .xor a b => r a ^^^ r b
  | .sll a b => r a <<< ((r b).toNat % 64)
  | .srl a b => r a >>> ((r b).toNat % 64)
  | .mul a b => r a * r b
  | .mulhu a b => rv64_mulhu (r a) (r b)
  | .xori a i => r a ^^^ signExtend12 i
  | .sltu a b => if (r a).ult (r b) then 1 else 0

theorem assign (o : Oracle) (m : Model) (rd : Reg) (e : Expr) :
    Contract o [e.instr rd] m (m.set rd (e.eval m.reg)) := by
  intro s fits
  let t := (s.setReg rd (e.eval m.reg)).setPC (s.pc+4)
  have step : ordinaryStep s (.base (e.instr rd)) = some t := by
    cases e <;> simp only [Expr.instr,Expr.eval,ordinaryStep,memoryArgumentsValid,memAccess,
      ite_true,execInstrBr,fits.registers,t]
  exact ⟨t,Run.one (.ordinary _ _ _ step rfl),(fits.reg rd _).pc _⟩

/-- Each address annotation is a word number. Validity checks it against
the actual register-plus-immediate byte address and the RV64 address limit. -/
inductive Op where
  | reg (rd : Reg) (e : Expr)
  | ld (rd rs : Reg) (imm : BitVec 12) (w : Nat)
  | sd (rs rv : Reg) (imm : BitVec 12) (w : Nat)

def Op.instr : Op → Instr
  | .reg rd e => e.instr rd
  | .ld rd rs i _ => .LD rd rs i
  | .sd rs rv i _ => .SD rs rv i

def Op.apply (m : Model) : Op → Model
  | .reg rd e => m.set rd (e.eval m.reg)
  | .ld rd _ _ w => m.set rd (m.mem w)
  | .sd _ rv _ w => m.store w (m.reg rv)

def Op.Valid (m : Model) : Op → Prop
  | .reg .. => True
  | .ld _ rs i w | .sd rs _ i w => w<2^33 ∧ m.reg rs+signExtend12 i=wordAddress w

def Checked (m : Model) : List Op → Prop
  | [] => True
  | a::ops => a.Valid m ∧ Checked (a.apply m) ops

theorem checked_run (o : Oracle) (m : Model) (ops : List Op) (ok : Checked m ops) :
    Contract o (ops.map Op.instr) m (ops.foldl (fun a i => i.apply a) m) := by
  induction ops generalizing m with
  | nil => exact LeafModel.empty _ _
  | cons i tail ih =>
    obtain ⟨here,rest⟩ := ok
    have single : Contract o [i.instr] m (i.apply m) := by
      cases i with
      | reg rd e => exact assign o m rd e
      | ld rd rs imm w => exact LeafModel.load _ _ _ _ _ _ here.1 here.2
      | sd rs rv imm w => exact LeafModel.store _ _ _ _ _ _ here.1 here.2
    exact LeafModel.combine single (ih _ rest)

def consecutive (start : Nat) : List Instr → HonestMachine.Trace
  | [] => []
  | i::rest => (start,i)::consecutive (start+1) rest

theorem segment (o : Oracle) (image : Image) (ops : List Instr) (s t : MachineState)
    (start : Nat) (atStart : s.pc = CommitBlocks.addr start) (run : Run o ops s t)
    (fetches : HonestMachine.Fetched image (consecutive start ops)) :
    CommitExact.Segment o image ops.length s t := by
  induction run generalizing start with
  | nil => exact CommitExact.empty _ _ _
  | @cons op ops s t u step tail ih =>
    have fetch := fetches start op (List.mem_cons_self) s atStart
    have one : CommitExact.Segment o image 1 s t := by
      cases step with
      | ordinary _ _ _ valid _ => exact CommitExact.plain _ _ _ _ _ fetch valid
      | permute _ _ _ room fits src dst mode len kind =>
        exact CommitExact.permutation _ _ _ _ _ room fits src dst mode len kind fetch
    have loc := (step.advance.trans (congrArg (·+4) atStart)).trans (CommitBlocks.addr_next start).symm
    have sub := ih (start+1) loc (fun j i h => fetches j i (List.mem_cons_of_mem _ h))
    simpa only [List.length_cons,Nat.add_comm 1] using CommitExact.compose one sub

end CommitGolfCandidate.Reconstruction.OpeningOps
