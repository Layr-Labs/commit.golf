import CommitGolfCandidate.Stage3cCheckNarrow
import CommitGolfCandidate.Stage3cCheckFlow
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
def preservedBy (q : Reg) : Instr→Bool
  | .LD d .. | .LBU d .. | .LHU d .. | .ADDI d .. | .LUI d .. | .SUB d .. | .ADD d .. | .MUL d .. |
    .SLL d .. | .SLLI d .. | .SRL d .. | .SRLI d .. | .OR d .. | .AND d .. | .ANDI d .. | .XORI d .. |
    .JAL d .. | .JALR d .. | .DIVU d .. | .REMU d .. => d != q
  | .SB .. | .SD .. | .SH .. | .SW .. | .BLTU .. | .BGEU .. | .BEQ .. | .BNE ..=>true
  | _=>false
theorem reg_after (s : MachineState) (q : Reg) (op : Instr) (safe : preservedBy q op) : (execInstrBr s op).getReg q=s.getReg q := by
  cases op <;> simp only [preservedBy,bne_iff_ne,Bool.false_eq_true] at safe
  all_goals first
    | exact MachineState.getReg_setPC.trans (MachineState.getReg_setReg_ne _ _ _ _ safe)
    | (simp only [execInstrBr];split <;> exact MachineState.getReg_setPC)
    | (cases q <;> rfl)
theorem reg_path (s : MachineState) (ops : PathCode) (q : Reg) (safe : ops.all (fun i=>preservedBy q i.2)) :
    (pathEnd s ops).getReg q=s.getReg q := by
  induction ops generalizing s with
  | nil=>rfl
  | cons x xs ih=>
    simp only [List.all_cons,Bool.and_eq_true] at safe
    exact (ih _ safe.2).trans (reg_after _ _ _ safe.1)
def parentLive (r : Reg) := r∉([.x0,.x5,.x6,.x7,.x10,.x11,.x12,.x13,.x28,.x29,.x30,.x31] : List Reg)
def ParentPreserves (s t : MachineState) := ∀ r,parentLive r→t.getReg r=s.getReg r
theorem ParentPreserves.trans {s t u} (a : ParentPreserves s t) (b : ParentPreserves t u) : ParentPreserves s u :=
  fun r h=>(b r h).trans (a r h)
private theorem maskOps (q : Reg) (h : parentLive q) :
    (maskStart true).all (fun x=>preservedBy q x.2) ∧ (maskStart false).all (fun x=>preservedBy q x.2) ∧
    narrowStart.all (fun x=>preservedBy q x.2) ∧ maskSetup.all (fun x=>preservedBy q x.2) ∧ maskWrite.all (fun x=>preservedBy q x.2) ∧
    preservedBy q (.SH .x12 .x0 30) ∧ preservedBy q (.JAL .x0 32) := by
  cases q <;> first | decide | (exfalso;apply h;decide)
theorem wide_preserves (s : MachineState) (wide : Bool) : ParentPreserves s (projected s wide) := by
  intro q h;obtain ⟨a,b,_,_,_,sh,j⟩:=maskOps q h
  cases wide
  · exact (reg_after _ _ _ j).trans ((reg_after _ _ _ sh).trans (reg_path s _ q b))
  · exact reg_path s _ q a
theorem narrow_preserves (s : MachineState) : ParentPreserves s (writtenMask (preparedMask (pathEnd s narrowStart))) := by
  intro q h;obtain ⟨_,_,a,b,c,_,_⟩:=maskOps q h
  exact (reg_path _ _ q c).trans ((reg_path _ _ q b).trans (reg_path s _ q a))
theorem parent_prepare_preserves (s : MachineState) : ParentPreserves s (prepared s) := by
  intro q h;apply reg_path
  cases q <;> first | decide | (exfalso;apply h;decide)
end CommitGolfCandidate.Chained.BinaryMachine.Check
