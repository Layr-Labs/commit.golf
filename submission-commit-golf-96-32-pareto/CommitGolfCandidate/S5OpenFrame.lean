import CommitGolfCandidate.S5Trace
namespace CommitGolfCandidate.S5Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

/-- Register framing for the ordinary instructions used by the packing routine. -/
def keepsReg (r : Reg) : Instr → Bool
  | .LD d .. | .ADDI d .. | .SLL d .. | .SRL d .. | .ADD d .. | .SUB d .. | .OR d .. | .JAL d .. | .JALR d .. => d != r
  | .SD .. | .BGEU .. | .BLTU .. | .BEQ .. | .BNE .. => true
  | _ => false

private theorem keeps_reg (s : MachineState) (op : Instr) (r : Reg) (h : keepsReg r op) :
    (execInstrBr s op).getReg r=s.getReg r := by
  cases op <;> simp only [keepsReg,bne_iff_ne,Bool.false_eq_true] at h
  all_goals first
    | exact MachineState.getReg_setPC.trans (MachineState.getReg_setReg_ne _ _ _ _ h)
    | (simp only [execInstrBr];split <;> exact MachineState.getReg_setPC)
    | (cases r <;> rfl)

theorem path_keeps_reg (code : PathCode) (s : MachineState) (r : Reg)
    (keep : code.all fun x=>keepsReg r x.2) : (pathEnd s code).getReg r=s.getReg r := by
  induction code generalizing s with
  | nil=>rfl
  | cons x xs ih=>
    simp only [List.all_cons,Bool.and_eq_true] at keep
    exact (ih _ keep.2).trans (keeps_reg s x.2 r keep.1)
end CommitGolfCandidate.S5Machine
