import CommitGolfCandidate.S5Code
namespace CommitGolfCandidate.S5Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

abbrev PathCode := List (Nat × Instr)

def matchesWord (pg : Program) (x : Nat × Instr) : Bool :=
  if h : x.1 < words pg then decodeInstruction (atWord pg ⟨x.1,h⟩) == some (.base x.2) else false

private theorem trace_site {pg x} (good : matchesWord pg x = true) : Site pg x.1 x.2 := by
  unfold matchesWord at good
  split at good
  next h => exact site h (beq_iff_eq.mp good)
  next => contradiction

def pathEnd (s : MachineState) : PathCode → MachineState
  | [] => s
  | (_,op)::rest => pathEnd (execInstrBr s op) rest

def pathReady (s : MachineState) : PathCode → Prop
  | [] => True
  | (i,op)::rest => s.pc=pcAt i ∧ ordinaryStep s (.base op)=some (execInstrBr s op) ∧
    instructionCycles (.base op)=1 ∧ pathReady (execInstrBr s op) rest

theorem path_run (pg : Program) (coins : Bool) (s : MachineState) (code : PathCode)
    (sites : code.all (matchesWord pg)) (ok : pathReady s code) (fuel : Nat) :
    execute (image pg) (fuel+code.length) s coins =
      (do let out ← execute (image pg) fuel (pathEnd s code) coins; return out.charge code.length 0) := by
  induction code generalizing s with
  | nil => simp [pathEnd,Execution.charge]
  | cons x xs ih =>
    obtain ⟨pc,step,cost,ready⟩:=ok
    simp only [List.all_cons,Bool.and_eq_true] at sites
    have first:=execute_ordinary_step (image pg) (.base x.2) s (execInstrBr s x.2)
      (fuel+xs.length) coins (trace_site sites.1 s pc) step
    rw [List.length_cons,←Nat.add_assoc,first,ih _ sites.2 ready,cost]
    simp [pathEnd,Execution.charge,Nat.add_assoc,Nat.add_comm 1]
end CommitGolfCandidate.S5Machine
