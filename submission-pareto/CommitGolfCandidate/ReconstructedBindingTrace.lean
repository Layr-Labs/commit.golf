import CommitGolfCandidate.ReconstructedBindingMachine

namespace CommitGolfCandidate.Reconstruction.Binding.Machine
open CommitGolf CommitGolf.Riscv OracleComp RiscvZkvm.Rv64
set_option maxRecDepth 8192

abbrev Trace := List (Nat × Instruction)

def effect (s : MachineState) : Instruction → MachineState
  | .base op => execInstrBr s op
  | .word op rd r t =>
    (s.setReg rd ((wordResult op ((s.getReg r).truncate 32) ((s.getReg t).truncate 32)).signExtend 64)).setPC (s.pc+4)
  | .sraiw rd r sh =>
    (s.setReg rd (((s.getReg r).truncate 32).sshiftRight sh.toNat |>.signExtend 64)).setPC (s.pc+4)

def enabled (s : MachineState) : Instruction → Bool
  | .base .ECALL | .base .EBREAK | .base (.CSRS ..) | .base (.LI ..) | .base (.MV ..) | .base .NOP => false
  | .base op => memoryArgumentsValid s op
  | _ => true

theorem enabled_step (s : MachineState) (op : Instruction) (ok : enabled s op = true) :
    ordinaryStep s op = some (effect s op) := by
  cases op with
  | base op => cases op <;> simp_all [ordinaryStep,enabled,effect]
  | word => rfl
  | sraiw => rfl

def valid : Trace → MachineState → Bool
  | [], _ => true
  | (i,op)::ops,s => s.pc == BitVec.ofNat 64 (4096+4*i) && enabled s op && valid ops (effect s op)

def last : Trace → MachineState → MachineState
  | [],s => s
  | (_,op)::ops,s => last ops (effect s op)

def cycles : Trace → Nat
  | [] => 0
  | (_,op)::ops => instructionCycles op + cycles ops

def Decoded (trace : Trace) := ∀ i op, (i,op) ∈ trace → ∀ s : MachineState,
  s.pc = BitVec.ofNat 64 (4096 + 4*i) → fetch image s = some op

theorem run_trace (trace : Trace) (s : MachineState) (fuel : Nat) (fetched : Decoded trace)
    (ok : valid trace s = true) :
    execute image (trace.length+fuel) s false =
      (do let result ← execute image fuel (last trace s) false; return result.charge (cycles trace) 0) := by
  induction trace generalizing s with
  | nil => simp [last,cycles,Execution.charge]
  | cons pair rest ih =>
    rcases pair with ⟨i,op⟩
    simp only [valid,Bool.and_eq_true,beq_iff_eq] at ok
    obtain ⟨⟨pc,en⟩,tail⟩ := ok
    have next := execute_ordinary_step image op s (effect s op) (rest.length+fuel) false
    rw [List.length_cons,show rest.length+1+fuel = (rest.length+fuel)+1 by omega,
      next (fetched i op (by simp) s pc) (enabled_step _ _ en),
      ih _ (fun j a h => fetched j a (List.mem_cons_of_mem _ h)) tail]
    simp [last,cycles,Execution.charge,Nat.add_assoc]

theorem trace_observation (o : Oracle) (trace : Trace) (s : MachineState) (fuel : Nat)
    (fetched : Decoded trace) (ok : valid trace s = true) :
    let result := observation o fuel (last trace s)
    observation o (trace.length+fuel) s = ((result.1.1.charge (cycles trace) 0,result.1.2),result.2) :=
  step_ordinary o s (last trace s) _ _ (fun n => run_trace trace s n fetched ok) fuel

end CommitGolfCandidate.Reconstruction.Binding.Machine
