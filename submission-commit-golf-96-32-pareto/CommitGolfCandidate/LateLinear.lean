import CommitGolfCandidate.LateCalls

namespace CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

def straight (op : Instr) := ∀ s, ordinaryStep s (.base op) = some (execInstrBr s op) ∧
  instructionCycles (.base op) = 1 ∧ (execInstrBr s op).pc = s.pc+4

theorem execute_linear (ops : List Instr) (n : Nat) (s : MachineState) (fuel : Nat)
    (pc : s.pc = pcAt n) (plain : ∀ op ∈ ops, straight op)
    (code : ∀ i (hi : i < ops.length), AtWord (n+i) ops[i]) :
    execute commitImage (fuel+ops.length) s true =
      (do let r ← execute commitImage fuel (ops.foldl execInstrBr s) true
          return r.charge ops.length 0) := by
  induction ops generalizing n s with
  | nil => simp [Execution.charge]
  | cons op ops ih =>
    obtain ⟨step,cost,inc⟩ := plain op (List.mem_cons_self ..) s
    have next := ih (n+1) (execInstrBr s op) (by rw [inc,pc,pc_succ])
      (fun o h => plain o (List.mem_cons_of_mem _ h))
      (fun i hi => by
        rw [show n+1+i = n+(i+1) by omega]
        exact code (i+1) (by simp; omega))
    have fetch : fetch commitImage s = some (.base op) := code 0 (by simp) s (by simpa using pc)
    simp only [List.length_cons, List.foldl_cons, ← Nat.add_assoc]
    rw [execute_ordinary_step _ _ _ _ _ _ fetch step, next, cost]
    simp [Execution.charge, ← Nat.add_assoc, Nat.add_comm 1 ops.length]

end CommitGolfCandidate.Late
