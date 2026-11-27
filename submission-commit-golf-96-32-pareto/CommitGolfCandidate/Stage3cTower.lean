import CommitGolfCandidate.Stage3cChainJoin
namespace CommitGolfCandidate.Chained.BinaryMachine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
set_option Elab.async false

/-- `stage n` is parent level `n`, for `n < 24`. -/
def stage (n : Nat) : Height := ⟨n % 24, by omega⟩

/-- Program counter after the first `n` parent passes. Level 0 begins at 5678. -/
def boundary : Nat → Nat
  | 0 => 5678
  | n + 1 => passEnd (stage n)

def sumCost (f : Height → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumCost f n + f (stage n)

theorem next_header (d : Height) : boundary d.val = passHeader d :=
  (by decide +kernel : ∀ k : Height, boundary k.val = passHeader k) d

theorem parent_sums : sumCost passSteps 24 = 60041451 ∧ sumCost passCycles 24 = 178888676 ∧
    sumCost (fun h => count h * calls h) 24 = 16978175 := by decide +kernel

theorem combined (o : Oracle) (s : MachineState) (base : Nat → Output) (salt : Late.SaltTape)
    (entry : s.pc = pcAt (boundary 0)) (regs : Common s)
    (startTree : TreeState o.compression base salt 0 s) (n : Nat) (hn : n ≤ 24) :
    ∃ t, t.pc = pcAt (boundary n) ∧ Common t ∧ TreeState o.compression base salt n t ∧
      Runs .commit true o s t (sumCost passSteps n) (sumCost passCycles n)
        (sumCost (fun h => count h * calls h) n) := by
  induction n with
  | zero => exact ⟨s, entry, regs, startTree, runs_id .commit true o s⟩
  | succ n ih =>
    obtain ⟨t, ip, ctx, tree, before⟩ := ih (by omega)
    let h : Height := ⟨n, by omega⟩
    obtain ⟨u, exit, next, result, run⟩ :=
      all_stages h o t base salt (ip.trans (congrArg pcAt (next_header h))) ctx tree
    have id : stage n = h := Fin.ext (Nat.mod_eq_of_lt h.isLt)
    simp only [boundary, sumCost, id]
    exact ⟨u, exit, next, result, runs_comp before run⟩

/-- The twenty-four parent passes, from the first header through the root hash. -/
theorem parent_tower (o : Oracle) (s : MachineState) (base : Nat → Output) (salt : Late.SaltTape)
    (entry : s.pc = pcAt 5678) (regs : Common s)
    (startTree : TreeState o.compression base salt 0 s) :
    ∃ t, t.pc = pcAt 11529 ∧ Common t ∧ TreeState o.compression base salt 24 t ∧
      Runs .commit true o s t 60041451 178888676 16978175 := by
  have entry' : s.pc = pcAt (boundary 0) := by simpa [boundary] using entry
  obtain ⟨t, last, cm, tree, parents⟩ := combined o s base salt entry' regs startTree 24 le_rfl
  have finalPC : boundary 24 = 11529 := by decide +kernel
  rw [finalPC] at last
  obtain ⟨steps, cycles, callCount⟩ := parent_sums
  rw [steps, cycles, callCount] at parents
  exact ⟨t, last, cm, tree, parents⟩
end CommitGolfCandidate.Chained.BinaryMachine
