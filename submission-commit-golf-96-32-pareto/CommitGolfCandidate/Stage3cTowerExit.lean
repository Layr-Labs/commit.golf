import CommitGolfCandidate.Stage3cPtrExit
namespace CommitGolfCandidate.Chained.BinaryMachine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option Elab.async false

/-- Parent passes plus the root copy and halt.
Entrance is the first parent header. The machine stops with the root digest in the public slot. -/
theorem tower_halt (o : Oracle) (s : MachineState) (base : Nat → Output) (salt : Late.SaltTape)
    (entry : s.pc = pcAt 5678) (regs : Common s)
    (startTree : TreeState o.compression base salt 0 s) (fuel : Nat) :
    ∃ t, t.pc = pcAt 11529 ∧ Common t ∧ TreeState o.compression base salt 24 t ∧
      o.run (execute commitImage (fuel + 60041465) s true) =
        pure (⟨.success, exited t, 178888690, 16978175⟩, 16978175) := by
  obtain ⟨t, pc, cm, tree, parents⟩ := parent_tower o s base salt entry regs startTree
  refine ⟨t, pc, cm, tree, ?_⟩
  have total : fuel + 60041465 = (fuel + 14) + 60041451 := by omega
  rw [total, parents]
  change (do let (out, k) ← o.run (execute commitImage (fuel + 14) t true)
             pure (out.charge 178888676 16978175, 16978175 + k)) = _
  rw [root_exit t pc cm fuel, oracle_run_pure, pure_bind]
  rfl
end CommitGolfCandidate.Chained.BinaryMachine
