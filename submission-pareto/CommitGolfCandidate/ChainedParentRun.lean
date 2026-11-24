import CommitGolfCandidate.ChainedFastPhase

/-! Complete native parent execution: specialized heights 0-7, the delivered level code for
heights 8-23, and the root halt. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.RV64
attribute [local irreducible] execute parentLevels chainedRootPrefix

def completeParentTrace (s : MachineState) : OracleComp World MachineState := Fast.fastParentTrace s

theorem complete_parent_constants : Fast.fastParentSteps=694912658 ∧ Fast.fastParentCycles=1166031243 ∧
    Fast.fastParentCalls=67302655 := by decide +kernel

theorem complete_parent_execution (s : MachineState) (pc : s.pc = 186848) (entry : FastEntry s)
    (output : s.getReg .x8 = 4294971392) (fuel : Nat) :
    execute chainedCommitImage (694912658+fuel) s true =
      (do let out ← completeParentTrace s
          return ⟨.success,out,1166031243,67302655⟩) := by
  have run:=Fast.fast_parent_execution s pc entry output fuel
  rw [complete_parent_constants.1,complete_parent_constants.2.1,complete_parent_constants.2.2] at run
  exact run

theorem leaf_prefix_output (ready : MachineState) (regs : Chain.BodyRegs ready) (out : MachineState)
    (reached : out ∈ support (leafPrefixTrace ready)) : out.getReg .x8 = 4294971392 := by
  simp only [leafPrefixTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
  obtain ⟨leaves,last,rfl⟩ := reached
  have fin := PackedLeaves.executableLeaves.finished ready regs leaves last
  exact (skip_entry_ready leaves fin.pc fin.selector fin.heap fin.stride fin.stop).2.2.1.trans fin.output

def chainedCommitBody (ready : MachineState) : OracleComp World MachineState := do
  let leaves ← leafPrefixTrace ready
  completeParentTrace leaves

theorem chained_commit_body_execution (ready : MachineState) (regs : Chain.BodyRegs ready) (fuel : Nat) :
    execute chainedCommitImage (879666839+fuel) ready true =
      (do let out ← chainedCommitBody ready
          return ⟨.success,out,1585666448,100857087⟩) := by
  rw [show 879666839+fuel = 184754175+skipEntryCost+(694912658+fuel) by unfold skipEntryCost; omega,
    leaf_prefix_execution ready regs]
  simp only [chainedCommitBody,bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro leaves reached
  rw [complete_parent_execution leaves (leaf_prefix_parent_pc ready regs leaves reached)
    (leaf_prefix_heap_ready ready regs leaves reached) (leaf_prefix_output ready regs leaves reached)]
  simp only [bind_assoc,pure_bind,Execution.charge,skipEntryCost]

end CommitGolfCandidate.Chained.Native
