import CommitGolfCandidate.ChainedParentPost

/-! Complete native parent execution, including initialization, 24 levels and root halt. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.RV64
attribute [local irreducible] execute parentLevels chainedRootPrefix

def completeParentTrace (s : MachineState) : OracleComp World MachineState := do
  let out ← parentLevels 24 (parentInitPrefix s 5)
  return chainedRootPrefix out 10

theorem complete_parent_execution (s : MachineState) (pc : s.pc = 184628)
    (ready : HeapLevelReady (parentInitPrefix s 5) 0 (heightCount 0))
    (output : s.getReg .x8 = 4294971392) (fuel : Nat) :
    execute chainedCommitImage (1343338090+fuel) s true =
      (do let out ← completeParentTrace s
          return ⟨.success,out,1814456675,67302655⟩) := by
  have entry : HeapLevelReady (parentInitPrefix s 5) (heightAt 24) (heightCount (heightAt 24)) := ready
  rw [show 1343338090+fuel = 5+(levelsSteps 24+(11+fuel)) by rw [parent_levels_totals.1]; omega,
    parent_init_execution s pc,parent_levels_execution 24 (by decide) _ (fun _ => entry)]
  simp only [completeParentTrace,bind_assoc,pure_bind]
  apply bind_congr_of_forall_mem_support
  intro out reached
  have endpc := parent_levels_pc 24 (by decide) (by decide) _ out entry reached
  have heap : out.getReg .x9 = 4294971424 :=
    (parent_levels_register 24 _ out reached .x9 (by simp [ParentSaved])).trans entry.base
  have target : out.getReg .x8 = 4294971392 :=
    (parent_levels_register 24 _ out reached .x8 (by simp [ParentSaved])).trans
      ((parent_init_register s .x8 (by decide)).trans output)
  rw [chained_root_execution out endpc heap target]
  simp only [pure_bind,Execution.charge,parent_levels_totals.2.1,parent_levels_totals.2.2]

theorem leaf_prefix_output (ready : MachineState) (regs : Chain.BodyRegs ready) (out : MachineState)
    (reached : out ∈ support (leafPrefixTrace ready)) : out.getReg .x8 = 4294971392 := by
  simp only [leafPrefixTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
  obtain ⟨leaves,last,rfl⟩ := reached
  have fin := PackedLeaves.executableLeaves.finished ready regs leaves last
  exact (zero_entry_ready leaves fin.pc fin.selector fin.heap fin.stride fin.stop).2.2.trans fin.output

def chainedCommitBody (ready : MachineState) : OracleComp World MachineState := do
  let leaves ← leafPrefixTrace ready
  completeParentTrace leaves

theorem chained_commit_body_execution (ready : MachineState) (regs : Chain.BodyRegs ready) (fuel : Nat) :
    execute chainedCommitImage (1579472499+fuel) ready true =
      (do let out ← chainedCommitBody ready
          return ⟨.success,out,2285472108,100857087⟩) := by
  rw [show 1579472499+fuel = 184754175+zeroEntryCost+(1343338090+fuel) by unfold zeroEntryCost; omega,
    leaf_prefix_execution ready regs]
  simp only [chainedCommitBody,bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro leaves reached
  rw [complete_parent_execution leaves (leaf_prefix_parent_pc ready regs leaves reached)
    (leaf_prefix_heap_ready ready regs leaves reached) (leaf_prefix_output ready regs leaves reached)]
  simp only [bind_assoc,pure_bind,Execution.charge,zeroEntryCost]

end CommitGolfCandidate.Chained.Native
