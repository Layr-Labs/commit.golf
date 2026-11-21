import CommitGolfCandidate.ChainedRootContent

/-! Readback composition without unfolding the interpreted parent-level computation. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
attribute [local irreducible] parentLevels checkEvaluation readBuffer

theorem evaluation_read_map (oracle : Oracle) (program : OracleComp World MachineState)
    (f : MachineState → MachineState) (address count : Nat) :
    readBuffer (checkEvaluation oracle (program >>= fun out => pure (f out))).1 address count =
      readBuffer (f (checkEvaluation oracle program).1) address count := by
  rw [check_evaluation_bind]
  simp only [check_evaluation_pure]

theorem complete_parent_content (oracle : Oracle) (heap : Nat → BitVec 238) (tree : ChainedTree oracle heap)
    (s : MachineState) (ready : HeapLevelReady (parentInitPrefix s 5) 0 (heightCount 0))
    (output : s.getReg .x8 = 4294971392) (prior : HeapContent s heap (2^24-1)) :
    readBuffer (checkEvaluation oracle (completeParentTrace s)).1 4294971392 32 = (heap 1).setWidth 256 := by
  have entry : HeapLevelReady (parentInitPrefix s 5) (heightAt 24) (heightCount (heightAt 24)) := ready
  have count : 2*heightCount (heightAt 24)-1 = 2^24-1 := by decide +kernel
  have content : HeapContent (parentInitPrefix s 5) heap (2*heightCount (heightAt 24)-1) := by
    rw [count]
    exact prior.frame (parent_init_memory s)
  let out := (checkEvaluation oracle (parentLevels 24 (parentInitPrefix s 5))).1
  have reached := check_evaluation_support oracle (parentLevels 24 (parentInitPrefix s 5))
  have computed := parent_levels_content oracle heap tree 24 (by decide) (by decide) _ entry content
  have heapreg : out.getReg .x9 = 4294971424 :=
    (parent_levels_register 24 _ out reached .x9 (by simp [ParentSaved])).trans entry.base
  have target : out.getReg .x8 = 4294971392 :=
    (parent_levels_register 24 _ out reached .x8 (by simp [ParentSaved])).trans
      ((parent_init_register s .x8 (by decide)).trans output)
  rw [completeParentTrace,evaluation_read_map]
  exact (chained_root_copy_output out heapreg target).trans (computed.nodes 1 (by decide) (by decide))

end CommitGolfCandidate.Chained.Native
