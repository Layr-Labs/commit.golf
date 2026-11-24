import CommitGolfCandidate.ChainedRootContent
import CommitGolfCandidate.ChainedFastContent

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
    (s : MachineState) (pc : s.pc = 186848) (entry : FastEntry s)
    (output : s.getReg .x8 = 4294971392) (prior : Fast.RawLeaves s heap) :
    readBuffer (checkEvaluation oracle (completeParentTrace s)).1 4294971392 32 = (heap 1).setWidth 256 := by
  have fc := Fast.fast_levels_content oracle heap tree s pc entry output prior
  rw [show completeParentTrace s = Fast.fastParentTrace s from rfl,Fast.fast_parent_eval]
  exact (chained_root_copy_output _ fc.2.1 fc.2.2).trans (fc.1.nodes 1 (by decide) (by decide))

end CommitGolfCandidate.Chained.Native
