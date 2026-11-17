import CommitGolfCandidate.CapWordCopy
import CommitGolfCandidate.CapCheckLeafTail

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem cap_check_leaf_copy_fetched :
    CapWordCopyFetched ((capExperimental 24).image .check) .x8 .x21 0 32 4824 := by
  intro state i bounded pc
  apply cap_image_fetch _ (capWordCopyPrefix .x8 .x21 0 32 state i)
    (182 + i) _ (by omega)
  · rw [cap_word_copy_prefix_pc .x8 .x21 0 32 state i (by omega), pc]
    interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem cap_check_leaf_compression_fetched :
    CapCheckCompressionFetched ((capExperimental 24).image .check) 4856 := by
  constructor
  · intro state i bounded pc
    apply cap_image_fetch _ (capCheckCompressionPrefix state i) (190 + i) _ (by omega)
    · rw [cap_check_compression_prefix_pc state i (by omega), pc]
      interval_cases i <;> rfl
    · interval_cases i <;> rfl
  · intro state pc
    apply cap_image_fetch _ (capCheckCompressionPrefix state 5) 195 _ (by decide)
    · rw [cap_check_compression_prefix_pc state 5 (by decide), pc]
      rfl
    · rfl

theorem cap_check_leaf_tail_fetched :
    CapCheckLeafTailFetched ((capExperimental 24).image .check) 4880 := by
  intro state i bounded pc
  apply cap_image_fetch _ (capCheckLeafTailPrefix state i) (196 + i) _ (by omega)
  · rw [cap_check_leaf_tail_prefix_pc state i bounded, pc]
    interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem cap_check_leaf_init_fetched (state : MachineState) (pc : state.pc = 4820) :
    fetch ((capExperimental 24).image .check) state =
      some (.base (.ADDI .x28 .x0 8)) := by
  apply cap_image_fetch _ state 181 _ (by decide) pc
  rfl

theorem cap_check_leaf_return_fetched (state : MachineState) (pc : state.pc = 4892) :
    fetch ((capExperimental 24).image .check) state =
      some (.base (.JALR .x0 .x1 0)) := by
  apply cap_image_fetch _ state 199 _ (by decide) pc
  rfl

end CommitGolfCandidate
