import CommitGolfCandidate.CapCheckPathPreparation
import CommitGolfCandidate.CapCheckPathImage

/-! One lower sibling step of the actual experimental checker. Preparation
preserves the sibling ordering chosen by the low index bit. The query sees
the prepared scratch buffer, and every arbitrary reply is followed by the
seven real latch instructions, which clear the reply's bytes 30 and 31. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
attribute [local irreducible] readBuffer

def capCheckPathBlockState (state : MachineState) (answer : BitVec 256) : MachineState :=
  capCheckPathTailPrefix (capCheckCompressionState (capCheckPathPreparedState state) answer) 7

def capCheckPathBlockSteps (state : MachineState) : Nat :=
  capCheckPathPreparationSteps (state.getReg .x20) + 13

theorem cap_check_path_block_execute (state : MachineState) (pc : state.pc = 4272)
    (scratch : state.getReg .x21 = 256)
    (sourceValid : ∀ word : Fin 4,
      accessValid (state.getReg .x25 + BitVec.ofNat 64 (8*word.val)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute ((capExperimental 24).image .check) (capCheckPathBlockSteps state+fuel)
      state allowCoins =
      (do let answer ← capCheckScratchQuery
            (readBuffer (capCheckPathPreparedState state) 256 64)
          let result ← execute ((capExperimental 24).image .check) fuel
            (capCheckPathBlockState state answer) allowCoins
          return result.charge (capCheckPathBlockSteps state+7) 1) := by
  have preparedScratch : (capCheckPathPreparedState state).getReg .x21 = 256 :=
    (cap_check_path_prepared_register state .x21 (by decide)).trans scratch
  have compressionPC (answer : BitVec 256) :
      (capCheckCompressionState (capCheckPathPreparedState state) answer).pc = 4404 := by
    rw [cap_check_compression_pc, cap_check_path_prepared_pc]
    rfl
  have compressionScratch (answer : BitVec 256) :
      (capCheckCompressionState (capCheckPathPreparedState state) answer).getReg .x21 = 256 :=
    (cap_check_compression_register _ answer .x21 (by decide)).trans preparedScratch
  rw [capCheckPathBlockSteps,
    show capCheckPathPreparationSteps (state.getReg .x20)+13+fuel =
      capCheckPathPreparationSteps (state.getReg .x20)+(6+(7+fuel)) by omega,
    cap_check_path_preparation_execute state pc scratch sourceValid,
    cap_check_compression_execute _ 4380 cap_check_path_compression_fetched _
      (cap_check_path_prepared_pc state) preparedScratch]
  simp only [bind_assoc, pure_bind]
  congr 1
  funext answer
  rw [cap_check_path_tail_execute _ cap_check_path_tail_fetched _
    (compressionPC answer) (compressionScratch answer)]
  simp [capCheckPathBlockState, capCheckPathBlockSteps, Execution.charge, ← Nat.add_assoc]

theorem cap_check_path_block_steps_bound (state : MachineState) :
    capCheckPathBlockSteps state ≤ 32 := by
  unfold capCheckPathBlockSteps capCheckPathPreparationSteps
  split <;> omega

end CommitGolfCandidate
