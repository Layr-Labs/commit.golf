import CommitGolfCandidate.CapCheckLeafImage

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
attribute [local irreducible] readBuffer

def capCheckLeafCopyState (state : MachineState) : MachineState :=
  capWordCopyPrefix .x8 .x21 0 32 state 8

def capCheckLeafBlockState (state : MachineState) (answer : BitVec 256) : MachineState :=
  capCheckLeafTailPrefix (capCheckCompressionState (capCheckLeafCopyState state) answer) 3

theorem cap_check_leaf_copy_pc (state : MachineState) :
    (capCheckLeafCopyState state).pc = state.pc + 32 :=
  cap_word_copy_prefix_pc .x8 .x21 0 32 state 8 (by decide)

theorem cap_check_leaf_copy_register (state : MachineState) (reg : Reg)
    (outside : reg ≠ .x6) :
    (capCheckLeafCopyState state).getReg reg = state.getReg reg :=
  cap_word_copy_prefix_register .x8 .x21 0 32 state 8 (by decide) reg outside

theorem cap_check_leaf_block_execute (state : MachineState) (pc : state.pc = 4824)
    (scratch : state.getReg .x21 = 256)
    (sourceValid : ∀ word : Fin 4,
      accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute ((capExperimental 24).image .check) (17 + fuel) state allowCoins =
      (do let answer ← capCheckScratchQuery
            (readBuffer (capCheckLeafCopyState state) 256 64)
          let result ← execute ((capExperimental 24).image .check) fuel
            (capCheckLeafBlockState state answer) allowCoins
          return result.charge 24 1) := by
  have source : ∀ word : Fin 4,
      accessValid (state.getReg .x8 + signExtend12
        (BitVec.ofNat 12 (0 + 8 * word.val))) 8 = true := by
    have offset (word : Fin 4) : signExtend12
        (BitVec.ofNat 12 (0 + 8 * word.val)) = BitVec.ofNat 64 (8 * word.val) := by
      fin_cases word <;> decide
    intro word
    rw [offset word]
    exact sourceValid word
  have destination : ∀ word : Fin 4,
      accessValid (state.getReg .x21 + signExtend12
        (BitVec.ofNat 12 (32 + 8 * word.val))) 8 = true := by
    intro word
    rw [scratch]
    fin_cases word <;> decide
  have copyPC : (capCheckLeafCopyState state).pc = 4856 := by
    rw [cap_check_leaf_copy_pc, pc]
    rfl
  have copyScratch : (capCheckLeafCopyState state).getReg .x21 = 256 :=
    (cap_check_leaf_copy_register state .x21 (by decide)).trans scratch
  have compressionPC (answer : BitVec 256) :
      (capCheckCompressionState (capCheckLeafCopyState state) answer).pc = 4880 := by
    rw [cap_check_compression_pc, copyPC]
    rfl
  rw [show 17 + fuel = 8 + (6 + (3 + fuel)) by omega,
    cap_word_copy_execute _ .x8 .x21 0 32 4824 cap_check_leaf_copy_fetched
      state pc (by decide) (by decide) source destination]
  change (do
    let result ← execute ((capExperimental 24).image .check)
        (6 + (3 + fuel)) (capCheckLeafCopyState state) allowCoins
    return result.charge 8 0) = _
  rw [cap_check_compression_execute _ 4856 cap_check_leaf_compression_fetched
    (capCheckLeafCopyState state) copyPC copyScratch]
  simp only [bind_assoc, pure_bind]
  congr 1
  funext answer
  rw [cap_check_leaf_tail_execute _ 4880 cap_check_leaf_tail_fetched _
    (compressionPC answer)]
  simp [capCheckLeafBlockState, Execution.charge, ← Nat.add_assoc]

theorem cap_check_leaf_block_pointers (state : MachineState) (answer : BitVec 256) :
    (capCheckLeafBlockState state answer).getReg .x8 = state.getReg .x8 + 32 ∧
    (capCheckLeafBlockState state answer).getReg .x28 = state.getReg .x28 - 1 := by
  have source := cap_check_compression_register (capCheckLeafCopyState state) answer .x8
    (by decide)
  have counter := cap_check_compression_register (capCheckLeafCopyState state) answer .x28
    (by decide)
  rw [cap_check_leaf_copy_register state .x8 (by decide)] at source
  rw [cap_check_leaf_copy_register state .x28 (by decide)] at counter
  simpa only [capCheckLeafBlockState, source, counter] using
    cap_check_leaf_tail_pointers (capCheckCompressionState (capCheckLeafCopyState state) answer)

theorem cap_check_leaf_block_pc (state : MachineState) (answer : BitVec 256)
    (pc : state.pc = 4824) :
    (capCheckLeafBlockState state answer).pc =
      if state.getReg .x28 - 1 = 0 then 4892 else 4824 := by
  have counter := cap_check_compression_register (capCheckLeafCopyState state) answer .x28
    (by decide)
  rw [cap_check_leaf_copy_register state .x28 (by decide)] at counter
  rw [capCheckLeafBlockState, cap_check_leaf_tail_pc, counter,
    cap_check_compression_pc, cap_check_leaf_copy_pc, pc]
  rfl

theorem cap_check_leaf_block_register (state : MachineState) (answer : BitVec 256)
    (reg : Reg) (outside : reg ∉ [.x6, .x5, .x8, .x10, .x11, .x12, .x13, .x28]) :
    (capCheckLeafBlockState state answer).getReg reg = state.getReg reg := by
  have not6 : reg ≠ .x6 := by simp_all
  have not5 : reg ≠ .x5 := by simp_all
  have not8 : reg ≠ .x8 := by simp_all
  have not10 : reg ≠ .x10 := by simp_all
  have not11 : reg ≠ .x11 := by simp_all
  have not12 : reg ≠ .x12 := by simp_all
  have not13 : reg ≠ .x13 := by simp_all
  have not28 : reg ≠ .x28 := by simp_all
  rw [capCheckLeafBlockState, cap_check_leaf_tail_register _ reg ⟨not8, not28⟩,
    cap_check_compression_register _ answer reg ⟨not5, not10, not11, not12, not13⟩,
    cap_check_leaf_copy_register state reg not6]

end CommitGolfCandidate
