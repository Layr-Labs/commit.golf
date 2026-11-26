import CommitGolfCandidate.TwoPermutationSyscall

/-! Inverse-permutation syscall (`a3 = 2`) on aligned 200-byte windows, in the shape of
`execute_permutation_call`. -/
namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv OracleComp RiscvZkvm.Rv64
set_option maxRecDepth 4096

theorem oracle_input_inverse (state : MachineState) (src dst : Nat)
    (srcBound : src + 25 ≤ 2 ^ 33) (dstBound : dst + 25 ≤ 2 ^ 33)
    (input : state.getReg .x10 = wordAddress src) (output : state.getReg .x12 = wordAddress dst)
    (size : state.getReg .x11 = 200) (primitive : state.getReg .x13 = 2) :
    oracleInput state = some (.inr (.inr (packBuffer (window (memoryView state) src)))) := by
  have srcValue := word_address_value (word := src) (by omega)
  have dstValue := word_address_value (word := dst) (by omega)
  have fitsSrc : 8 * src + 200 ≤ MEMORY_BYTES := by unfold MEMORY_BYTES; omega
  have fitsDst : 8 * dst + 200 ≤ MEMORY_BYTES := by unfold MEMORY_BYTES; omega
  have kind : (state.getReg .x13).toNat = 2 := by rw [primitive]; rfl
  unfold oracleInput
  dsimp only
  rw [kind]
  simp [input, output, size, srcValue, dstValue, rangeValid,
    fitsSrc, fitsDst, PERMUTATION_WIDTH, read_permutation_window]

theorem execute_inverse_call (image : Image) (fuel : Nat) (state : MachineState) (allowCoins : Bool)
    (src dst : Nat) (srcBound : src + 25 ≤ 2 ^ 33) (dstBound : dst + 25 ≤ 2 ^ 33)
    (input : state.getReg .x10 = wordAddress src) (output : state.getReg .x12 = wordAddress dst)
    (selector : state.getReg .x5 = 0) (size : state.getReg .x11 = 200) (primitive : state.getReg .x13 = 2)
    (fetched : fetch image state = some (.base .ECALL)) :
    execute image (fuel + 1) state allowCoins = (do
      let answer ← World.query (.inr (.inr (.inr (packBuffer (window (memoryView state) src)))))
      let result ← execute image fuel (writeBits state (wordAddress dst) answer) allowCoins
      pure (result.charge 30 1)) := by
  have ready := oracle_input_inverse state src dst srcBound dstBound input output size primitive
  simp only [execute, fetched, selector, ↓reduceIte, ready, output, writeOracleAnswer, oracleCycles, PERMUTATION_CYCLES]

end TwoPermutationPrototype.RV64
