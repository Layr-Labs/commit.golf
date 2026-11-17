import CommitGolfCandidate.CapCheckPathMemory
import CommitGolfCandidate.CapCheckPathOutcome
import CommitGolfCandidate.CapMemoryFrame

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
attribute [local irreducible] capCheckPathBlockState

theorem cap_check_path_loop_word_frame (state : MachineState) (count : Nat)
    (scratch : state.getReg .x21 = 256) (finished : MachineState)
    (reachable : finished ∈ support (capCheckPathLoop state count)) (address : Word)
    (outside : ∀ i < 8, address ≠ BitVec.ofNat 64 (256 + 8*i)) :
    finished.getMem address = state.getMem address := by
  induction count generalizing state with
  | zero =>
    simp only [capCheckPathLoop, support_pure, Set.mem_singleton_iff] at reachable
    subst finished
    rfl
  | succ count ih =>
    simp only [capCheckPathLoop, mem_support_bind_iff] at reachable
    obtain ⟨answer, _, tail⟩ := reachable
    have nextScratch := (cap_check_path_block_register state answer .x21 (by decide)).trans scratch
    exact (ih _ nextScratch tail).trans
      (cap_check_path_block_outside state answer scratch address outside)

theorem cap_check_path_loop_high_frame (state reference : MachineState) (count : Nat)
    (scratch : state.getReg .x21 = 256) (finished : MachineState)
    (reachable : finished ∈ support (capCheckPathLoop state count))
    (frame : CapHighBytes state reference) : CapHighBytes finished reference := by
  intro address lower upper
  have distinct : ∀ i < 8,
      BitVec.ofNat 64 (8 * (address / 8)) ≠ BitVec.ofNat 64 (256 + 8*i) := by
    intro i inside equal
    have numeric := congrArg BitVec.toNat equal
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 8 * (address / 8) < 2^64),
      Nat.mod_eq_of_lt (by omega : 256 + 8*i < 2^64)] at numeric
    omega
  have word := cap_check_path_loop_word_frame state count scratch finished reachable
    (BitVec.ofNat 64 (8 * (address / 8))) distinct
  have finishedByte := aligned_byte finished (address / 8) (address % 8) (by omega)
  have stateByte := aligned_byte state (address / 8) (address % 8) (by omega)
  have decomp : 8 * (address / 8) + address % 8 = address := by omega
  simp only [Nat.div_eq_of_lt (by omega : address % 8 < 8), Nat.mul_zero,
    Nat.add_zero, Nat.mod_eq_of_lt (by omega : address % 8 < 8), decomp] at finishedByte stateByte
  rw [finishedByte, word, ← stateByte]
  exact frame address lower upper

end CommitGolfCandidate
