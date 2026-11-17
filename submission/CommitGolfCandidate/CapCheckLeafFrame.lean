import CommitGolfCandidate.CapCheckLeafReference
import CommitGolfCandidate.CapMemoryFrame

/-! Frames for every supported leaf-loop outcome, including inconsistent
successive replies. Only the eight scratch words may change. These frames
preserve real input buffers, collected cap roots and finalized marks. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

/-- The count is structural and holds on every possible reply continuation. -/
theorem cap_check_leaf_loop_query_bound (state : MachineState) (count : Nat) :
    IsTotalQueryBound (capCheckLeafLoop state count) count := by
  induction count generalizing state with
  | zero => trivial
  | succ count ih =>
    unfold capCheckLeafLoop capCheckScratchQuery
    erw [isTotalQueryBound_query_bind_iff]
    exact ⟨by omega, fun answer => by simpa using ih (capCheckLeafBlockState state answer)⟩

theorem cap_check_leaf_loop_register_frame (state : MachineState) (count : Nat)
    (finished : MachineState) (reachable : finished ∈ support (capCheckLeafLoop state count))
    (reg : Reg) (outside : reg ∉ [.x6, .x5, .x8, .x10, .x11, .x12, .x13, .x28]) :
    finished.getReg reg = state.getReg reg := by
  induction count generalizing state with
  | zero =>
    simp only [capCheckLeafLoop, support_pure, Set.mem_singleton_iff] at reachable
    subst finished
    rfl
  | succ count ih =>
    simp only [capCheckLeafLoop, mem_support_bind_iff] at reachable
    obtain ⟨answer, _, tail⟩ := reachable
    exact (ih _ tail).trans (cap_check_leaf_block_register state answer reg outside)

theorem cap_check_leaf_loop_word_frame (state : MachineState) (count : Nat)
    (scratch : state.getReg .x21 = 256) (finished : MachineState)
    (reachable : finished ∈ support (capCheckLeafLoop state count)) (address : Word)
    (outside : ∀ i < 8, address ≠ BitVec.ofNat 64 (256 + 8*i)) :
    finished.getMem address = state.getMem address := by
  induction count generalizing state with
  | zero =>
    simp only [capCheckLeafLoop, support_pure, Set.mem_singleton_iff] at reachable
    subst finished
    rfl
  | succ count ih =>
    simp only [capCheckLeafLoop, mem_support_bind_iff] at reachable
    obtain ⟨answer, _, tail⟩ := reachable
    have nextScratch := (cap_check_leaf_block_register state answer .x21 (by decide)).trans scratch
    exact (ih _ nextScratch tail).trans
      (cap_check_leaf_block_outside state answer scratch address outside)

/-- The unchanged backing word also gives exact high-byte preservation. -/
theorem cap_check_leaf_loop_high_frame (state reference : MachineState) (count : Nat)
    (scratch : state.getReg .x21 = 256) (finished : MachineState)
    (reachable : finished ∈ support (capCheckLeafLoop state count))
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
  have word := cap_check_leaf_loop_word_frame state count scratch finished reachable
    (BitVec.ofNat 64 (8 * (address / 8))) distinct
  have finishedByte := aligned_byte finished (address / 8) (address % 8) (by omega)
  have stateByte := aligned_byte state (address / 8) (address % 8) (by omega)
  have decomp : 8 * (address / 8) + address % 8 = address := by omega
  simp only [Nat.div_eq_of_lt (by omega : address % 8 < 8), Nat.mul_zero,
    Nat.add_zero, Nat.mod_eq_of_lt (by omega : address % 8 < 8), decomp] at finishedByte stateByte
  rw [finishedByte, word, ← stateByte]
  exact frame address lower upper

end CommitGolfCandidate
