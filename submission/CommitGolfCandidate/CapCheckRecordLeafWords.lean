import CommitGolfCandidate.CapCheckRecordLeafFrame

/-! Low root and mark slots require a word frame separate from high ABI bytes.
The entire salt-and-leaf macro writes only the 36 low workspace words at
0, 8, ..., 280 on every possible reply continuation. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

private theorem word_memory_congr (left right : MachineState)
    (same : left.mem = right.mem) (address : Word) :
    left.getMem address = right.getMem address := congrFun same address

/-- The salt-and-leaf macro writes only words 0, 8, ..., 280. -/
theorem cap_check_record_leaf_word_frame (state finished : MachineState)
    (scratch : state.getReg .x21 = 256)
    (reachable : finished ∈ support (capCheckRecordLeaf state))
    (address : Word)
    (outside : ∀ i < 36, address ≠ BitVec.ofNat 64 (8*i)) :
    finished.getMem address = state.getMem address := by
  obtain ⟨body, bodyReachable, rfl⟩ := cap_check_record_leaf_support state finished reachable
  have bodyWord := cap_check_leaf_word_frame _ body bodyReachable address outside
  have startWord := word_memory_congr _ _
    (cap_check_record_leaf_start_memory state) address
  have saltWord := cap_check_salt_outside state address scratch (fun i inside => by
    have distinct := outside (32 + i) (by omega)
    rwa [show 8 * (32 + i) = 256 + 8*i by omega] at distinct)
  exact bodyWord.trans (startWord.trans saltWord)

theorem cap_check_record_leaf_low_frame (state finished : MachineState)
    (scratch : state.getReg .x21 = 256)
    (reachable : finished ∈ support (capCheckRecordLeaf state))
    (address : Nat) (above : 320 ≤ address) (below : address < 32768) :
    finished.getMem (BitVec.ofNat 64 address) =
      state.getMem (BitVec.ofNat 64 address) := by
  apply cap_check_record_leaf_word_frame state finished scratch reachable
  intro i inside equal
  have numeric := congrArg BitVec.toNat equal
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : address < 2^64),
    Nat.mod_eq_of_lt (by omega : 8*i < 2^64)] at numeric
  omega

end CommitGolfCandidate
