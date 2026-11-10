import CommitGolfCandidate.CapCheckRecordLeafFrame

/-! Low root and mark slots require a word frame separate from high ABI bytes.
The entire salt-and-leaf macro writes only the eight scratch words at
256, 264, ..., 312 on every possible reply continuation. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

private theorem word_memory_congr (left right : MachineState)
    (same : left.mem = right.mem) (address : Word) :
    left.getMem address = right.getMem address := congrFun same address

theorem cap_check_record_leaf_word_frame (state finished : MachineState)
    (scratch : state.getReg .x21 = 256)
    (reachable : finished ∈ support (capCheckRecordLeaf state))
    (address : Word)
    (outside : ∀ i < 8, address ≠ BitVec.ofNat 64 (256 + 8*i)) :
    finished.getMem address = state.getMem address := by
  simp only [capCheckRecordLeaf, mem_support_bind_iff] at reachable
  obtain ⟨body, bodyReachable, tail⟩ := reachable
  simp only [support_pure, Set.mem_singleton_iff] at tail
  subst finished
  have startScratch :=
    (cap_check_record_leaf_start_register state .x21 (by decide)).trans scratch
  have bodyWord := cap_check_leaf_loop_word_frame _ 8 startScratch
    body bodyReachable address outside
  have startWord := word_memory_congr _ _
    (cap_check_record_leaf_start_memory state) address
  have saltWord := cap_check_salt_outside state address scratch
    (fun i inside => outside i (by omega))
  exact bodyWord.trans (startWord.trans saltWord)

theorem cap_check_record_leaf_low_frame (state finished : MachineState)
    (scratch : state.getReg .x21 = 256)
    (reachable : finished ∈ support (capCheckRecordLeaf state))
    (address : Nat) (above : 320 ≤ address) (below : address < 22528) :
    finished.getMem (BitVec.ofNat 64 address) =
      state.getMem (BitVec.ofNat 64 address) := by
  apply cap_check_record_leaf_word_frame state finished scratch reachable
  intro i inside equal
  have numeric := congrArg BitVec.toNat equal
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : address < 2^64),
    Nat.mod_eq_of_lt (by omega : 256 + 8*i < 2^64)] at numeric
  omega

end CommitGolfCandidate
