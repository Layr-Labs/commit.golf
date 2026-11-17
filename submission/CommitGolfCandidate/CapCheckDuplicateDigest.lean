import CommitGolfCandidate.CapCheckDuplicateFinish
import CommitGolfCandidate.CopyRefinement

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

theorem cap_check_duplicate_passed_digest (state : MachineState) (root : Nat)
    (scratch : state.getReg .x21 = BitVec.ofNat 64 256)
    (rootPointer : state.getReg .x23 = BitVec.ofNat 64 root)
    (aligned : root % 8 = 0) :
    (capCheckDuplicateLoop state 0 4).2 = true ↔
      readBuffer state 256 32 = readBuffer state root 32 := by
  rw [cap_check_duplicate_loop_passed,
    read_digest_eq_iff state state 256 root (by decide) aligned]
  constructor
  · intro equal word bounded
    have result := equal word bounded
    unfold CapCheckDuplicateEqual at result
    rw [scratch, rootPointer, Nat.zero_add] at result
    have offset : signExtend12 (BitVec.ofNat 12 (8*word)) =
        BitVec.ofNat 64 (8*word) := by interval_cases word <;> rfl
    rw [offset] at result
    change state.getMem (BitVec.ofNat 64 256+BitVec.ofNat 64 (8*word)) =
      state.getMem (BitVec.ofNat 64 root+BitVec.ofNat 64 (8*word)) at result
    simpa only [← BitVec.ofNat_add] using result
  · intro equal word bounded
    unfold CapCheckDuplicateEqual
    rw [scratch, rootPointer, Nat.zero_add]
    have result := equal word bounded
    have offset : signExtend12 (BitVec.ofNat 12 (8*word)) =
        BitVec.ofNat 64 (8*word) := by interval_cases word <;> rfl
    rw [offset]
    change state.getMem (BitVec.ofNat 64 256+BitVec.ofNat 64 (8*word)) =
      state.getMem (BitVec.ofNat 64 root+BitVec.ofNat 64 (8*word))
    simpa only [← BitVec.ofNat_add] using result

theorem cap_check_duplicate_done_memory (state : MachineState) :
    (capCheckDuplicateDone state).mem = state.mem :=
  (cap_flow_memory _ _).trans (cap_check_duplicate_loop_memory state 0 4)

theorem cap_check_duplicate_done_register (state : MachineState) (reg : Reg)
    (outside6 : reg ≠ .x6) (outside7 : reg ≠ .x7) :
    (capCheckDuplicateDone state).getReg reg = state.getReg reg :=
  (cap_flow_register _ _ reg).trans
    (cap_check_duplicate_loop_register state 0 4 reg outside6 outside7)

end CommitGolfCandidate
