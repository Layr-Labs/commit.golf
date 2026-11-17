import CommitGolfCandidate.NonceExpandCapacity
import CommitGolfCandidate.NonceCheckExit

/-! Every failed expansion guard reaches the actual retained reject HALT,
without any proof-memory access or public query. Instruction counts and
charged costs are kept separate at the multiplication guard. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 400000
attribute [local irreducible] nonceExpandHeaderPrefix nonceExpandMinimumPrefix nonceExpandCapacityPrefix

theorem nonce_expand_reject_alignment (state : MachineState) (pc : state.pc=4896) (length : Nat)
    (small : length<2^64) (reported : state.getReg .x17=BitVec.ofNat 64 length)
    (unaligned : length%8 ≠ 0) (fuel : Nat) :
    execute nonceExpandedImage (7+fuel) state false=
      pure ⟨.failure,capCheckExitState (nonceExpandHeaderPrefix state 4) false,7,0⟩ := by
  have rejected : (nonceExpandHeaderPrefix state 4).pc=4808 := by
    simpa only [if_neg unaligned] using nonce_expand_header_pc state pc length small reported
  rw [show 7+fuel=4+(3+fuel) by omega,nonce_expand_header_execute state pc (3+fuel) false,
    nonce_expanded_check_exit _ false rejected fuel false]
  simp only [pure_bind,Execution.charge] <;> rfl

theorem nonce_expand_reject_short (state : MachineState) (pc : state.pc=4912) (length count : Nat)
    (lengthSmall : length<2^64) (productSmall : 536*count<2^64)
    (reported : state.getReg .x17=BitVec.ofNat 64 length) (counter : state.getReg .x16=BitVec.ofNat 64 count)
    (short : length<536*count) (fuel : Nat) :
    execute nonceExpandedImage (8+fuel) state false=
      pure ⟨.failure,capCheckExitState (nonceExpandMinimumPrefix state 5) false,11,0⟩ := by
  have rejected : (nonceExpandMinimumPrefix state 5).pc=4808 := by
    simpa only [if_pos short] using nonce_expand_minimum_pc state pc length count lengthSmall productSmall reported counter
  rw [show 8+fuel=5+(3+fuel) by omega,nonce_expand_minimum_execute state pc (3+fuel) false,
    nonce_expanded_check_exit _ false rejected fuel false]
  simp only [pure_bind,Execution.charge] <;> rfl

theorem nonce_expand_reject_capacity (state : MachineState) (pc : state.pc=4932) (length count : Nat)
    (small : length+8*count<2^64) (reported : state.getReg .x17=BitVec.ofNat 64 length)
    (counter : state.getReg .x16=BitVec.ofNat 64 count) (oversized : 13421772800<length+8*count) (fuel : Nat) :
    execute nonceExpandedImage (15+fuel) state false=
      pure ⟨.failure,capCheckExitState (nonceExpandCapacityPrefix state 12) false,15,0⟩ := by
  have rejected : (nonceExpandCapacityPrefix state 12).pc=4808 := by
    simpa only [if_pos oversized] using nonce_expand_capacity_pc state pc length count small reported counter
  rw [show 15+fuel=12+(3+fuel) by omega,nonce_expand_capacity_execute state pc (3+fuel) false,
    nonce_expanded_check_exit _ false rejected fuel false]
  simp only [pure_bind,Execution.charge] <;> rfl

end CommitGolfCandidate
