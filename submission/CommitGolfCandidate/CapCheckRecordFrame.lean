import CommitGolfCandidate.CapCheckRecordRun

/-! All supported consistency paths touch only the low root/mark workspace.
Thus the complete record retains every high ABI input byte even on rejection.
The frame does not assume a consistent oracle or successful comparison. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false
attribute [local irreducible] capCheckRecordNextPrefix capCheckGroupStartPrefix

theorem cap_check_group_high_frame (state reference : MachineState) (group : Nat)
    (ready : CapCheckGroupReady state group) (frame : CapHighBytes state reference) :
    CapHighBytes (capCheckGroupResult state).1 reference := by
  have addresses := cap_check_group_start_addresses state group ready.bounded ready.index
    ready.leaves ready.marks ready.roots
  intro address lower upper
  have markOutside : BitVec.ofNat 64 (8*(address/8)) ≠
      (capCheckGroupStartPrefix state 6).getReg .x30 := by
    rw [addresses.2.1]
    intro equal
    have numeric := congrArg BitVec.toNat equal
    have bounded := ready.bounded
    rw [BitVec.toNat_ofNat,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 8*(address/8)<2^64),
      Nat.mod_eq_of_lt (by omega : 28672+8*(256+group)<2^64)] at numeric
    omega
  have rootOutside : ∀ word : Fin 4, BitVec.ofNat 64 (8*(address/8)) ≠
      (capCheckGroupStartPrefix state 6).getReg .x23+
        BitVec.ofNat 64 (8*word.val) := by
    intro word equal
    rw [addresses.2.2,← BitVec.ofNat_add] at equal
    have numeric := congrArg BitVec.toNat equal
    have bounded := ready.bounded
    have inside := word.isLt
    rw [BitVec.toNat_ofNat,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 8*(address/8)<2^64),
      Nat.mod_eq_of_lt (by omega : 12288+32*(256+group)+8*word.val<2^64)] at numeric
    omega
  have word := cap_check_group_result_word_frame state
    (BitVec.ofNat 64 (8*(address/8))) markOutside rootOutside
  have nextByte := aligned_byte (capCheckGroupResult state).1
    (address/8) (address%8) (by omega)
  have stateByte := aligned_byte state (address/8) (address%8) (by omega)
  have decomp : 8*(address/8)+address%8=address := by omega
  simp only [Nat.div_eq_of_lt (by omega : address%8<8),Nat.mul_zero,
    Nat.add_zero,Nat.mod_eq_of_lt (by omega : address%8<8),decomp] at nextByte stateByte
  rw [nextByte,word,← stateByte]
  exact frame address lower upper

theorem cap_check_record_result_high_frame (lower reference : MachineState) (group : Nat)
    (ready : CapCheckGroupReady lower group) (frame : CapHighBytes lower reference) :
    CapHighBytes (capCheckRecordResult lower).1 reference := by
  have groupFrame := cap_check_group_high_frame lower reference group ready frame
  dsimp only [capCheckRecordResult]
  split
  · exact cap_high_bytes_memory _ _ _
      (cap_check_record_next_memory _) groupFrame
  · exact groupFrame

theorem cap_check_record_run_high_frame (state reference : MachineState) (index : Nat)
    (bounded : index < 2^24)
    (loaded : state.getMem (state.getReg .x24) = BitVec.ofNat 64 index)
    (scratch : state.getReg .x21 = 256) (leaves : state.getReg .x19 = 256)
    (marks : state.getReg .x9 = 28672) (roots : state.getReg .x18 = 12288)
    (one : state.getReg .x31 = 1) (frame : CapHighBytes state reference)
    (result : MachineState × Bool)
    (reachable : result ∈ support (capCheckRecordRun state)) :
    CapHighBytes result.1 reference := by
  obtain ⟨lower, lowerReachable, equal⟩ :=
    (cap_check_record_run_support state result).mp reachable
  subst result
  have ready := cap_check_lower_group_ready state lower index bounded loaded scratch
    leaves marks roots one lowerReachable
  exact cap_check_record_result_high_frame lower reference (index/2^16) ready
    (cap_check_lower_record_high_frame state reference lower scratch frame lowerReachable)

end CommitGolfCandidate
