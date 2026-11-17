import CommitGolfCandidate.CapParentPrepare

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
attribute [local irreducible] capParentPrefix readBuffer

def capParentAnswerState (state : MachineState) (answer : BitVec 256) : MachineState :=
  capCompressionAnswer (capParentPrefix state 4) answer

private theorem parent_charge (result : Execution) :
    (result.charge 8 1).charge 4 0 = result.charge 12 1 := by
  simp only [Execution.charge, Nat.zero_add, ← Nat.add_assoc]

theorem cap_parent_query (state : MachineState) (node : Nat)
    (roots : state.getReg .x18 = 12288)
    (index : state.getReg .x20 = BitVec.ofNat 64 node) (bounded : node < 256) :
    capCompressionInput (capParentPrefix state 4) =
      .inl (readBuffer state (12288 + 64 * node + 32) 32 ++
        readBuffer state (12288 + 64 * node) 32) := by
  rw [cap_compression_halves (capParentPrefix state 4) (12288 + 64 * node)
    (cap_parent_source state node roots index) (by omega) (by omega)]
  rw [read_buffer_memory_congr (capParentPrefix state 4) state
    (cap_parent_prefix_memory state 4 (by decide)),
    read_buffer_memory_congr (capParentPrefix state 4) state
      (cap_parent_prefix_memory state 4 (by decide))]

theorem cap_parent_execute (state : MachineState) (node : Nat)
    (pc : state.pc = 4704) (roots : state.getReg .x18 = 12288)
    (index : state.getReg .x20 = BitVec.ofNat 64 node) (bounded : node < 256)
    (selectors : state.getReg .x5 = 0 ∧ state.getReg .x11 = 64 ∧ state.getReg .x13 = 0)
    (fuel : Nat) (allowCoins : Bool) :
    execute ((capExperimental 24).image .check) (5 + fuel) state allowCoins =
      (do let answer ← World.query (.inr (.inl
            (readBuffer state (12288 + 64 * node + 32) 32 ++
              readBuffer state (12288 + 64 * node) 32)))
          let result ← execute ((capExperimental 24).image .check) fuel
            (capParentAnswerState state answer) allowCoins
          return result.charge 12 1) := by
  have source := cap_parent_source state node roots index
  have destination := cap_parent_destination state node roots index
  have access := cap_parent_access node bounded
  have constants :
      (capParentPrefix state 4).getReg .x5 = 0 ∧
      (capParentPrefix state 4).getReg .x11 = 64 ∧
      (capParentPrefix state 4).getReg .x13 = 0 :=
    ⟨(cap_parent_prefix_register state 4 (by decide) .x5 (by decide)).trans selectors.1,
     (cap_parent_prefix_register state 4 (by decide) .x11 (by decide)).trans selectors.2.1,
     (cap_parent_prefix_register state 4 (by decide) .x13 (by decide)).trans selectors.2.2⟩
  have fetched := cap_parent_ecall_fetched (capParentPrefix state 4) (by
    rw [cap_parent_prefix_pc state 4 (by decide), pc]
    rfl)
  rw [show 5 + fuel = 4 + (1 + fuel) by omega,
    cap_parent_prepare_execute _ 4704 cap_parent_prepare_fetched state pc]
  rw [cap_compression_execute _ (capParentPrefix state 4) fetched constants
    (by rw [source]; exact access.1)
    (by rw [destination]; exact access.2.1)
    (by rw [source]; exact access.2.2.1)
    (by rw [destination]; exact access.2.2.2)]
  have inputBytes :
      readBuffer (capParentPrefix state 4) ((capParentPrefix state 4).getReg .x10).toNat 64 =
        readBuffer state (12288 + 64 * node + 32) 32 ++
          readBuffer state (12288 + 64 * node) 32 :=
    Sum.inl.inj (cap_parent_query state node roots index bounded)
  simp only [capCompressionInput]
  rw [inputBytes]
  simp only [bind_assoc, pure_bind, parent_charge, capParentAnswerState]

theorem cap_parent_answer_register (state : MachineState) (answer : BitVec 256)
    (reg : Reg) (outside : reg ≠ .x10 ∧ reg ≠ .x12) :
    (capParentAnswerState state answer).getReg reg = state.getReg reg :=
  (cap_compression_register (capParentPrefix state 4) answer reg).trans
    (cap_parent_prefix_register state 4 (by decide) reg outside)

theorem cap_parent_answer_marks (state : MachineState) (node : Nat)
    (answer : BitVec 256) (marked : Nat → Bool)
    (roots : state.getReg .x18 = 12288)
    (index : state.getReg .x20 = BitVec.ofNat 64 node) (bounded : node < 256)
    (ready : CapMarksReady state 256 0 marked) :
    CapMarksReady (capParentAnswerState state answer) 256 0 marked := by
  apply cap_compression_ready (capParentPrefix state 4) (12288 + 32 * node) answer marked
  · exact cap_parent_destination state node roots index
  · omega
  · exact cap_marks_ready_memory state (capParentPrefix state 4) 256 0 marked
      (cap_parent_prefix_memory state 4 (by decide)) ready

theorem cap_parent_answer_high (state reference : MachineState) (node : Nat)
    (answer : BitVec 256) (roots : state.getReg .x18 = 12288)
    (index : state.getReg .x20 = BitVec.ofNat 64 node) (bounded : node < 256)
    (frame : CapHighBytes state reference) :
    CapHighBytes (capParentAnswerState state answer) reference := by
  apply cap_compression_high_bytes (capParentPrefix state 4) reference
    (12288 + 32 * node) answer
  · exact cap_parent_destination state node roots index
  · omega
  · exact cap_high_bytes_memory state (capParentPrefix state 4) reference
      (cap_parent_prefix_memory state 4 (by decide)) frame

end CommitGolfCandidate
