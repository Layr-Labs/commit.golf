import CommitGolfCandidate.CapParentExecute

/-! Parent reconstruction updates exactly one root slot. The arbitrary reply
is observable at that parent; every other slot remains unchanged. This frame
is separate from preservation of occupancy marks and high ABI input bytes. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
attribute [local irreducible] readBuffer capParentPrefix

def capReadRoot (state : MachineState) (node : Nat) : BitVec 256 :=
  readBuffer state (12288 + 32 * node) 32

theorem cap_parent_answer_root (state : MachineState) (node : Nat)
    (answer : BitVec 256) (roots : state.getReg .x18 = 12288)
    (index : state.getReg .x20 = BitVec.ofNat 64 node) :
    capReadRoot (capParentAnswerState state answer) node = answer := by
  exact cap_compression_answer_digest (capParentPrefix state 4) (12288 + 32 * node)
    answer (cap_parent_destination state node roots index)

theorem cap_parent_answer_other_root (state : MachineState) (node other : Nat)
    (answer : BitVec 256) (roots : state.getReg .x18 = 12288)
    (index : state.getReg .x20 = BitVec.ofNat 64 node)
    (parentBound : node < 128) (otherBound : other < 256) (distinct : other ≠ node) :
    capReadRoot (capParentAnswerState state answer) other = capReadRoot state other := by
  unfold capReadRoot capParentAnswerState capCompressionAnswer
  rw [cap_parent_destination state node roots index]
  unfold capRootAddress
  rw [write_bits_read_outside (capParentPrefix state 4) answer
    (12288 + 32 * node) (12288 + 32 * other) 32
    (by omega) (by omega) (by omega)]
  exact read_buffer_memory_congr (capParentPrefix state 4) state
    (cap_parent_prefix_memory state 4 (by decide)) _ _

/-- The root-memory projection is a point update, without full-state equality. -/
theorem cap_parent_answer_root_map (state : MachineState) (node : Nat)
    (answer : BitVec 256) (roots : state.getReg .x18 = 12288)
    (index : state.getReg .x20 = BitVec.ofNat 64 node)
    (parentBound : node < 128) (other : Nat) (otherBound : other < 256) :
    capReadRoot (capParentAnswerState state answer) other =
      if other = node then answer else capReadRoot state other := by
  by_cases same : other = node
  · subst other
    rw [if_pos rfl]
    exact cap_parent_answer_root state node answer roots index
  · rw [if_neg same]
    exact cap_parent_answer_other_root state node other answer roots index
      parentBound otherBound same

theorem cap_parent_query_roots (state : MachineState) (node : Nat)
    (roots : state.getReg .x18 = 12288)
    (index : state.getReg .x20 = BitVec.ofNat 64 node) (bounded : node < 128) :
    capCompressionInput (capParentPrefix state 4) =
      .inl (capReadRoot state (2 * node + 1) ++ capReadRoot state (2 * node)) := by
  rw [cap_parent_query state node roots index bounded]
  unfold capReadRoot
  rw [show 12288 + 32 * (2 * node + 1) = 12288 + 64 * node + 32 by omega,
    show 12288 + 32 * (2 * node) = 12288 + 64 * node by omega]

end CommitGolfCandidate
