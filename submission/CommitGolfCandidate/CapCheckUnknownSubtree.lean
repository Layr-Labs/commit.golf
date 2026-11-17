import CommitGolfCandidate.CapCheckOneValue
import CommitGolfCandidate.CapCheckKnownLeaves

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false

theorem cap_check_view_mark {height : Nat} (view : CapView height)
    (marked : Nat → Bool) (node : Nat)
    (marks : CapViewMarks marked node view) :
    marked node=capOccupied view := by
  cases view with
  | leaf known => exact marks
  | node left right => exact marks.1

theorem cap_check_unknown_subtree (oracle : Oracle) (limit : Nat)
    (marked : Nat → Bool) (height node : Nat) (state : MachineState)
    (cursor : Nat) (head : Digest) (words : List Digest) (tailBytes : Nat)
    (ready : CapCheckDfsReady limit marked (.visit node) state)
    (suffix : CapCheckWordSuffix state cursor (head::words) tailBytes)
    (absent : marked node=false) :
    let result := capCheckSubtreeValue oracle marked height node state
    result.2=true ∧ capReadRoot result.1 node=head ∧
      CapCheckWordSuffix result.1 (cursor+32) words tailBytes ∧
      CapCheckDfsReady limit marked (.advance node) result.1 := by
  have step := cap_check_unknown_word oracle limit marked node state cursor
    head words tailBytes ready suffix absent
  have nextReady := cap_check_dfs_ready_transport limit marked (.visit node)
    state _ ready step.1 (cap_check_next_supported oracle marked (.visit node) state)
  have control : capControlStep marked (.visit node)=.advance node := by
    simp [capControlStep,absent]
  rw [control] at nextReady
  have value := cap_check_one_value oracle marked (.visit node) state step.1
  cases height <;>
    simp only [capCheckSubtreeValue,absent,Bool.false_eq_true,↓reduceIte,value]
  · exact ⟨trivial,step.2.2,step.2.1,nextReady⟩
  · exact ⟨trivial,step.2.2,step.2.1,nextReady⟩

theorem cap_check_unknown_subtree_short (oracle : Oracle) (marked : Nat → Bool)
    (height node : Nat) (state : MachineState) (cursor tailBytes : Nat)
    (suffix : CapCheckWordSuffix state cursor [] tailBytes)
    (absent : marked node=false) :
    (capCheckSubtreeValue oracle marked height node state).2=false := by
  have short : capCheckDfsShort marked (.visit node) state=true := by
    rw [cap_check_word_suffix_short marked node state cursor [] tailBytes suffix absent]
    rfl
  have value := cap_check_one_short oracle marked (.visit node) state short
  cases height <;>
    simpa only [capCheckSubtreeValue,absent,Bool.false_eq_true,↓reduceIte] using value

end CommitGolfCandidate
