import CommitGolfCandidate.CapCheckCodecNavigation

/-! A decoder result is related to the actual traversal state and rejection
flag. Successful decoding retains an exact remaining-word/partial-tail
invariant and physical readiness; failed decoding must reject. The flag here
describes only traversal completion, not final proof/root acceptance. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false
attribute [local irreducible] capCheckDfsNext capCheckDfsValue capCheckSubtreeValue

def CapCheckCodecResult (limit : Nat) (marked : Nat → Bool) (node tailBytes : Nat)
    (result : MachineState × Bool) : Option (Digest × List Digest) → Prop
  | none => result.2=false
  | some (root,rest) =>
      result.2=true ∧ capReadRoot result.1 node=root ∧
        ∃ cursor, CapCheckWordSuffix result.1 cursor rest tailBytes ∧
          CapCheckDfsReady limit marked (.advance node) result.1

theorem cap_decode_unoccupied (compress : Compression) {height : Nat}
    (view : CapView height) (words : List Digest)
    (empty : capOccupied view=false) :
    capDecode compress view words=
      match words with
      | [] => none
      | head::rest => some (head,rest) := by
  cases view <;> simp only [capDecode,empty,Bool.false_eq_true,↓reduceIte]
  all_goals cases words <;> rfl

theorem cap_check_codec_result_unknown (oracle : Oracle) (limit : Nat)
    (marked : Nat → Bool) {height : Nat} (view : CapView height)
    (node : Nat) (state : MachineState) (cursor : Nat)
    (words : List Digest) (tailBytes : Nat)
    (ready : CapCheckDfsReady limit marked (.visit node) state)
    (suffix : CapCheckWordSuffix state cursor words tailBytes)
    (marks : CapViewMarks marked node view)
    (empty : capOccupied view=false) :
    CapCheckCodecResult limit marked node tailBytes
      (capCheckSubtreeValue oracle marked height node state)
      (capDecode (s6Compress oracle.compression) view words) := by
  have absent : marked node=false := (cap_check_view_mark view marked node marks).trans empty
  rw [cap_decode_unoccupied (s6Compress oracle.compression) view words empty]
  cases words with
  | nil =>
    change (capCheckSubtreeValue oracle marked height node state).2=false
    exact cap_check_unknown_subtree_short oracle marked height node state
      cursor tailBytes suffix absent
  | cons head rest =>
    have actual := cap_check_unknown_subtree oracle limit marked height node state
      cursor head rest tailBytes ready suffix absent
    change (capCheckSubtreeValue oracle marked height node state).2=true ∧
      capReadRoot (capCheckSubtreeValue oracle marked height node state).1 node=head ∧
      ∃ nextCursor, CapCheckWordSuffix
        (capCheckSubtreeValue oracle marked height node state).1 nextCursor rest tailBytes ∧
        CapCheckDfsReady limit marked (.advance node)
          (capCheckSubtreeValue oracle marked height node state).1
    exact ⟨actual.1,actual.2.1,cursor+32,actual.2.2.1,actual.2.2.2⟩

theorem cap_check_codec_result_leaf (oracle : Oracle) (limit : Nat)
    (marked : Nat → Bool) (known : Option Digest) (node : Nat)
    (state : MachineState) (cursor : Nat) (words : List Digest) (tailBytes : Nat)
    (ready : CapCheckDfsReady limit marked (.visit node) state)
    (suffix : CapCheckWordSuffix state cursor words tailBytes)
    (lower : 256≤node)
    (marks : CapViewMarks marked node (.leaf known))
    (payload : CapCheckKnownLeaves state node (.leaf known)) :
    CapCheckCodecResult limit marked node tailBytes
      (capCheckSubtreeValue oracle marked 0 node state)
      (capDecode (s6Compress oracle.compression) (.leaf known) words) := by
  cases known with
  | none =>
    exact cap_check_codec_result_unknown oracle limit marked (.leaf none)
      node state cursor words tailBytes ready suffix marks rfl
  | some digest =>
    have present : marked node=true := marks
    have actual := cap_check_known_leaf_value oracle limit marked node state
      cursor words tailBytes digest ready suffix lower present (payload digest rfl)
    simp only [capDecode,capOccupied,Option.isSome_some,↓reduceIte,
      Option.map_some,CapCheckCodecResult]
    exact ⟨actual.1,actual.2.1,cursor,actual.2.2.1,actual.2.2.2⟩

end CommitGolfCandidate
