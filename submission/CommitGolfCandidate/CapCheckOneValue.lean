import CommitGolfCandidate.CapCheckUnknownWord
import CommitGolfCandidate.CapCheckSegmentSuccess
import CommitGolfCandidate.CapCheckPairResult

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false
attribute [local irreducible] capCheckDfsNext capCheckDfsValue capCheckSubtreeValue

theorem cap_check_one_value (oracle : Oracle) (marked : Nat → Bool)
    (control : CapDfsControl) (state : MachineState)
    (notShort : capCheckDfsShort marked control state=false) :
    capCheckDfsValue oracle marked 1 control state=
      (capCheckDfsNext oracle marked control state,true) := by
  simp only [capCheckDfsValue,notShort,Bool.false_eq_true,↓reduceIte]

theorem cap_check_one_short (oracle : Oracle) (marked : Nat → Bool)
    (control : CapDfsControl) (state : MachineState)
    (short : capCheckDfsShort marked control state=true) :
    (capCheckDfsValue oracle marked 1 control state).2=false := by
  simp only [capCheckDfsValue,short,↓reduceIte]

theorem cap_check_known_leaf_value (oracle : Oracle) (limit : Nat)
    (marked : Nat → Bool) (node : Nat) (state : MachineState)
    (cursor : Nat) (words : List Digest) (tailBytes : Nat) (digest : Digest)
    (ready : CapCheckDfsReady limit marked (.visit node) state)
    (suffix : CapCheckWordSuffix state cursor words tailBytes)
    (lower : 256≤node) (present : marked node=true)
    (payload : capReadRoot state node=digest) :
    let result := capCheckSubtreeValue oracle marked 0 node state
    result.2=true ∧ capReadRoot result.1 node=digest ∧
      CapCheckWordSuffix result.1 cursor words tailBytes ∧
      CapCheckDfsReady limit marked (.advance node) result.1 := by
  have notShort : capCheckDfsShort marked (.visit node) state=false := by
    simp only [capCheckDfsShort,present,↓reduceIte]
  have one := cap_check_one_value oracle marked (.visit node) state notShort
  have small := cap_check_word_suffix_small state cursor words tailBytes suffix
  have above : 32768≤(state.getReg .x25).toNat := by
    rw [suffix.pointer,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small.1]
    exact suffix.high
  have stored := cap_check_next_known_root oracle limit marked (.visit node) state
    ready above node lower ready.valid.2 present
  have wordsNext := cap_check_nonconsuming_words oracle limit marked (.visit node)
    state cursor words tailBytes ready suffix (by
      simp only [capBoundaryIncrement,present,↓reduceIte])
  have nextReady := cap_check_dfs_ready_transport limit marked (.visit node) state _
    ready notShort (cap_check_next_supported oracle marked (.visit node) state)
  have control : capControlStep marked (.visit node)=.advance node := by
    simp [capControlStep,present,Nat.not_lt.mpr lower]
  rw [control] at nextReady
  have equal :
      capCheckSubtreeValue oracle marked 0 node state=
        (capCheckDfsNext oracle marked (.visit node) state,true) := by
    rw [capCheckSubtreeValue]
    exact one
  exact cap_check_pair_result limit marked node
    (capCheckSubtreeValue oracle marked 0 node state)
    (capCheckDfsNext oracle marked (.visit node) state) cursor words tailBytes digest
    equal (stored.trans payload) wordsNext nextReady

end CommitGolfCandidate
