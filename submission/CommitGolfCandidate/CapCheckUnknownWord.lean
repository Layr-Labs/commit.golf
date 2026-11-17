import CommitGolfCandidate.CapCheckWordSuffix

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false
attribute [local irreducible] readBuffer

theorem cap_check_unknown_word (oracle : Oracle) (limit : Nat)
    (marked : Nat → Bool) (node : Nat) (state : MachineState)
    (cursor : Nat) (head : Digest) (words : List Digest) (tailBytes : Nat)
    (ready : CapCheckDfsReady limit marked (.visit node) state)
    (suffix : CapCheckWordSuffix state cursor (head::words) tailBytes)
    (absent : marked node=false) :
    capCheckDfsShort marked (.visit node) state=false ∧
      CapCheckWordSuffix (capCheckDfsNext oracle marked (.visit node) state)
        (cursor+32) words tailBytes ∧
      capReadRoot (capCheckDfsNext oracle marked (.visit node) state) node=head := by
  have notShort : capCheckDfsShort marked (.visit node) state=false := by
    rw [cap_check_word_suffix_short marked node state cursor (head::words)
      tailBytes suffix absent]
    simp only [reduceCtorEq,decide_false]
  have reached := cap_check_next_supported oracle marked (.visit node) state
  have frame := cap_dfs_check_step_high limit marked (.visit node) state _
    state ready (cap_high_bytes_refl state) reached
  have pointer := cap_dfs_check_cursor_effect marked (.visit node) state _ cursor
    suffix.pointer reached
  simp only [capBoundaryIncrement,absent,Bool.false_eq_true,↓reduceIte] at pointer
  have endPointer := cap_dfs_check_end_pointer marked (.visit node) state _ reached
  have transported := cap_check_word_suffix_tail state _ cursor head words tailBytes
    suffix frame pointer endPointer
  have small := cap_check_word_suffix_small state cursor (head::words) tailBytes suffix
  have numeric : (state.getReg .x25).toNat=cursor := by
    rw [suffix.pointer,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small.1]
  have root := cap_check_dfs_next_roots oracle limit marked (.visit node) state
    ready (by rw [numeric]; exact suffix.high) node ready.valid.2
  simp only [capCheckRootStep,absent,Bool.false_eq_true,↓reduceIte,if_pos rfl,numeric] at root
  have first := suffix.slots 0 (by simp only [List.length_cons]; omega)
  simp only [Nat.mul_zero,Nat.add_zero,List.getElem_cons_zero] at first
  exact ⟨notShort,transported,root.trans first⟩

theorem cap_check_nonconsuming_words (oracle : Oracle) (limit : Nat)
    (marked : Nat → Bool) (control : CapDfsControl) (state : MachineState)
    (cursor : Nat) (words : List Digest) (tailBytes : Nat)
    (ready : CapCheckDfsReady limit marked control state)
    (suffix : CapCheckWordSuffix state cursor words tailBytes)
    (noIncrement : capBoundaryIncrement marked control=0) :
    CapCheckWordSuffix (capCheckDfsNext oracle marked control state)
      cursor words tailBytes := by
  have reached := cap_check_next_supported oracle marked control state
  have frame := cap_dfs_check_step_high limit marked control state _
    state ready (cap_high_bytes_refl state) reached
  have pointer := cap_dfs_check_cursor_effect marked control state _ cursor
    suffix.pointer reached
  simp only [noIncrement,Nat.add_zero] at pointer
  exact cap_check_word_suffix_frame state _ cursor words tailBytes suffix frame
    (pointer.trans suffix.pointer.symm)
    (cap_dfs_check_end_pointer marked control state _ reached)

end CommitGolfCandidate
