import CommitGolfCandidate.CapCheckCodecResult

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false
attribute [local irreducible] capCheckDfsNext

theorem cap_check_codec_known_frame (oracle : Oracle) (limit : Nat)
    (marked : Nat → Bool) (control : CapDfsControl) (state : MachineState)
    (cursor : Nat) (words : List Digest) (tailBytes : Nat)
    (ready : CapCheckDfsReady limit marked control state)
    (suffix : CapCheckWordSuffix state cursor words tailBytes)
    (notShort : capCheckDfsShort marked control state=false)
    {height : Nat} (view : CapView height) (node : Nat)
    (lower : 256≤node*2^height) (upper : (node+1)*2^height≤512)
    (marks : CapViewMarks marked node view)
    (known : CapCheckKnownLeaves state node view) :
    CapCheckKnownLeaves (capCheckDfsNext oracle marked control state) node view := by
  have small := cap_check_word_suffix_small state cursor words tailBytes suffix
  have above : 32768≤(state.getReg .x25).toNat := by
    rw [suffix.pointer,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small.1]
    exact suffix.high
  have one := cap_check_one_value oracle marked control state notShort
  have framed := cap_check_value_known_leaves oracle limit marked 1 control state
    ready above view node lower upper marks known (by rw [one])
  rw [one] at framed
  exact framed

theorem cap_check_codec_enter (oracle : Oracle) (limit : Nat)
    (marked : Nat → Bool) (node : Nat) (state : MachineState)
    (cursor : Nat) (words : List Digest) (tailBytes : Nat)
    (ready : CapCheckDfsReady limit marked (.visit node) state)
    (suffix : CapCheckWordSuffix state cursor words tailBytes)
    (internal : node<256) (present : marked node=true) :
    CapCheckWordSuffix (capCheckDfsNext oracle marked (.visit node) state)
        cursor words tailBytes ∧
      CapCheckDfsReady limit marked (.visit (2*node))
        (capCheckDfsNext oracle marked (.visit node) state) := by
  have result := cap_check_codec_navigation oracle limit marked (.visit node)
    state cursor words tailBytes ready suffix
    (by simp only [capCheckDfsShort,present,↓reduceIte])
    (by simp only [capBoundaryIncrement,present,↓reduceIte])
  simpa [capControlStep,present,internal] using result

theorem cap_check_codec_sibling (oracle : Oracle) (limit : Nat)
    (marked : Nat → Bool) (node : Nat) (state : MachineState)
    (cursor : Nat) (words : List Digest) (tailBytes : Nat)
    (ready : CapCheckDfsReady limit marked (.advance (2*node)) state)
    (suffix : CapCheckWordSuffix state cursor words tailBytes)
    (positive : 0<node) (bounded : node<256) :
    CapCheckWordSuffix (capCheckDfsNext oracle marked (.advance (2*node)) state)
        cursor words tailBytes ∧
      CapCheckDfsReady limit marked (.visit (2*node+1))
        (capCheckDfsNext oracle marked (.advance (2*node)) state) ∧
      capReadRoot (capCheckDfsNext oracle marked (.advance (2*node)) state) (2*node)=
        capReadRoot state (2*node) := by
  have nonroot : 2*node≠1 := by omega
  have even : (2*node)%2=0 := by omega
  have result := cap_check_codec_navigation oracle limit marked (.advance (2*node))
    state cursor words tailBytes ready suffix rfl rfl
  have control : capControlStep marked (.advance (2*node))=.visit (2*node+1) := by
    simp only [capControlStep,nonroot,even,↓reduceIte]
  rw [control] at result
  have small := cap_check_word_suffix_small state cursor words tailBytes suffix
  have root := cap_check_dfs_next_roots oracle limit marked (.advance (2*node))
    state ready (by
      rw [suffix.pointer,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small.1]
      exact suffix.high) (2*node) (by omega)
  simp only [capCheckRootStep,even,or_true,↓reduceIte] at root
  exact ⟨result.1,result.2,root⟩

end CommitGolfCandidate
