import CommitGolfCandidate.CapCheckUnknownSubtree
import CommitGolfCandidate.CapCheckRootSegmentFrame

/-! Non-consuming navigation keeps the exact remaining proof words and byte
tail. The parent transition reads the two reconstructed children and performs
the same compression as the recursive decoder. Actual admission stays in the
reachable-state invariant. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false

theorem cap_check_codec_navigation (oracle : Oracle) (limit : Nat)
    (marked : Nat → Bool) (control : CapDfsControl) (state : MachineState)
    (cursor : Nat) (words : List Digest) (tailBytes : Nat)
    (ready : CapCheckDfsReady limit marked control state)
    (suffix : CapCheckWordSuffix state cursor words tailBytes)
    (notShort : capCheckDfsShort marked control state=false)
    (noIncrement : capBoundaryIncrement marked control=0) :
    CapCheckWordSuffix (capCheckDfsNext oracle marked control state)
        cursor words tailBytes ∧
      CapCheckDfsReady limit marked (capControlStep marked control)
        (capCheckDfsNext oracle marked control state) := by
  exact ⟨cap_check_nonconsuming_words oracle limit marked control state
      cursor words tailBytes ready suffix noIncrement,
    cap_check_dfs_ready_transport limit marked control state _ ready notShort
      (cap_check_next_supported oracle marked control state)⟩

theorem cap_check_codec_parent (oracle : Oracle) (limit : Nat)
    (marked : Nat → Bool) (node : Nat) (state : MachineState)
    (cursor : Nat) (words : List Digest) (tailBytes : Nat)
    (ready : CapCheckDfsReady limit marked (.advance (2*node+1)) state)
    (suffix : CapCheckWordSuffix state cursor words tailBytes)
    (positive : 0<node) (bounded : node<256) :
    capReadRoot (capCheckDfsNext oracle marked (.advance (2*node+1)) state) node=
      combine oracle.compression (capReadRoot state (2*node))
        (capReadRoot state (2*node+1)) := by
  have small := cap_check_word_suffix_small state cursor words tailBytes suffix
  have numeric : (state.getReg .x25).toNat=cursor := by
    rw [suffix.pointer,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small.1]
  have root := cap_check_dfs_next_roots oracle limit marked
    (.advance (2*node+1)) state ready
    (by rw [numeric]; exact suffix.high) node (by omega)
  have nonroot : 2*node+1≠1 := by omega
  have odd : (2*node+1)%2≠0 := by omega
  have half : (2*node+1)/2=node := by omega
  simpa only [capCheckRootStep,nonroot,odd,false_or,↓reduceIte,half,if_pos rfl]
    using root

end CommitGolfCandidate
