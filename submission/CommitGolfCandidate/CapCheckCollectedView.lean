import CommitGolfCandidate.CapCheckKnownLeaves
import CommitGolfCandidate.CapCheckKnownMarks

/-! The duplicate-checked collected map supplies the exact known-leaf payloads
of the cap decoder. Internal roots remain unconstrained until traversal. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false

theorem cap_check_collected_view_leaves (state : MachineState) (roots : CapRootMap)
    (collected : CapCheckCollected state roots) (height offset node : Nat)
    (address : offset+128=node*2^height)
    (bounded : offset+2^height≤128) :
    CapCheckKnownLeaves state node (capKnownView roots height offset) := by
  induction height generalizing offset node with
  | zero =>
    have nodeEq : node=offset+128 := by simpa using address.symm
    have offsetBound : offset<128 := by
      have bound : offset+1≤128 := by simpa using bounded
      omega
    intro digest known
    have payload : roots offset=some digest := known
    have stored := collected.roots offset offsetBound digest payload
    simpa only [capReadRoot,capCheckRootAddress,nodeEq,Nat.add_comm offset 128] using stored
  | succ height ih =>
    have power := Nat.two_pow_pos height
    have address' := address
    rw [pow_succ] at address'
    have bounded' := bounded
    rw [pow_succ] at bounded'
    exact ⟨ih offset (2*node) (by nlinarith) (by nlinarith),
      ih (offset+2^height) (2*node+1) (by nlinarith) (by nlinarith)⟩

theorem cap_check_collected_root_view (state : MachineState) (roots : CapRootMap)
    (collected : CapCheckCollected state roots) :
    CapCheckKnownLeaves state 1 (capKnownView roots 7 0) :=
  cap_check_collected_view_leaves state roots collected 7 0 1 (by decide) (by decide)

end CommitGolfCandidate
