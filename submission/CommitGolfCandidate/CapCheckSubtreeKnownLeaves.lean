import CommitGolfCandidate.CapCheckKnownLeaves

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false
attribute [local irreducible] capCheckDfsValue capCheckSubtreeValue

theorem cap_check_subtree_known_leaves (oracle : Oracle) (limit : Nat)
    (marked : Nat → Bool) (height node : Nat) (state : MachineState)
    (lower : 256≤node*2^height) (upper : (node+1)*2^height≤512)
    (ready : CapCheckDfsReady limit marked (.visit node) state)
    (above : 32768≤(state.getReg .x25).toNat)
    {viewHeight : Nat} (view : CapView viewHeight) (viewNode : Nat)
    (viewLower : 256≤viewNode*2^viewHeight)
    (viewUpper : (viewNode+1)*2^viewHeight≤512)
    (marks : CapViewMarks marked viewNode view)
    (known : CapCheckKnownLeaves state viewNode view)
    (passed : (capCheckSubtreeValue oracle marked height node state).2=true) :
    CapCheckKnownLeaves (capCheckSubtreeValue oracle marked height node state).1
      viewNode view := by
  have actualPassed :
      (capCheckDfsValue oracle marked (capSubtreeSteps marked height node)
        (.visit node) state).2=true := by
    rw [cap_check_subtree_value oracle marked height node state lower upper]
    exact passed
  have result := cap_check_value_known_leaves oracle limit marked
    (capSubtreeSteps marked height node) (.visit node) state ready above
    view viewNode viewLower viewUpper marks known actualPassed
  rw [cap_check_subtree_value oracle marked height node state lower upper] at result
  exact result

end CommitGolfCandidate
