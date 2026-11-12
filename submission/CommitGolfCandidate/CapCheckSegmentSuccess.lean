import CommitGolfCandidate.CapCheckSubtreeValue
import CommitGolfCandidate.CapCheckKnownRootFrame

/-! Successful composition exposes each reached child phase without treating
its success flag as final acceptance. These lemmas keep the actual states for
the subsequent memory, cursor and root-codec induction. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false

theorem cap_check_value_then_success (head : MachineState × Bool)
    (tail : MachineState → MachineState × Bool)
    (passed : (capCheckValueThen head tail).2=true) :
    head.2=true ∧ capCheckValueThen head tail=tail head.1 ∧
      (tail head.1).2=true := by
  cases flag : head.2
  · simp only [capCheckValueThen,flag,Bool.false_eq_true,↓reduceIte] at passed
  · simp only [capCheckValueThen,flag,↓reduceIte] at passed ⊢
    exact ⟨trivial,trivial,passed⟩

theorem cap_check_subtree_ready (oracle : Oracle) (limit : Nat)
    (marked : Nat → Bool) (height node : Nat) (state : MachineState)
    (lower : 256≤node*2^height) (upper : (node+1)*2^height≤512)
    (ready : CapCheckDfsReady limit marked (.visit node) state)
    (passed : (capCheckSubtreeValue oracle marked height node state).2=true) :
    CapCheckDfsReady limit marked (.advance node)
      (capCheckSubtreeValue oracle marked height node state).1 := by
  have result := cap_check_dfs_value_ready oracle limit marked
    (capSubtreeSteps marked height node) (.visit node) state ready
    (by rw [cap_check_subtree_value oracle marked height node state lower upper]; exact passed)
  rw [cap_subtree_run_end marked height node lower upper,
    cap_check_subtree_value oracle marked height node state lower upper] at result
  exact result

theorem cap_check_subtree_known_root (oracle : Oracle) (limit : Nat)
    (marked : Nat → Bool) (height node : Nat) (state : MachineState)
    (lower : 256≤node*2^height) (upper : (node+1)*2^height≤512)
    (ready : CapCheckDfsReady limit marked (.visit node) state)
    (above : 32768≤(state.getReg .x25).toNat)
    (leaf : Nat) (leafLower : 256≤leaf) (leafUpper : leaf<512)
    (known : marked leaf=true)
    (passed : (capCheckSubtreeValue oracle marked height node state).2=true) :
    capReadRoot (capCheckSubtreeValue oracle marked height node state).1 leaf=
        capReadRoot state leaf ∧
      (state.getReg .x25).toNat≤
        ((capCheckSubtreeValue oracle marked height node state).1.getReg .x25).toNat := by
  have result := cap_check_value_known_root oracle limit marked
    (capSubtreeSteps marked height node) (.visit node) state ready above
    leaf leafLower leafUpper known
    (by rw [cap_check_subtree_value oracle marked height node state lower upper]; exact passed)
  rw [cap_check_subtree_value oracle marked height node state lower upper] at result
  exact result

end CommitGolfCandidate
