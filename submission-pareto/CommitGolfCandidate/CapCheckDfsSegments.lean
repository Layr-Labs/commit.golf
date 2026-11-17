import CommitGolfCandidate.CapCheckDfsEvaluation
import CommitGolfCandidate.CapDfsSubtree

/-! Segment composition of the actual fixed-oracle DFS fold. A failed guard
ends the segment immediately and cannot resume a later subtree. The static
control endpoint is used only when the preceding state result passed. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false

def capCheckValueThen (head : MachineState × Bool)
    (tail : MachineState → MachineState × Bool) : MachineState × Bool :=
  if head.2 then tail head.1 else head

theorem cap_check_value_then_assoc (head : MachineState × Bool)
    (middle tail : MachineState → MachineState × Bool) :
    capCheckValueThen (capCheckValueThen head middle) tail =
      capCheckValueThen head (fun state => capCheckValueThen (middle state) tail) := by
  cases passed : head.2 <;>
    simp only [capCheckValueThen,passed,Bool.false_eq_true,↓reduceIte]

theorem cap_check_dfs_value_head (oracle : Oracle) (marked : Nat → Bool)
    (count : Nat) (control : CapDfsControl) (state : MachineState) :
    capCheckDfsValue oracle marked (count+1) control state =
      capCheckValueThen (capCheckDfsValue oracle marked 1 control state)
        (capCheckDfsValue oracle marked count (capControlStep marked control)) := by
  rw [capCheckDfsValue]
  cases short : capCheckDfsShort marked control state <;>
    simp only [capCheckDfsValue,short,Bool.false_eq_true,↓reduceIte,capCheckValueThen]

theorem cap_check_dfs_value_add (oracle : Oracle) (marked : Nat → Bool)
    (first second : Nat) (control : CapDfsControl) (state : MachineState) :
    capCheckDfsValue oracle marked (first+second) control state =
      capCheckValueThen (capCheckDfsValue oracle marked first control state)
        (capCheckDfsValue oracle marked second (capControlRun marked first control)) := by
  induction first generalizing control state with
  | zero =>
    simp only [Nat.zero_add,capCheckDfsValue,capControlRun,capCheckValueThen,↓reduceIte]
  | succ first ih =>
    rw [Nat.succ_add]
    conv_lhs => rw [cap_check_dfs_value_head oracle marked (first+second)]
    conv_rhs => rw [cap_check_dfs_value_head oracle marked first]
    rw [cap_check_value_then_assoc]
    change capCheckValueThen (capCheckDfsValue oracle marked 1 control state)
      (capCheckDfsValue oracle marked (first+second) (capControlStep marked control)) =
      capCheckValueThen (capCheckDfsValue oracle marked 1 control state)
        (fun next => capCheckValueThen
          (capCheckDfsValue oracle marked first (capControlStep marked control) next)
          (capCheckDfsValue oracle marked second
            (capControlRun marked first (capControlStep marked control))))
    exact congrArg
      (capCheckValueThen (capCheckDfsValue oracle marked 1 control state))
      (funext (ih (capControlStep marked control)))

end CommitGolfCandidate
