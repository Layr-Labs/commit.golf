import CommitGolfCandidate.CapCheckDfsSegments

/-! Recursive segmentation of the actual checker fold. Each segment retains
its physical state and rejection flag; a rejected child never runs its sibling
or its parent compression. This is an order theorem, independent of digest
correctness and byte admission. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false

def capCheckSubtreeValue (oracle : Oracle) (marked : Nat → Bool) :
    Nat → Nat → MachineState → MachineState × Bool
  | 0,node,state => capCheckDfsValue oracle marked 1 (.visit node) state
  | height+1,node,state =>
      if marked node then
        capCheckValueThen (capCheckDfsValue oracle marked 1 (.visit node) state)
          (fun entered =>
            capCheckValueThen (capCheckSubtreeValue oracle marked height (2*node) entered)
              (fun left =>
                capCheckValueThen (capCheckDfsValue oracle marked 1 (.advance (2*node)) left)
                  (fun sibling =>
                    capCheckValueThen
                      (capCheckSubtreeValue oracle marked height (2*node+1) sibling)
                      (capCheckDfsValue oracle marked 1 (.advance (2*node+1))))))
      else capCheckDfsValue oracle marked 1 (.visit node) state

private theorem children (height node : Nat)
    (lower : 256 ≤ node*2^(height+1))
    (upper : (node+1)*2^(height+1) ≤ 512) :
    0<node ∧ node<256 ∧
      256≤(2*node)*2^height ∧ (2*node+1)*2^height≤ 512 ∧
      256≤(2*node+1)*2^height ∧ (2*node+2)*2^height≤ 512 := by
  have power := Nat.two_pow_pos height
  rw [pow_succ] at lower upper
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem cap_check_subtree_value (oracle : Oracle) (marked : Nat → Bool)
    (height node : Nat) (state : MachineState)
    (lower : 256≤node*2^height) (upper : (node+1)*2^height≤ 512) :
    capCheckDfsValue oracle marked (capSubtreeSteps marked height node) (.visit node) state =
      capCheckSubtreeValue oracle marked height node state := by
  induction height generalizing node state with
  | zero => rfl
  | succ height ih =>
    obtain ⟨positive,internal,ll,lu,rl,ru⟩ := children height node lower upper
    by_cases present : marked node=true
    · have leftEnd := cap_subtree_run_end marked height (2*node) ll lu
      have rightEnd := cap_subtree_run_end marked height (2*node+1) rl ru
      have enter : capControlRun marked 1 (.visit node) = .visit (2*node) := by
        simp [capControlRun,capControlStep,present,internal]
      have sibling : capControlRun marked 1 (.advance (2*node)) =
          .visit (2*node+1) := by
        have notRoot : 2*node≠1 := by omega
        simp [capControlRun,capControlStep,notRoot]
      have count :
          1+capSubtreeSteps marked height (2*node)+1+
            capSubtreeSteps marked height (2*node+1)+1 =
          1+(capSubtreeSteps marked height (2*node)+
            (1+(capSubtreeSteps marked height (2*node+1)+1))) := by omega
      rw [capSubtreeSteps,if_pos present,count,
        cap_check_dfs_value_add oracle marked 1
          (capSubtreeSteps marked height (2*node)+
            (1+(capSubtreeSteps marked height (2*node+1)+1))),enter,
        capCheckSubtreeValue,if_pos present]
      apply congrArg (capCheckValueThen (capCheckDfsValue oracle marked 1 (.visit node) state))
      funext entered
      rw [cap_check_dfs_value_add oracle marked
        (capSubtreeSteps marked height (2*node))
          (1+(capSubtreeSteps marked height (2*node+1)+1)),leftEnd,
        ih (2*node) entered ll lu]
      apply congrArg (capCheckValueThen (capCheckSubtreeValue oracle marked height (2*node) entered))
      funext left
      rw [
        cap_check_dfs_value_add oracle marked 1
          (capSubtreeSteps marked height (2*node+1)+1),sibling]
      apply congrArg (capCheckValueThen (capCheckDfsValue oracle marked 1 (.advance (2*node)) left))
      funext siblingState
      rw [
        cap_check_dfs_value_add oracle marked
          (capSubtreeSteps marked height (2*node+1)) 1,rightEnd,
        ih (2*node+1) siblingState rl ru]
    · simp only [capSubtreeSteps,capCheckSubtreeValue,if_neg present]

end CommitGolfCandidate
