import CommitGolfCandidate.CapDfsSerialization
import CommitGolfCandidate.CapDfsCostBound

/-! Exact static compression count of the iterative cap traversal. Finalized
marks identify the same occupied view as the recursive decoder. Unknown
boundary copies use no queries; each occupied internal node is compressed
once. This control theorem is independent of oracle replies and proof bytes. -/
namespace CommitGolfCandidate
open CommitGolf
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false

theorem cap_dfs_query_total_add (marked : Nat → Bool) (first second : Nat)
    (control : CapDfsControl) :
    capDfsQueryTotal true marked (first+second) control=
      capDfsQueryTotal true marked first control+
        capDfsQueryTotal true marked second (capControlRun marked first control) := by
  induction first generalizing control with
  | zero => simp only [Nat.zero_add,capDfsQueryTotal,capControlRun]
  | succ first ih =>
    simp only [Nat.succ_add,capDfsQueryTotal,capControlRun,ih,Nat.add_assoc]

theorem cap_subtree_query_count (marked : Nat → Bool) {height : Nat}
    (view : CapView height) (node : Nat)
    (lower : 256≤node*2^height) (upper : (node+1)*2^height≤512)
    (marks : CapViewMarks marked node view) :
    capDfsQueryTotal true marked (capSubtreeSteps marked height node) (.visit node)=
      capCalls view := by
  induction view generalizing node with
  | leaf known =>
    simp only [capSubtreeSteps,capDfsQueryTotal,capDfsStepQueries,capCalls,Nat.zero_add]
  | @node height leftView rightView leftIH rightIH =>
    have power : 0<2^height := Nat.two_pow_pos height
    have lower' := lower
    have upper' := upper
    rw [pow_succ] at lower' upper'
    have positive : 0<node := by nlinarith
    have internal : node<256 := by nlinarith
    have leftLower : 256≤(2*node)*2^height := by nlinarith
    have leftUpper : (2*node+1)*2^height≤512 := by nlinarith
    have rightLower : 256≤(2*node+1)*2^height := by nlinarith
    have rightUpper : (2*node+1+1)*2^height≤512 := by nlinarith
    obtain ⟨mark,leftMarks,rightMarks⟩ := marks
    by_cases present : marked node=true
    · have occupied : capOccupied (.node leftView rightView)=true := mark.symm.trans present
      have left := leftIH (2*node) leftLower leftUpper leftMarks
      have right := rightIH (2*node+1) rightLower rightUpper rightMarks
      have leftEnd := cap_subtree_run_end marked height (2*node) leftLower leftUpper
      have rightEnd := cap_subtree_run_end marked height (2*node+1) rightLower rightUpper
      have firstStep : capControlRun marked 1 (.visit node)=.visit (2*node) := by
        simp [capControlRun,capControlStep,present,internal]
      have oneLeft : capControlRun marked 1 (.advance (2*node))=.visit (2*node+1) := by
        have nonroot : 2*node≠1 := by omega
        simp [capControlRun,capControlStep,nonroot]
      rw [capSubtreeSteps,if_pos present,capCalls,if_pos occupied]
      have splitCount :
          1+capSubtreeSteps marked height (2*node)+1+
            capSubtreeSteps marked height (2*node+1)+1=
          1+(capSubtreeSteps marked height (2*node)+
            (1+(capSubtreeSteps marked height (2*node+1)+1))) := by omega
      rw [splitCount,cap_dfs_query_total_add marked 1,firstStep,
        cap_dfs_query_total_add marked (capSubtreeSteps marked height (2*node)),
        left,leftEnd,cap_dfs_query_total_add marked 1,oneLeft,
        cap_dfs_query_total_add marked (capSubtreeSteps marked height (2*node+1)),
        right,rightEnd]
      simp [capDfsQueryTotal,capDfsStepQueries,ne_of_gt positive,Nat.add_assoc]
    · have absent : marked node=false := Bool.eq_false_iff.mpr present
      have unoccupied : capOccupied (.node leftView rightView)=false := mark.symm.trans absent
      simp [capSubtreeSteps,absent,capDfsQueryTotal,capDfsStepQueries,capCalls,unoccupied]

theorem cap_dfs_done_queries (marked : Nat → Bool) (count : Nat) :
    capDfsQueryTotal true marked count .done=0 := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [capDfsQueryTotal,capDfsStepQueries,capControlStep,ih,Nat.zero_add]

theorem cap_root_query_count (marked : Nat → Bool) (view : CapView 8)
    (marks : CapViewMarks marked 1 view) :
    capDfsQueryTotal true marked 1022 (.visit 1)=capCalls view := by
  have ended := cap_subtree_run_end marked 8 1 (by decide) (by decide)
  have counted := cap_subtree_query_count marked view 1 (by decide) (by decide) marks
  have bounded := cap_subtree_steps_bound marked 8 1
  have count : capSubtreeSteps marked 8 1+1≤1022 := by norm_num at bounded; omega
  rw [show 1022=(capSubtreeSteps marked 8 1+1)+
    (1022-(capSubtreeSteps marked 8 1+1)) by omega,
    cap_dfs_query_total_add,cap_dfs_query_total_add,ended,counted]
  have oneDone : capControlRun marked 1 (.advance 1)=.done := by
    simp [capControlRun,capControlStep]
  rw [cap_control_run_add,ended,oneDone,cap_dfs_done_queries]
  simp [capDfsQueryTotal,capDfsStepQueries]

end CommitGolfCandidate
