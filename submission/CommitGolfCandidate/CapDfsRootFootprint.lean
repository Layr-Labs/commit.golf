import CommitGolfCandidate.CapDfsSubtree

namespace CommitGolfCandidate
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false

def capControlRootWritesHead (marked : Nat → Bool) : CapDfsControl → List Nat
  | .visit node => if marked node then [] else [node]
  | .advance node => if node=1 ∨ node%2=0 then [] else [node/2]
  | .done => []

def capControlRootWrites (marked : Nat → Bool) : Nat → CapDfsControl → List Nat
  | 0,_ => []
  | count+1,control =>
    capControlRootWritesHead marked control ++
      capControlRootWrites marked count (capControlStep marked control)

theorem cap_control_root_writes_add (marked : Nat → Bool) (first second : Nat)
    (control : CapDfsControl) :
    capControlRootWrites marked (first+second) control=
      capControlRootWrites marked first control ++
        capControlRootWrites marked second (capControlRun marked first control) := by
  induction first generalizing control with
  | zero => simp only [Nat.zero_add,capControlRootWrites,capControlRun,List.nil_append]
  | succ first ih =>
    simp only [Nat.succ_add,capControlRootWrites,capControlRun,ih,List.append_assoc]

theorem cap_subtree_root_writes_bound (marked : Nat → Bool) (height node : Nat)
    (lower : 256≤node*2^height) (upper : (node+1)*2^height≤512)
    (written : Nat)
    (member : written ∈ capControlRootWrites marked
      (capSubtreeSteps marked height node) (.visit node)) :
    node≤written := by
  induction height generalizing node with
  | zero =>
    simp only [capSubtreeSteps,capControlRootWrites,capControlRootWritesHead,
      List.append_nil] at member
    split at member
    · simp only [List.not_mem_nil] at member
    · simp only [List.mem_singleton] at member
      omega
  | succ height ih =>
    have power := Nat.two_pow_pos height
    have lower' := lower
    have upper' := upper
    rw [pow_succ] at lower' upper'
    have positive : 0<node := by nlinarith
    have internal : node<256 := by nlinarith
    have ll : 256≤(2*node)*2^height := by nlinarith
    have lu : (2*node+1)*2^height≤512 := by nlinarith
    have rl : 256≤(2*node+1)*2^height := by nlinarith
    have ru : (2*node+2)*2^height≤512 := by nlinarith
    by_cases present : marked node=true
    · have enter : capControlRun marked 1 (.visit node)=.visit (2*node) := by
        simp [capControlRun,capControlStep,present,internal]
      have sibling : capControlRun marked 1 (.advance (2*node))=.visit (2*node+1) := by
        have notRoot : 2*node≠1 := by omega
        simp [capControlRun,capControlStep,notRoot]
      have leftEnd := cap_subtree_run_end marked height (2*node) ll lu
      have rightEnd := cap_subtree_run_end marked height (2*node+1) rl ru
      have splitCount :
          1+capSubtreeSteps marked height (2*node)+1+
            capSubtreeSteps marked height (2*node+1)+1=
          1+(capSubtreeSteps marked height (2*node)+
            (1+(capSubtreeSteps marked height (2*node+1)+1))) := by omega
      rw [capSubtreeSteps,if_pos present,splitCount,
        cap_control_root_writes_add marked 1,enter,
        cap_control_root_writes_add marked (capSubtreeSteps marked height (2*node)),
        leftEnd,cap_control_root_writes_add marked 1,sibling,
        cap_control_root_writes_add marked (capSubtreeSteps marked height (2*node+1)),
        rightEnd] at member
      have leftNotRoot : 2*node≠1 := by omega
      have rightNotRoot : 2*node+1≠1 := by omega
      have firstWrites : capControlRootWritesHead marked (.visit node)=[] := by
        simp only [capControlRootWritesHead,if_pos present]
      have leftWrites : capControlRootWritesHead marked (.advance (2*node))=[] := by
        simp [capControlRootWritesHead,leftNotRoot]
      have rightWrites : capControlRootWritesHead marked (.advance (2*node+1))=[node] := by
        simp [capControlRootWritesHead,rightNotRoot,Nat.add_div,
          Nat.mul_div_left,Nat.ne_of_gt positive]
      simp only [capControlRootWrites,firstWrites,leftWrites,rightWrites,
        List.append_nil,List.nil_append,List.mem_append,
        List.mem_singleton] at member
      rcases member with left | right | atParent
      · have bound := ih (2*node) ll lu left
        omega
      · have bound := ih (2*node+1) rl ru right
        omega
      · omega
    · simp only [capSubtreeSteps,if_neg present,capControlRootWrites,
        capControlRootWritesHead,if_neg present,List.append_nil,
        List.mem_singleton] at member
      omega

end CommitGolfCandidate
