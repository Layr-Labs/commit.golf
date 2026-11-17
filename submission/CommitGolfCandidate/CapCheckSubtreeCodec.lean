import CommitGolfCandidate.CapCheckCodecInternal

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false

theorem cap_check_subtree_codec (oracle : Oracle) (limit : Nat)
    (marked : Nat → Bool) {height : Nat} (view : CapView height) (node : Nat)
    (lower : 256≤node*2^height) (upper : (node+1)*2^height≤512)
    (marks : CapViewMarks marked node view) :
    CapCheckCodecCorrect oracle limit marked view node := by
  induction view generalizing node with
  | leaf known =>
    intro state cursor words tailBytes ready suffix payload
    have nodeLower : 256≤node := by simpa only [pow_zero,Nat.mul_one] using lower
    exact cap_check_codec_result_leaf oracle limit marked known node state
      cursor words tailBytes ready suffix nodeLower marks payload
  | @node depth left right ihLeft ihRight =>
    by_cases occupied : capOccupied (.node left right)=true
    · have power := Nat.two_pow_pos depth
      have lower' := lower
      have upper' := upper
      rw [pow_succ] at lower' upper'
      have positive : 0<node := by nlinarith
      have internal : node<256 := by nlinarith
      have leftLower : 256≤(2*node)*2^depth := by nlinarith
      have leftUpper : (2*node+1)*2^depth≤512 := by nlinarith
      have rightLower : 256≤(2*node+1)*2^depth := by nlinarith
      have rightUpper : (2*node+2)*2^depth≤512 := by nlinarith
      exact cap_check_codec_internal oracle limit marked left right node
        positive internal leftLower leftUpper rightLower rightUpper marks occupied
        (ihLeft (2*node) leftLower leftUpper marks.2.1)
        (ihRight (2*node+1) rightLower rightUpper marks.2.2)
    · intro state cursor words tailBytes ready suffix _
      exact cap_check_codec_result_unknown oracle limit marked (.node left right)
        node state cursor words tailBytes ready suffix marks (Bool.eq_false_iff.mpr occupied)

end CommitGolfCandidate
