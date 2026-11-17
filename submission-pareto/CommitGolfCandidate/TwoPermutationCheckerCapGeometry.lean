import CommitGolfCandidate.TwoPermutationCheckerCapPaths
import CommitGolfCandidate.TwoPermutationCheckerCapFrame

namespace TwoPermutationPrototype.Checker
open CommitGolf CommitGolfCandidate CommitGolf.Riscv RiscvZkvm.Rv64
open TwoPermutationPrototype.RV64

def Under (node height other : Nat) : Prop :=
  ∃ depth ≤ height, node*2^depth ≤ other ∧ other < (node+1)*2^depth

theorem Under.self (node height : Nat) : Under node height node := by
  use 0
  simp

private theorem under_child {node height other kid : Nat} (placed : kid = 2*node ∨ kid = 2*node+1)
    (child : Under kid height other) : Under node (height+1) other := by
  obtain ⟨depth, smaller, low, high⟩ := child
  refine ⟨depth+1, by omega, ?_, ?_⟩
  · rw [show node*2^(depth+1) = 2*node*2^depth by rw [Nat.pow_succ]; ring]
    exact (Nat.mul_le_mul_right _ (by omega : 2*node ≤ kid)).trans low
  · rw [show (node+1)*2^(depth+1) = (2*(node+1))*2^depth by rw [Nat.pow_succ]; ring]
    exact high.trans_le (Nat.mul_le_mul_right _ (by omega))

theorem Under.left {node height other : Nat} (child : Under (2*node) height other) :
    Under node (height+1) other := under_child (Or.inl rfl) child

theorem Under.right {node height other : Nat} (child : Under (2*node+1) height other) :
    Under node (height+1) other := under_child (Or.inr rfl) child

theorem node_outside_children {node height : Nat} (position : 0 < node) :
    ¬ Under (2*node) height node ∧ ¬ Under (2*node+1) height node := by
  constructor <;> intro hit <;> obtain ⟨depth, _, low, _⟩ := hit
  · have child := Nat.mul_le_mul_left (2*node) (Nat.one_le_pow depth 2 (by decide))
    simp only [Nat.mul_one] at child
    omega
  · have child := Nat.mul_le_mul_left (2*node+1) (Nat.one_le_pow depth 2 (by decide))
    simp only [Nat.mul_one] at child
    omega

theorem left_root_outside_right {node height : Nat} : ¬ Under (2*node+1) height (2*node) := by
  rintro ⟨depth, _, low, _⟩
  have child := Nat.mul_le_mul_left (2*node+1) (Nat.one_le_pow depth 2 (by decide))
  simp only [Nat.mul_one] at child
  omega

end TwoPermutationPrototype.Checker
