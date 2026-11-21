import CommitGolfCandidate.ChainedSchedule
import CommitGolfCandidate.TwoPermutationOpeningCapStructure

/-! The variable-width cap frontier has at most 30,208 bits, including height sixteen. -/
namespace CommitGolfCandidate.Chained.InteriorCodec
open CommitGolf TwoPermutationPrototype TwoPermutationPrototype.Sampling TwoPermutationPrototype.Opening

def footerWidth (node : Nat) : Nat := if 256 ≤ node then 234 else 238
def footerBits (nodes : List Nat) : Nat := (nodes.map footerWidth).sum

def capBits : {height : Nat} → CapMarks height → Nat
  | 0,.leaf marked => if marked then 0 else 234
  | _+1,.node left right =>
    if left.occupied || right.occupied then capBits left+capBits right else 238

theorem cap_bits_two (tree : CapMarks 2) : capBits tree ≤ 472 := by
  cases tree with
  | node left right =>
    cases left with
    | node a b =>
      cases right with
      | node c d =>
        cases a with
        | leaf a =>
          cases b with
          | leaf b =>
            cases c with
            | leaf c =>
              cases d with
              | leaf d => cases a <;> cases b <;> cases c <;> cases d <;> decide

theorem cap_bits_bound (height : Nat) (tree : CapMarks (height+2)) :
    capBits tree ≤ 472*2^height := by
  induction height with
  | zero => exact cap_bits_two tree
  | succ height ih =>
    cases tree with
    | node left right =>
      have lower := ih left
      have upper := ih right
      have positive : 0 < 2^height := by positivity
      rw [capBits,Nat.pow_succ]
      split <;> omega

theorem footer_bits_frontier (groups : List Nat) (node height : Nat) (span : CapSpan node height) :
    footerBits (capFrontierNodes groups node height) = capBits (capMarkTree groups node height) := by
  induction height generalizing node with
  | zero =>
    have leaf := cap_span_is_leaf node span
    cases mark : capIsMarked groups node 0 <;>
      simp [footerBits,capFrontierNodes,capMarkTree,capBits,mark,footerWidth,leaf]
  | succ height ih =>
    have internal := cap_span_is_internal node height span
    have children := cap_span_children node height span
    change footerBits (capFrontierNodes groups node (height+1)) =
      if (capMarkTree groups (2*node) height).occupied || (capMarkTree groups (2*node+1) height).occupied
      then capBits (capMarkTree groups (2*node) height)+capBits (capMarkTree groups (2*node+1) height) else 238
    rw [cap_tree_occupied,cap_tree_occupied,←cap_marked_children,capFrontierNodes]
    cases mark : capIsMarked groups node (height+1)
    · simp [mark,footerBits,footerWidth,Nat.not_le_of_gt internal]
    · simp only [mark,ite_true,footerBits,List.map_append,List.sum_append]
      exact congrArg₂ Nat.add (ih _ children.1) (ih _ children.2)

theorem footer_bits_bound (groups : List Nat) : footerBits (capFrontierNodes groups 1 8) ≤ 30208 := by
  rw [footer_bits_frontier groups 1 8 cap_span_root]
  exact cap_bits_bound 6 _

def footerNodes (positions : Positions) : List Nat :=
  if positions.card = 0 then []
  else capFrontierNodes ((positions.sort (· ≤ ·)).map capGroup) 1 8

def proofLength (positions : Positions) : Nat :=
  482*positions.card+(footerBits (footerNodes positions)+7)/8

theorem proof_length_bound (positions : Positions) (scored : positions.card ≤ 128) :
    proofLength positions ≤ 65472 := by
  have limit : footerBits (footerNodes positions) ≤ 30208 := by
    unfold footerNodes
    split
    · simp [footerBits]
    · exact footer_bits_bound _
  unfold proofLength
  omega

theorem proof_length_empty (positions : Positions) (empty : positions.card = 0) : proofLength positions = 0 := by
  simp [proofLength,footerNodes,empty,footerBits]

theorem record_bits : 121+238+(∑ h : Fin 15, width ⟨h.val,by omega⟩) = 3856 := by decide +kernel

end CommitGolfCandidate.Chained.InteriorCodec
