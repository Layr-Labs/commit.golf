import CommitGolfCandidate.TwoPermutationPostorderProgram

namespace TwoPermutationPrototype.Opening.Postorder
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64

set_option maxRecDepth 4096
set_option maxHeartbeats 600000
attribute [local simp] getReg_setReg getReg_setMem

private def nodes (n : Nat) : Nat → List Nat
  | 0 => [n]
  | h+1 => n :: (nodes (2*n) h ++ nodes (2*n+1) h)

private theorem all_nodes : ∀ n : Fin 511, n.val+1 ∈ nodes 1 8 := by decide

@[local simp] private theorem reg_mem (s : MachineState) (r : Reg) (v : Word) :
    (s.setReg r v).mem = s.mem := by cases r <;> rfl

private theorem finish_word (s : MachineState) (n d : Nat) (address : Word) :
    (finish s n d).getMem address = if address = addr n then
      s.getReg (reg d) ||| s.getReg (reg (d+1)) else s.getMem address := by
  simp [finish, MachineState.getMem, MachineState.setMem, MachineState.setPC]

private theorem address_ne {j n : Nat} (left : j < 512) (right : n < 512) (diff : j ≠ n) :
    addr j ≠ addr n := by
  intro eq
  unfold addr markBase at eq
  have := nat_address_injective (by omega) (by omega) eq
  omega

private structure Correct (before after : MachineState) (expected : Nat → Word) (n h d : Nat) : Prop where
  register : after.getReg (reg d) = expected n
  memory : ∀ k, k < 512 →
    (before.getMem (addr k) = expected k ∨ k ∈ nodes n h) → after.getMem (addr k) = expected k

/-- A register holds each subtree result. Stores preserve all entries that already
agree with the expected tree, including every leaf and all completed subtrees. -/
private theorem meaning (s : MachineState) (expected : Nat → Word) (n h d : Nat)
    (span : CapSpan n h) (room : d+h < 9)
    (leaves : ∀ k, 256 ≤ k → k < 512 → s.getMem (addr k) = expected k)
    (parent : ∀ k, 0 < k → k < 256 → expected k = expected (2*k) ||| expected (2*k+1)) :
    Correct s (eval s n h d) expected n h d := by
  induction h generalizing s n d with
  | zero =>
    have leaf := leaves n (cap_span_is_leaf n span) (cap_span_node n 0 span).2
    constructor
    · simp [eval, reg_ne_zero ⟨d,by omega⟩, leaf]
    · intro k upper cond
      simp only [eval, MachineState.getMem, MachineState.setPC, reg_mem]
      rcases cond with known | member
      · exact known
      · have eq : k = n := by simpa [nodes] using member
        subst k; exact leaf
  | succ h ih =>
    let l := eval s (2*n) h d
    let r := eval l (2*n+1) h (d+1)
    obtain ⟨ls,rs⟩ := cap_span_children n h span
    have lc : Correct s l expected (2*n) h d := ih s (2*n) d ls (by omega) leaves
    have rc : Correct l r expected (2*n+1) h (d+1) :=
      ih l _ _ rs (by omega) (fun k lo hi => lc.memory k hi (.inl (leaves k lo hi)))
    have keep : r.getReg (reg d) = l.getReg (reg d) :=
      eval_register l _ _ _ _ (by
        intro j lower upper
        exact reg_distinct ⟨j,by omega⟩ ⟨d,by omega⟩ (by change j ≠ d; omega))
    have word : r.getReg (reg d) ||| r.getReg (reg (d+1)) = expected n := by
      rw [keep, lc.register, rc.register, ← parent n (cap_span_node n _ span).1
        (cap_span_is_internal n h span)]
    constructor
    · change (finish r n d).getReg (reg d) = expected n
      simpa [finish, reg_ne_zero ⟨d,by omega⟩] using word
    · intro k upper cond
      change (finish r n d).getMem (addr k) = expected k
      rw [finish_word]
      by_cases eq : k = n
      · subst k; simpa using word
      · rw [ite_eq_right (address_ne upper (cap_span_node n _ span).2 eq)]
        apply rc.memory k upper
        rcases cond with known | member
        · exact .inl (lc.memory k upper (.inl known))
        · simp only [nodes, List.mem_cons, List.mem_append] at member
          rcases member with same | fromLeft | fromRight
          · contradiction
          · exact .inl (lc.memory k upper (.inr fromLeft))
          · exact .inr fromRight

/-- The complete traversal accepts any leaf words and any expected tree whose
parents contain their two children's bitwise OR. -/
theorem root_marks (s : MachineState) (expected : Nat → Word)
    (leaves : ∀ k, 256 ≤ k → k < 512 → s.getMem (addr k) = expected k)
    (parent : ∀ k, 0 < k → k < 256 → expected k = expected (2*k) ||| expected (2*k+1))
    (k : Nat) (positive : 0 < k) (upper : k < 512) :
    (eval s 1 8 0).getMem (addr k) = expected k := by
  apply (meaning s expected 1 8 0 cap_span_root (by decide) leaves parent).memory k upper
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  exact .inr (all_nodes ⟨j,by omega⟩)

theorem frame (s : MachineState) (n h d address : Nat) (span : CapSpan n h)
    (above : trapdoorBase ≤ address) (fit : address < 2^64) :
    (eval s n h d).getMem (BitVec.ofNat 64 address) = s.getMem (BitVec.ofNat 64 address) := by
  induction h generalizing s n d with
  | zero => simp [eval, MachineState.getMem, MachineState.setPC]
  | succ h ih =>
    obtain ⟨ls,rs⟩ := cap_span_children n h span
    let l := eval s (2*n) h d
    let r := eval l (2*n+1) h (d+1)
    have nb := (cap_span_node n _ span).2
    have diff : BitVec.ofNat 64 address ≠ addr n := by
      intro eq
      have before := marks_before_trapdoor
      have size : markBase+8*n < 2^64 := by unfold markBase; omega
      have := nat_address_injective fit size eq
      omega
    change (finish r n d).getMem _ = _
    rw [finish_word, ite_eq_right diff]
    exact (ih l _ (d+1) rs).trans (ih s _ d ls)

end TwoPermutationPrototype.Opening.Postorder
