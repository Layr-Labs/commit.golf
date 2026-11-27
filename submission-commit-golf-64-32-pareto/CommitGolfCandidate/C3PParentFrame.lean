import CommitGolfCandidate.TwoPermutationHybridMeaning
import CommitGolfCandidate.C3CommitMemory

/-! # The paired parent phase leaves the reply area alone

Every parent step stores one node digest at `treeWord n` (the masked ones also store a halfword inside
that slot), for `n < 2^24`. So every word at or above `treeWord (2^24)` (the reply area starts there)
is unchanged by the whole parent phase, on every reachable path. -/
namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64.C3Leaves (compression_write_memory memoryView_congr addi_mem)
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option autoImplicit false

theorem parent_regs_set_pc {s : MachineState} {n : Nat} (regs : ParentRegs s n) (pc : Word) :
    ParentRegs (s.setPC pc) n := ⟨regs.source, regs.target, regs.selector, regs.size, regs.primitive, regs.heap⟩

theorem tree_word_mono {a b : Nat} (h : a ≤ b) : treeWord a ≤ treeWord b := by unfold treeWord; omega

theorem written_frame (s : MachineState) (n : Nat) (reply : BitVec 256) (hn : n < 2 ^ 24) :
    ∀ w < 2 ^ 33, treeWord (n + 1) ≤ w → memoryView (parentWritten s n reply) w = memoryView s w := by
  intro w wb above
  rw [parentWritten, compression_write_memory _ _ _ _ (by unfold treeWord; omega) wb]
  simp only [writeWindow]
  rw [dif_neg (by unfold treeWord at above ⊢; omega)]

theorem parents_p_frame (remaining : Nat) : ∀ count (s : MachineState), remaining + count < 2 ^ 24 →
    ∀ out ∈ support (parentsTraceP remaining count s), ∀ w < 2 ^ 33, treeWord (remaining + count + 1) ≤ w →
      memoryView out w = memoryView s w := by
  intro count
  induction count with
  | zero =>
    intro s _ out hit w _ _
    simp only [parentsTraceP, support_pure, Set.mem_singleton_iff] at hit
    subst hit; rfl
  | succ k ih =>
    intro s bound out hit w wb above
    simp only [parentsTraceP, mem_support_bind_iff] at hit
    obtain ⟨answer, _, rest⟩ := hit
    rw [ih _ (by omega) out rest w wb (le_trans (tree_word_mono (by omega)) above)]
    have m : (parentAfterP s (remaining + (k + 1)) answer).mem = (parentWritten s (remaining + (k + 1)) answer).mem := by
      simp only [parentAfterP, addi_mem]
    rw [memoryView_congr m, written_frame s (remaining + (k + 1)) answer (by omega) w wb (le_trans (tree_word_mono (by omega)) above)]

theorem lower_frame (span : Nat) : ∀ n (s : MachineState), hybridCut + span * n < 2 ^ 24 →
    ∀ out ∈ support (hybridLowerForP span n s), ∀ w < 2 ^ 33, treeWord (hybridCut + span * n + 1) ≤ w →
      memoryView out w = memoryView s w := by
  intro n
  induction n with
  | zero =>
    intro s _ out hit w _ _
    simp only [hybridLowerForP, support_pure, Set.mem_singleton_iff] at hit
    subst hit; rfl
  | succ n ih =>
    intro s bound out hit w wb above
    simp only [hybridLowerForP, mem_support_bind_iff] at hit
    obtain ⟨mid, path, rest⟩ := hit
    have b1 : hybridCut + span * n + span < 2 ^ 24 := by rw [Nat.mul_succ] at bound; omega
    rw [ih _ (by omega) out rest w wb (le_trans (tree_word_mono (by simp only [Nat.mul_succ]; omega)) above)]
    rw [show memoryView (mid.setPC (lowerNext (span * n))) = memoryView mid from memoryView_congr rfl]
    exact parents_p_frame _ span s b1 mid path w wb (le_trans (tree_word_mono (by simp only [Nat.mul_succ]; omega)) above)

theorem packed_trace_mem_frame (remaining : Nat) : ∀ count (s : MachineState), ParentRegs s (remaining + count) →
    remaining + count < 2 ^ 24 → ∀ out ∈ support (packedParentsTrace remaining count s),
      ParentRegs out remaining ∧
        ∀ w < 2 ^ 33, treeWord (remaining + count + 1) ≤ w → memoryView out w = memoryView s w := by
  intro count
  induction count with
  | zero =>
    intro s regs _ out hit
    simp only [packedParentsTrace, support_pure, Set.mem_singleton_iff] at hit
    subst hit; exact ⟨regs, fun _ _ _ => rfl⟩
  | succ k ih =>
    intro s regs bound out hit
    simp only [packedParentsTrace, mem_support_bind_iff] at hit
    obtain ⟨answer, _, rest⟩ := hit
    have regs' := packed_next_parent_regs s (remaining + k) answer regs
    obtain ⟨endRegs, frame⟩ := ih _ regs' (by omega) out rest
    refine ⟨endRegs, fun w wb above => ?_⟩
    rw [frame w wb (le_trans (tree_word_mono (by omega)) above),
      memoryView_congr (packed_parent_memory s (remaining + k + 1) answer regs (by omega)),
      written_frame s (remaining + k + 1) _ (by omega) w wb (le_trans (tree_word_mono (by omega)) above)]

theorem groups_mem_frame (base : Word) (span : Nat) : ∀ groups (s : MachineState), ParentRegs s (span * groups) →
    span * groups < 2 ^ 24 → ∀ out ∈ support (packedParentGroups base span groups s),
      ∀ w < 2 ^ 33, treeWord (span * groups + 1) ≤ w → memoryView out w = memoryView s w := by
  intro groups
  induction groups with
  | zero =>
    intro s _ _ out hit w _ _
    simp only [packedParentGroups, support_pure, Set.mem_singleton_iff] at hit
    subst hit; rfl
  | succ g ih =>
    intro s regs bound out hit w wb above
    simp only [packedParentGroups, mem_support_bind_iff] at hit
    obtain ⟨body, path, rest⟩ := hit
    have regs1 : ParentRegs s (span * g + span) := by rw [← Nat.mul_succ]; exact regs
    have b1 : span * g + span < 2 ^ 24 := by rw [Nat.mul_succ] at bound; exact bound
    obtain ⟨bodyRegs, frame⟩ := packed_trace_mem_frame (span * g) span s regs1 b1 body path
    rw [ih _ (parent_regs_set_pc bodyRegs _) (by omega) out rest w wb (le_trans (tree_word_mono (by simp only [Nat.mul_succ]; omega)) above),
      show memoryView (body.setPC (packedParentNextPC base span (span * g))) = memoryView body from memoryView_congr rfl,
      frame w wb (le_trans (tree_word_mono (by simp only [Nat.mul_succ]; omega)) above)]

theorem hybrid_start_mem (s : MachineState) : (hybridStart s).mem = s.mem := by
  unfold hybridStart
  show (execInstrBr (execInstrBr s (.LUI .x18 65536)) (.ADD .x18 .x18 .x8)).mem = s.mem
  rfl

/-- **The paired parent phase does not touch any word at or above `treeWord (2^24)`.** -/
theorem parent_phase_frame (X : MachineState) (regs : ParentRegsP X (2 ^ 24 - 1)) (pc : X.pc = 217572) :
    ∀ out ∈ support (hybridParentPhase X), ∀ w < 2 ^ 33, treeWord (2 ^ 24) ≤ w →
      memoryView out w = memoryView X w := by
  intro out hit w wb above
  simp only [hybridParentPhase, mem_support_bind_iff] at hit
  obtain ⟨lower, path, tail⟩ := hit
  have start : (hybridStart X).pc = 217580 := by change X.pc + 4 + 4 = _; rw [pc]; rfl
  have post := lower_postP 256 _ (fun _ => start) (hybrid_start_regsP X _ regs) path
  have cutRegs := regs_of_cut lower post.1
  have nr : ParentRegs (lower.setPC 615176) hybridCut :=
    ⟨cutRegs.source, cutRegs.target, cutRegs.selector, cutRegs.size, cutRegs.primitive, cutRegs.heap⟩
  simp only [hybridUpper, mem_support_bind_iff] at tail
  obtain ⟨mid, midPath, groupsPath⟩ := tail
  have nr' : ParentRegs (lower.setPC 615176) (8361285 + 27322) := nr
  obtain ⟨midRegs, midFrame⟩ := packed_trace_mem_frame 8361285 27322 _ nr' (by decide) mid midPath
  have gr : ParentRegs (mid.setPC 610808) (27595 * 303) := parent_regs_set_pc midRegs _
  rw [groups_mem_frame 610808 27595 303 _ gr (by decide) out groupsPath w wb
      (le_trans (tree_word_mono (by decide)) above),
    show memoryView (mid.setPC 610808) = memoryView mid from memoryView_congr rfl,
    midFrame w wb (le_trans (tree_word_mono (by decide)) above),
    show memoryView (lower.setPC 615176) = memoryView lower from memoryView_congr rfl,
    lower_frame fullSpan 256 _ (by decide) lower path w wb (le_trans (tree_word_mono (by decide)) above),
    memoryView_congr (hybrid_start_mem X)]

end TwoPermutationPrototype.RV64
