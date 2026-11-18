import CommitGolfCandidate.NonceExpandRecord

/-! The record loop (words 471..491), from the last record down, and the finish (words 492..504):
x17 becomes the expanded length, the scratch registers are cleared and the retained initializer
resumes at word 1. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The expanded records of a proof at `base`: record `r` at `base + 576 r` of the delivered
record at `base + 560 r`, whose position word is at `indices + 8 r`. -/
def NonceRecordsTarget (start : MachineState) (target : Nat → Byte) (base indices count : Nat) : Prop :=
  ∀ r < count, ∃ position, position < 2 ^ 24 ∧
    start.getMem (BitVec.ofNat 64 (indices + 8 * r)) = BitVec.ofNat 64 position ∧
    NonceRecordTarget start target (base + 560 * r) (base + 576 * r) position

theorem nonce_records_loop (start : MachineState) (target : Nat → Byte) (base indices count high : Nat)
    (facts : NonceRecordsTarget start target base indices count)
    (indicesAligned : indices % 8 = 0) (indicesBelow : indices + 8 * count ≤ base)
    (countBound : count ≤ 2 ^ 24) (alignedBase : base % 8 = 0)
    (within : base + 576 * count ≤ high) (range : high ≤ MEMORY_BYTES) :
    ∀ r, r < count → ∀ (state : MachineState) (regs : Reg → Word), NonceAt state 472 regs →
      regs .x24 = BitVec.ofNat 64 (r + 1) → regs .x13 = BitVec.ofNat 64 indices →
      regs .x23 = BitVec.ofNat 64 (base + 560 * (r + 1)) →
      regs .x25 = BitVec.ofNat 64 (base + 576 * (r + 1)) →
      NonceExpandMem start state (base + 576 * (r + 1)) high target →
      ∃ next later, NonceExpandRuns state (945 * (r + 1)) next ∧ NonceAt next 492 later ∧
        later .x23 = BitVec.ofNat 64 base ∧ later .x25 = BitVec.ofNat 64 base ∧
        (∀ reg, reg ∉ [Reg.x1, .x6, .x23, .x24, .x25, .x28, .x29] → later reg = regs reg) ∧
        NonceExpandMem start next base high target := by
  have record : ∀ r < count, ∀ (state : MachineState) (regs : Reg → Word), NonceAt state 472 regs →
      regs .x24 = BitVec.ofNat 64 (r + 1) → regs .x13 = BitVec.ofNat 64 indices →
      regs .x23 = BitVec.ofNat 64 (base + 560 * (r + 1)) →
      regs .x25 = BitVec.ofNat 64 (base + 576 * (r + 1)) →
      NonceExpandMem start state (base + 576 * (r + 1)) high target →
      ∃ next later, NonceExpandRuns state 945 next ∧ NonceAt next (if r = 0 then 492 else 472) later ∧
        later .x24 = BitVec.ofNat 64 r ∧ later .x23 = BitVec.ofNat 64 (base + 560 * r) ∧
        later .x25 = BitVec.ofNat 64 (base + 576 * r) ∧
        (∀ reg, reg ∉ [Reg.x1, .x6, .x23, .x24, .x25, .x28, .x29] → later reg = regs reg) ∧
        NonceExpandMem start next (base + 576 * r) high target := by
    intro r bounded state regs here counter indexBase source dest mem
    obtain ⟨position, positionBound, positionWord, target⟩ := facts r bounded
    exact nonce_expand_record start _ (base + 560 * r) (base + 576 * r) indices r position high target
      positionWord positionBound indicesAligned (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) range state regs here counter indexBase
      (by rw [source]; all_goals (congr 1 <;> ring)) (by rw [dest]; all_goals (congr 1 <;> ring))
      (by rw [show base + 576 * r + 576 = base + 576 * (r + 1) by ring]; exact mem)
  intro r
  induction r with
  | zero =>
    intro bounded state regs here counter indexBase source dest mem
    obtain ⟨next, later, run, final, _, source', dest', frame, mem'⟩ :=
      record 0 bounded state regs here counter indexBase source dest mem
    exact ⟨next, later, run.cast rfl, by simpa using final, by simpa using source', by simpa using dest',
      frame, by simpa using mem'⟩
  | succ r ih =>
    intro bounded state regs here counter indexBase source dest mem
    obtain ⟨next, later, run, final, counter', source', dest', frame, mem'⟩ :=
      record (r + 1) bounded state regs here counter indexBase source dest mem
    rw [if_neg (by omega)] at final
    obtain ⟨last, regsLast, run', final', sourceLast, destLast, frame', memLast⟩ :=
      ih (by omega) next later final counter' (by rw [frame .x13 (by simp), indexBase]) source' dest' mem'
    refine ⟨last, regsLast, (run.trans run').cast (by ring), final', sourceLast, destLast, ?_, memLast⟩
    intro reg outside
    rw [frame' reg outside, frame reg outside]

/-- The finish (words 492..504): x17 = x18, the scratch registers cleared, then word 1. -/
theorem nonce_expand_done (state : MachineState) (regs : Reg → Word) (here : NonceAt state 492 regs) :
    ∃ next later, NonceExpandRuns state 13 next ∧ NonceAt next 1 later ∧ later .x17 = regs .x18 ∧
      (∀ reg ∈ [Reg.x1, .x6, .x7, .x18, .x19, .x23, .x24, .x25, .x28, .x29, .x30], later reg = 0) ∧
      (∀ reg, reg ∉ [Reg.x1, .x6, .x7, .x17, .x18, .x19, .x23, .x24, .x25, .x28, .x29, .x30] →
        later reg = regs reg) ∧
      next.mem = state.mem := by
  have zero := nonce_reg_zero here
  obtain ⟨run0, at0⟩ := nonce_step_addi here .x17 .x18 0 (by decide) (by omega) (by omega) rfl
  obtain ⟨run1, at1⟩ := nonce_step_addi at0 .x1 .x0 0 (by decide) (by omega) (by omega) rfl
  obtain ⟨run2, at2⟩ := nonce_step_addi at1 .x6 .x0 0 (by decide) (by omega) (by omega) rfl
  obtain ⟨run3, at3⟩ := nonce_step_addi at2 .x7 .x0 0 (by decide) (by omega) (by omega) rfl
  obtain ⟨run4, at4⟩ := nonce_step_addi at3 .x18 .x0 0 (by decide) (by omega) (by omega) rfl
  obtain ⟨run5, at5⟩ := nonce_step_addi at4 .x19 .x0 0 (by decide) (by omega) (by omega) rfl
  obtain ⟨run6, at6⟩ := nonce_step_addi at5 .x23 .x0 0 (by decide) (by omega) (by omega) rfl
  obtain ⟨run7, at7⟩ := nonce_step_addi at6 .x24 .x0 0 (by decide) (by omega) (by omega) rfl
  obtain ⟨run8, at8⟩ := nonce_step_addi at7 .x25 .x0 0 (by decide) (by omega) (by omega) rfl
  obtain ⟨run9, at9⟩ := nonce_step_addi at8 .x28 .x0 0 (by decide) (by omega) (by omega) rfl
  obtain ⟨run10, at10⟩ := nonce_step_addi at9 .x29 .x0 0 (by decide) (by omega) (by omega) rfl
  obtain ⟨run11, at11⟩ := nonce_step_addi at10 .x30 .x0 0 (by decide) (by omega) (by omega) rfl
  obtain ⟨run12, at12⟩ := nonce_step_jal at11 .x0 2095140 1 (by omega) (by omega) rfl (by decide)
  rw [if_pos rfl] at at12
  refine ⟨_, _, (run0.trans (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans (run8.trans (run9.trans (run10.trans (run11.trans run12)))))))))))).cast rfl, at12, ?_, ?_, ?_, ?_⟩
  · simp [Function.update_apply, nonce_add_zero, nonce_sign_zero, nonce_sign_zero']
  · intro reg member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp [Function.update_apply, nonce_add_zero, nonce_sign_zero, nonce_sign_zero', zero]
  · intro reg outside
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
    obtain ⟨n1, n6, n7, n17, n18, n19, n23, n24, n25, n28, n29, n30⟩ := outside
    simp [Function.update_apply, n1, n6, n7, n17, n18, n19, n23, n24, n25, n28, n29, n30]
  · exact (nonce_jal_mem _ _ _).trans <| (nonce_addi_mem _ _ _ _).trans <| (nonce_addi_mem _ _ _ _).trans <| (nonce_addi_mem _ _ _ _).trans <| (nonce_addi_mem _ _ _ _).trans <| (nonce_addi_mem _ _ _ _).trans <| (nonce_addi_mem _ _ _ _).trans <| (nonce_addi_mem _ _ _ _).trans <| (nonce_addi_mem _ _ _ _).trans <| (nonce_addi_mem _ _ _ _).trans <| (nonce_addi_mem _ _ _ _).trans <| (nonce_addi_mem _ _ _ _).trans <| (nonce_addi_mem _ _ _ _)

end CommitGolfCandidate
