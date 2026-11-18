import CommitGolfCandidate.NonceExpandHalves

/-! The footer loop (words 467..470): every 30-byte footer field becomes a 32-byte node, from the
last field down. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The footer of the expanded proof: node `j` at `nodes + 32 j` is field `j` at `fields + 30 j`
followed by two zero bytes. -/
structure NonceFooterTarget (start : MachineState) (target : Nat → Byte) (fields nodes footer : Nat) :
    Prop where
  copies : ∀ j < footer, ∀ o < 30,
    target (nodes + 32 * j + o) = start.getByte (BitVec.ofNat 64 (fields + 30 * j + o))
  zeros : ∀ j < footer, target (nodes + 32 * j + 30) = 0 ∧ target (nodes + 32 * j + 31) = 0

theorem nonce_footer_loop (start : MachineState) (target : Nat → Byte) (fields nodes footer high : Nat)
    (facts : NonceFooterTarget start target fields nodes footer)
    (order : fields ≤ nodes) (evenFields : fields % 2 = 0) (evenNodes : nodes % 2 = 0)
    (within : nodes + 32 * footer ≤ high) (range : high ≤ MEMORY_BYTES) :
    ∀ j ≤ footer, ∀ (state : MachineState) (regs : Reg → Word), NonceAt state 467 regs →
      regs .x29 = BitVec.ofNat 64 j → regs .x23 = BitVec.ofNat 64 (fields + 30 * j) →
      regs .x25 = BitVec.ofNat 64 (nodes + 32 * j) →
      NonceExpandMem start state (nodes + 32 * j) high target →
      ∃ next later, NonceExpandRuns state (38 * j + 1) next ∧ NonceAt next 471 later ∧
        later .x23 = BitVec.ofNat 64 fields ∧ later .x25 = BitVec.ofNat 64 nodes ∧
        (∀ reg, reg ∉ [Reg.x1, .x6, .x23, .x25, .x29] → later reg = regs reg) ∧
        NonceExpandMem start next nodes high target := by
  have memoryBound : MEMORY_BYTES < 2 ^ 64 := by decide
  intro j
  induction j with
  | zero =>
    intro _ state regs here counter source dest mem
    have zero := nonce_reg_zero here
    obtain ⟨run, at1⟩ := nonce_step_beq here .x29 .x0 16 471 (by omega) (by omega) rfl (by decide)
    rw [if_pos (by rw [counter, zero]; rfl)] at at1
    exact ⟨_, regs, run, at1, by simpa using source, by simpa using dest, fun _ _ => rfl,
      (by simpa using mem.same_mem (nonce_beq_mem _ _ _ _))⟩
  | succ j ih =>
    intro bounded state regs here counter source dest mem
    have zero := nonce_reg_zero here
    obtain ⟨run1, at1⟩ := nonce_step_beq here .x29 .x0 16 471 (by omega) (by omega) rfl (by decide)
    rw [if_neg (by rw [counter, zero, nonce_ofNat_eq_zero _ (by omega)]; omega)] at at1
    obtain ⟨run2, at2⟩ := nonce_step_jal at1 .x1 2097328 512 (by omega) (by omega) rfl (by decide)
    rw [if_neg (by decide)] at at2
    obtain ⟨r2, at2, v2, f2⟩ := at2.fresh
    have mem2 : NonceExpandMem start (execInstrBr (execInstrBr state (.BEQ .x29 .x0 16)) (.JAL .x1 2097328))
        (nodes + 32 * j + 32) high target := by
      have m := (mem.same_mem (nonce_beq_mem state .x29 .x0 16)).same_mem (nonce_jal_mem _ .x1 2097328)
      rwa [show nodes + 32 * (j + 1) = nodes + 32 * j + 32 by ring] at m
    obtain ⟨next3, r3, run3, at3, source3, dest3, frame3, mem3⟩ :=
      nonce_expand_node start _ r2 (fields + 30 * j) (nodes + 32 * j) high 469 target at2
        (by rw [f2 _ (by decide), source]; congr 1 <;> ring)
        (by rw [f2 _ (by decide), dest]; congr 1 <;> ring) v2 (by omega) (by decide) mem2
        (by omega) (by omega) (by omega) (by omega) range
        (fun o inside => facts.copies j (by omega) o inside) (facts.zeros j (by omega))
    obtain ⟨run4, at4⟩ := nonce_step_addi at3 .x29 .x29 4095 (by decide) (by omega) (by omega) rfl
    obtain ⟨r4, at4, v4, f4⟩ := at4.fresh
    obtain ⟨run5, at5⟩ := nonce_step_jal at4 .x0 2097140 467 (by omega) (by omega) rfl (by decide)
    rw [if_pos rfl] at at5
    have counter4 : r4 .x29 = BitVec.ofNat 64 j := by
      rw [v4, frame3 _ (by decide) (by decide) (by decide), f2 _ (by decide), counter,
        nonce_address_sub _ 1 _ (by decide) (by omega) (by omega) (by omega)]
      congr 1
    obtain ⟨next, later, run, final, sourceEnd, destEnd, frame, memEnd⟩ :=
      ih (by omega) _ r4 at5 counter4
        (by rw [f4 _ (by decide), source3])
        (by rw [f4 _ (by decide), dest3])
        ((mem3.same_mem (nonce_addi_mem _ .x29 .x29 4095)).same_mem (nonce_jal_mem _ .x0 2097140))
    refine ⟨next, later, (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans run))))).cast
      (by ring), final, sourceEnd, destEnd, ?_, memEnd⟩
    intro reg outside
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
    obtain ⟨n1, n6, n23, n25, n29⟩ := outside
    rw [frame reg (by simp [n1, n6, n23, n25, n29]), f4 _ n29, frame3 _ n6 n23 n25, f2 _ n1]

end CommitGolfCandidate
