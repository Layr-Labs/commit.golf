import CommitGolfCandidate.NonceExpandFlow

/-! Observed register state at the retained checker: proof length is expanded,
root is saved, scratch is cleared, and the other ABI registers are preserved. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
attribute [local irreducible] nonceExpandHeaderPrefix nonceExpandMinimumPrefix
  nonceExpandCapacityPrefix nonceExpandFooterPrefix nonceBackwardReturned

theorem nonce_expand_entry_register (state : MachineState) (words : Nat) (reg : Reg)
    (outside : reg ≠ .x1 ∧ reg ≠ .x6 ∧ reg ≠ .x23 ∧ reg ≠ .x25 ∧ reg ≠ .x28) :
    (nonceExpandRecordEntry state words).getReg reg=state.getReg reg := by
  unfold nonceExpandRecordEntry
  rw [nonce_expand_guard_register]
  unfold nonceExpandAfterFooter
  split
  · rfl
  · rw [nonce_backward_returned_register _ _ reg outside.2,
      nonce_expand_footer_call_register _ reg outside.1]

theorem nonce_expand_records_register (state : MachineState) (count length : Nat) (reg : Reg)
    (outside : reg ≠ .x1 ∧ reg ≠ .x6 ∧ reg ≠ .x23 ∧ reg ≠ .x24 ∧ reg ≠ .x25 ∧ reg ≠ .x28) :
    (nonceExpandRecordsEnd state count length).getReg reg=(nonceExpandSetupState state).getReg reg := by
  rw [nonceExpandRecordsEnd,nonce_expand_outer_register _ count reg outside,
    nonce_expand_entry_register _ _ reg ⟨outside.1,outside.2.1,outside.2.2.1,outside.2.2.2.2⟩]

theorem nonce_expand_core_reset (state : MachineState) (count length : Nat) (reg : Reg)
    (reset : reg ∈ nonceExpandResetRegisters) :
    (nonceExpandCoreState state count length).getReg reg=0 := nonce_expand_finish_zero _ reg reset

theorem nonce_expand_core_register (state : MachineState) (count length : Nat) (reg : Reg)
    (outside : reg ≠ .x17 ∧ reg ≠ .x26 ∧ reg ∉ nonceExpandResetRegisters) :
    (nonceExpandCoreState state count length).getReg reg=state.getReg reg := by
  have distinct : ∀ rd, rd ∈ nonceExpandResetRegisters → reg ≠ rd := by
    intro rd member equal; subst reg; exact outside.2.2 member
  rw [nonceExpandCoreState,nonce_expand_finish_register _ reg ⟨outside.1,outside.2.2⟩,
    nonce_expand_records_register _ count length reg
      ⟨distinct _ (by decide),distinct _ (by decide),distinct _ (by decide),distinct _ (by decide),distinct _ (by decide),distinct _ (by decide)⟩]
  apply nonce_expand_setup_register
  cases reg <;> simp_all [nonceExpandSetupClobbers,nonceExpandResetRegisters]

theorem nonce_expand_core_metadata (state : MachineState) (base count length : Nat)
    (facts : NonceExpandSetupFacts base count length state) :
    (nonceExpandCoreState state count length).getReg .x17=BitVec.ofNat 64 (length+8*count) ∧
    (nonceExpandCoreState state count length).getReg .x26=state.getReg .x11 := by
  constructor
  · rw [nonceExpandCoreState,nonce_expand_finish_length,
      nonce_expand_records_register _ count length .x18 (by decide)]
    exact facts.expanded
  · rw [nonceExpandCoreState,nonce_expand_finish_register _ .x26 (by decide),
      nonce_expand_records_register _ count length .x26 (by decide)]
    exact facts.root
end CommitGolfCandidate
