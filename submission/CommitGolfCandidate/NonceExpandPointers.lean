import CommitGolfCandidate.NonceExpandRecord

/-! Pointer changes and stable registers of the concrete expansion record.
Only the padding-skip call decrements x25 outside the shared copy routine. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

theorem nonce_expand_call_target (nonce : Bool) (state : MachineState) :
    (nonceExpandCallPrefix nonce state (nonceExpandCallCount nonce)).getReg .x25=
      if nonce then state.getReg .x25+signExtend12 (4088 : BitVec 12) else state.getReg .x25 := by
  cases nonce <;>
    simp [nonceExpandCallPrefix,nonceExpandCallInstructions,nonceExpandCallCount,execInstrBr,
      MachineState.getReg,MachineState.setPC,MachineState.setReg,MachineState.setMem]

theorem nonce_expand_outer_counter (state : MachineState) :
    (nonceExpandNonceCopied state).getReg .x24=state.getReg .x24 := by
  rw [nonceExpandNonceCopied,nonce_backward_returned_register _ _ .x24 (by decide)]
  change (nonceExpandCallPrefix true (nonceExpandSiblingsCopied state)
    (nonceExpandCallCount true)).getReg .x24=_
  rw [nonce_expand_call_register true _ .x24 (by decide)]
  rw [nonceExpandSiblingsCopied,nonce_backward_returned_register _ _ .x24 (by decide)]
  change (nonceExpandCallPrefix false state (nonceExpandCallCount false)).getReg .x24=_
  exact nonce_expand_call_register false state .x24 (by decide)

theorem nonce_expand_record_register (state : MachineState) (reg : Reg)
    (outside : reg ≠ .x1 ∧ reg ≠ .x6 ∧ reg ≠ .x23 ∧ reg ≠ .x24 ∧ reg ≠ .x25 ∧ reg ≠ .x28) :
    (nonceExpandRecordState state).getReg reg=state.getReg reg := by
  rw [nonceExpandRecordState,nonce_expand_tail_register _ reg outside.2.2.2.1]
  rw [nonceExpandNonceCopied,
    nonce_backward_returned_register _ _ reg ⟨outside.2.1,outside.2.2.1,outside.2.2.2.2.1,outside.2.2.2.2.2⟩]
  change (nonceExpandCallPrefix true (nonceExpandSiblingsCopied state)
    (nonceExpandCallCount true)).getReg reg=_
  rw [nonce_expand_call_register true _ reg ⟨outside.1,outside.2.2.2.2.1,outside.2.2.2.2.2⟩]
  rw [nonceExpandSiblingsCopied,
    nonce_backward_returned_register _ _ reg ⟨outside.2.1,outside.2.2.1,outside.2.2.2.2.1,outside.2.2.2.2.2⟩]
  change (nonceExpandCallPrefix false state (nonceExpandCallCount false)).getReg reg=_
  exact nonce_expand_call_register false state reg ⟨outside.1,outside.2.2.2.2.1,outside.2.2.2.2.2⟩

end CommitGolfCandidate
