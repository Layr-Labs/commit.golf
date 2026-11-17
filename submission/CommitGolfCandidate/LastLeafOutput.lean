import CommitGolfCandidate.CommitLoop

/-! A completed leaf leaves its actual digest destination in x12. The reference
heap cursor x23 has advanced by 32 bytes. This permits a group to advance its
heap cursor from the syscall output register, even when the entire group's
stride exceeds the positive signed RV64I ADDI range. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

theorem final_heap_reply_registers (state : MachineState) (cursor : Nat)
    (answer : BitVec 256) :
    (heapStreamingReplyState state cursor answer).getReg .x12 =
      (heapStreamingReplyState state cursor answer).getReg .x23 := by
  unfold heapStreamingReplyState
  rw [writeBits_register, writeBits_register]
  rfl

theorem nonempty_heap_blocks_destination (state : MachineState) (cursor count : Nat)
    (finished : MachineState)
    (reached : finished ∈ support (heapStreamingMachineBlocks state cursor (count + 1))) :
    finished.getReg .x12 = finished.getReg .x23 := by
  simp only [heapStreamingMachineBlocks, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at reached
  obtain ⟨body, _, answer, _, rfl⟩ := reached
  exact final_heap_reply_registers body _ answer

theorem leaf_output_cursor (state finished : MachineState)
    (reached : finished ∈ support (commitPositionRun state)) :
    finished.getReg .x12 + 32 = finished.getReg .x23 := by
  simp only [commitPositionRun, commitLeafLoop, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at reached
  obtain ⟨leaf, ⟨body, reachedBody, rfl⟩, rfl⟩ := reached
  change body.getReg .x12 + 32 = body.getReg .x23 + 32
  rw [nonempty_heap_blocks_destination _ _ 7 body reachedBody]

theorem group_output_cursor (state : MachineState) (remaining : Nat)
    (finished : MachineState) (reached : finished ∈ support (commitLeaves state (remaining + 1))) :
    finished.getReg .x12 + 32 = finished.getReg .x23 := by
  induction remaining generalizing state with
  | zero =>
    simp only [commitLeaves, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reached
    obtain ⟨_, stepped, rfl⟩ := reached
    exact leaf_output_cursor state _ stepped
  | succ remaining ih =>
    simp only [commitLeaves, mem_support_bind_iff] at reached
    obtain ⟨next, _, rest⟩ := reached
    exact ih next (by simpa only [commitLeaves, mem_support_bind_iff] using rest)
end CommitGolfCandidate
