import CommitGolfCandidate.CursorLeaf

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

theorem cursor_prefix_register (state : MachineState) (cursor count : Nat)
    (finished : MachineState) (reachable : finished ∈ support (cursorPrefix state cursor count))
    (reg : Reg) (preserved : reg ∉ [Reg.x10, .x12]) :
    finished.getReg reg = state.getReg reg := by
  induction count generalizing state cursor with
  | zero =>
    simp only [cursorPrefix, support_pure, Set.mem_singleton_iff] at reachable
    subst finished
    rfl
  | succ count ih =>
    simp only [cursorPrefix, mem_support_bind_iff] at reachable
    obtain ⟨answer, _, reached⟩ := reachable
    change BitVec 256 at answer
    exact (ih (cursorNextState state false answer) (cursor + 32) reached).trans
      (cursor_next_register state false answer reg preserved)

theorem cursor_prefix_pointer (state : MachineState) (cursor count : Nat)
    (pointer : state.getReg .x10 = BitVec.ofNat 64 cursor)
    (finished : MachineState) (reachable : finished ∈ support (cursorPrefix state cursor count)) :
    finished.getReg .x10 = BitVec.ofNat 64 (cursor + 32 * count) := by
  induction count generalizing state cursor with
  | zero =>
    simp only [cursorPrefix, support_pure, Set.mem_singleton_iff] at reachable
    subst finished
    simpa using pointer
  | succ count ih =>
    simp only [cursorPrefix, mem_support_bind_iff] at reachable
    obtain ⟨answer, _, reached⟩ := reachable
    change BitVec 256 at answer
    have next : (cursorNextState state false answer).getReg .x10 =
        BitVec.ofNat 64 (cursor + 32) := by
      rw [cursor_next_pointer, pointer]
      exact (BitVec.ofNat_add cursor 32).symm
    have done := ih (cursorNextState state false answer) (cursor + 32) next reached
    have index : cursor + 32 + 32 * count = cursor + 32 * (count + 1) := by omega
    simpa only [index] using done

theorem cursor_prefix_pc (state : MachineState) (cursor count : Nat)
    (finished : MachineState) (reachable : finished ∈ support (cursorPrefix state cursor count)) :
    finished.pc = state.pc + BitVec.ofNat 64 (12 * count) := by
  induction count generalizing state cursor with
  | zero =>
    simp only [cursorPrefix, support_pure, Set.mem_singleton_iff] at reachable
    subst finished
    simp
  | succ count ih =>
    simp only [cursorPrefix, mem_support_bind_iff] at reachable
    obtain ⟨answer, _, reached⟩ := reachable
    change BitVec 256 at answer
    rw [ih (cursorNextState state false answer) (cursor + 32) reached,
      cursor_next_pc, BitVec.add_assoc]
    change state.pc + (BitVec.ofNat 64 12 + BitVec.ofNat 64 (12 * count)) = _
    rw [← BitVec.ofNat_add]
    have index : 12 + 12 * count = 12 * (count + 1) := by omega
    rw [index]

theorem cursor_prefix_ready (state : MachineState) (cursor count : Nat)
    (ready : StreamingOracleReady state) (finished : MachineState)
    (reachable : finished ∈ support (cursorPrefix state cursor count)) :
    StreamingOracleReady finished := by
  rcases ready with ⟨r5, r11, r13⟩
  exact ⟨(cursor_prefix_register state cursor count finished reachable .x5 (by decide)).trans r5,
    (cursor_prefix_register state cursor count finished reachable .x11 (by decide)).trans r11,
    (cursor_prefix_register state cursor count finished reachable .x13 (by decide)).trans r13⟩

end CommitGolfCandidate
