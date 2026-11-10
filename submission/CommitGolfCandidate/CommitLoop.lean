import CommitGolfCandidate.OuterHelpers

/-! Execution of every leaf iteration of the submitted commitment image. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

/-- The salt, digest, message, and index pointers advance independently. The reference loop
preserves the tree base, total leaf count, scratch pointer, fixed output limit,
and commitment pointer. -/
theorem commit_position_registers (state finished : MachineState)
    (reachable : finished ∈ support (commitPositionRun state)) :
    finished.getReg .x8 = state.getReg .x8 + 256 ∧
    finished.getReg .x18 = state.getReg .x18 + 32 ∧
    finished.getReg .x23 = state.getReg .x23 + 32 ∧
    finished.getReg .x20 = state.getReg .x20 + 1 ∧
    finished.pc = (if BitVec.ult (state.getReg .x20 + 1) (state.getReg .x19) then 4280 else 4364) ∧
    ∀ reg ∈ [Reg.x9, .x19, .x21, .x22, .x26], finished.getReg reg = state.getReg reg := by
  simp only [commitPositionRun, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reachable
  obtain ⟨leaf, reached, rfl⟩ := reachable
  let ready := commitLeafReadyState (commitPositionState state)
  have regs := commit_leaf_loop_registers ready 8 leaf reached
  have preserved (reg : Reg) (notCounter : reg ≠ .x28) (notLink : reg ≠ .x1)
      (notTemporary : reg ≠ .x6) (notOracle : reg ∉ [.x5,.x10,.x11,.x12,.x13]) :
      ready.getReg reg = state.getReg reg := by
    rw [commit_leaf_ready_register _ reg (by simp_all)]
    exact commit_position_register state reg notLink notTemporary
  have leafReg (reg : Reg) (member : reg ∈ [Reg.x9, .x18, .x19, .x20, .x21, .x22, .x23, .x26]) :
      leaf.getReg reg = state.getReg reg := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (regs.2 _ (by decide)).trans (preserved _ (by decide) (by decide) (by decide) (by decide))
  have value : leaf.getReg .x8 = state.getReg .x8 + 256 := by
    rw [regs.1, preserved .x8 (by decide) (by decide) (by decide) (by decide)]; rfl
  have copied (reg : Reg) (notTemporary : reg ≠ .x6) :
      (commitCopyState (leaf.setPC 4316) 55).getReg reg = leaf.getReg reg := by
    rw [commit_copy_register _ _ reg notTemporary, MachineState.getReg_setPC]
  have advance (current : MachineState) (reg : Reg) :
      (commitPositionNextState current).getReg reg =
        if reg = .x18 then current.getReg .x18 + 32 else
        if reg = .x23 then current.getReg .x23 + 32 else
        if reg = .x20 then current.getReg .x20 + 1 else current.getReg reg := by
    cases reg <;> rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [advance]
    change (commitCopyState (leaf.setPC 4316) 55).getReg .x8 = _
    exact (copied .x8 (by decide)).trans value
  · rw [advance]
    change (commitCopyState (leaf.setPC 4316) 55).getReg .x18 + 32 = _
    rw [copied .x18 (by decide), leafReg .x18 (by simp)]
  · rw [advance]
    change (commitCopyState (leaf.setPC 4316) 55).getReg .x23 + 32 = _
    rw [copied .x23 (by decide), leafReg .x23 (by simp)]
  · rw [advance]
    change (commitCopyState (leaf.setPC 4316) 55).getReg .x20 + 1 = _
    rw [copied .x20 (by decide), leafReg .x20 (by simp)]
  · change (if BitVec.ult ((commitCopyState (leaf.setPC 4316) 55).getReg .x20 + 1)
        ((commitCopyState (leaf.setPC 4316) 55).getReg .x19) then 4280 else 4364) = _
    rw [copied .x20 (by decide), copied .x19 (by decide),
      leafReg .x20 (by simp), leafReg .x19 (by simp)]
  · intro reg member
    have not6 : reg ≠ .x6 := by intro equal; subst reg; simp at member
    have not18 : reg ≠ .x18 := by intro equal; subst reg; simp at member
    have not23 : reg ≠ .x23 := by intro equal; subst reg; simp at member
    have not20 : reg ≠ .x20 := by intro equal; subst reg; simp at member
    rw [advance, if_neg not18, if_neg not23, if_neg not20, copied reg not6]
    apply leafReg reg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
    tauto

/-- A complete reference leaf restores the fixed arguments and zero block counter. -/
theorem commit_position_oracle_ready (state finished : MachineState)
    (scratch : state.getReg .x21=256)
    (reachable : finished ∈ support (commitPositionRun state)) :
    CommitLeafOracleReady finished ∧ finished.getReg .x28=0 := by
  simp only [commitPositionRun,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reachable
  obtain ⟨leaf,reached,rfl⟩ := reachable
  let input := commitLeafReadyState (commitPositionState state)
  have callScratch : (commitPositionState state).getReg .x21=256 :=
    (commit_position_register state .x21 (by decide) (by decide)).trans scratch
  have inputScratch : input.getReg .x21=256 :=
    (commit_leaf_ready_register _ .x21 (by decide)).trans callScratch
  have inputReady : CommitLeafOracleReady input := commit_leaf_ready_oracle _ callScratch
  have leafReady := commit_leaf_loop_ready input 8 inputScratch inputReady leaf reached
  have leafCounter := (commit_leaf_loop_finished input 8 (by decide)
    (commit_leaf_ready_counter _) leaf reached).1
  have preserved (reg : Reg) (not6 : Reg.x6 ≠ reg) (not18 : Reg.x18 ≠ reg)
      (not23 : Reg.x23 ≠ reg) (not20 : Reg.x20 ≠ reg) :
      (commitPositionNextState (commitCopyState (leaf.setPC 4316) 55)).getReg reg = leaf.getReg reg := by
    unfold commitPositionNextState
    rw [MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ not20,
      MachineState.getReg_setReg_ne _ _ _ _ not23,
      MachineState.getReg_setReg_ne _ _ _ _ not18,
      commit_copy_register _ _ reg (Ne.symm not6),MachineState.getReg_setPC]
  rcases leafReady with ⟨r5,r10,r11,r12,r13⟩
  exact ⟨⟨(preserved .x5 (by decide) (by decide) (by decide) (by decide)).trans r5,
    (preserved .x10 (by decide) (by decide) (by decide) (by decide)).trans r10,
    (preserved .x11 (by decide) (by decide) (by decide) (by decide)).trans r11,
    (preserved .x12 (by decide) (by decide) (by decide) (by decide)).trans r12,
    (preserved .x13 (by decide) (by decide) (by decide) (by decide)).trans r13⟩,
    (preserved .x28 (by decide) (by decide) (by decide) (by decide)).trans leafCounter⟩

/-- Safety and loop-control conditions, independent of the input bytes. -/
structure CommitLeavesInvariant (state : MachineState) (remaining : Nat) : Prop where
  pc : state.pc = if remaining = 0 then 4364 else 4280
  counter : (state.getReg .x20).toNat + remaining = (state.getReg .x19).toNat
  bounded : (state.getReg .x19).toNat ≤ 2 ^ 24
  scratch : state.getReg .x21 = 256
  message : ∀ word < 32 * remaining,
    accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word)) 8 = true
  salts : ∀ word < 4 * remaining,
    accessValid (state.getReg .x18 + BitVec.ofNat 64 (8 * word)) 8 = true
  heap : ∀ word < 4 * remaining,
    accessValid (state.getReg .x23 + BitVec.ofNat 64 (8 * word)) 8 = true
  oracleReady : CommitLeafOracleReady state
  blockCounter : state.getReg .x28=0
  messageProgress : (state.getReg .x8).toNat+256*remaining=(state.getReg .x26).toNat

theorem message_step_nooverflow (pointer limit : Word) (remaining : Nat)
    (progress : pointer.toNat+256*(remaining+1)=limit.toNat) :
    (pointer+256).toNat=pointer.toNat+256 := by
  rw [BitVec.toNat_add]
  change (pointer.toNat+256)%18446744073709551616=pointer.toNat+256
  apply Nat.mod_eq_of_lt
  have small := BitVec.isLt limit
  change limit.toNat<18446744073709551616 at small
  omega

theorem message_step_branch (pointer limit : Word) (remaining : Nat)
    (progress : pointer.toNat+256*(remaining+1)=limit.toNat) :
    BitVec.ult (pointer+256) limit=decide (0<remaining) := by
  simp only [BitVec.ult,message_step_nooverflow pointer limit remaining progress]
  have equivalent : pointer.toNat+256<limit.toNat ↔ 0<remaining := by omega
  simp only [equivalent]

theorem commit_leaves_next_invariant (state finished : MachineState) (remaining : Nat)
    (invariant : CommitLeavesInvariant state (remaining + 1))
    (reachable : finished ∈ support (commitPositionRun state)) :
    CommitLeavesInvariant finished remaining := by
  have regs := commit_position_registers state finished reachable
  have counter : (state.getReg .x20 + 1).toNat = (state.getReg .x20).toNat + 1 := by
    rw [BitVec.toNat_add]
    change ((state.getReg .x20).toNat + 1) % 18446744073709551616 = _
    apply Nat.mod_eq_of_lt
    have := invariant.counter
    have := invariant.bounded
    omega
  have branch : BitVec.ult (state.getReg .x20 + 1) (state.getReg .x19) =
      decide (0 < remaining) := by
    simp only [BitVec.ult, counter]
    have equivalent : (state.getReg .x20).toNat + 1 < (state.getReg .x19).toNat ↔ 0 < remaining := by
      have := invariant.counter
      omega
    simp only [equivalent]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [regs.2.2.2.2.1, branch]
    by_cases empty : remaining = 0 <;> simp [empty, Nat.pos_of_ne_zero]
  · rw [regs.2.2.2.1, regs.2.2.2.2.2 .x19 (by simp), counter]
    have := invariant.counter
    omega
  · rw [regs.2.2.2.2.2 .x19 (by simp)]
    exact invariant.bounded
  · exact (regs.2.2.2.2.2 .x21 (by simp)).trans invariant.scratch
  · intro word bounded
    rw [regs.1]
    have address : state.getReg .x8 + 256 + BitVec.ofNat 64 (8 * word) =
        state.getReg .x8 + BitVec.ofNat 64 (8 * (word + 32)) := by
      rw [show 8 * (word + 32) = 256 + 8 * word by omega, BitVec.ofNat_add, BitVec.add_assoc]; rfl
    rw [address]
    exact invariant.message (word + 32) (by omega)
  · intro word bounded
    rw [regs.2.1]
    have address : state.getReg .x18 + 32 + BitVec.ofNat 64 (8 * word) =
        state.getReg .x18 + BitVec.ofNat 64 (8 * (word + 4)) := by
      rw [show 8 * (word + 4) = 32 + 8 * word by omega, BitVec.ofNat_add, BitVec.add_assoc]; rfl
    rw [address]
    exact invariant.salts (word + 4) (by omega)
  · intro word bounded
    rw [regs.2.2.1]
    have address : state.getReg .x23 + 32 + BitVec.ofNat 64 (8 * word) =
        state.getReg .x23 + BitVec.ofNat 64 (8 * (word + 4)) := by
      rw [show 8 * (word + 4) = 32 + 8 * word by omega, BitVec.ofNat_add, BitVec.add_assoc]; rfl
    rw [address]
    exact invariant.heap (word + 4) (by omega)

  · exact (commit_position_oracle_ready state finished invariant.scratch reachable).1
  · exact (commit_position_oracle_ready state finished invariant.scratch reachable).2
  · rw [regs.1,regs.2.2.2.2.2 .x26 (by simp),
      message_step_nooverflow _ _ remaining invariant.messageProgress]
    have := invariant.messageProgress
    omega

/-- Loop state distribution, using precisely the same queries as the machine. -/
def commitLeaves : MachineState → Nat → OracleComp World MachineState
  | state, 0 => pure state
  | state, remaining + 1 => do
      let next ← commitPositionRun state
      commitLeaves next remaining

attribute [local irreducible] execute commitPositionRun

/-- The physical loop carries no incrementing position counter. Its heap pointer
selects the same iteration count as the reference counter. -/
theorem outer_position_execute (state : MachineState) (remaining : Nat)
    (invariant : CommitLeavesInvariant state (remaining+1)) (fuel : Nat) :
    execute (submission.image .commit) (94+fuel) (outerFinish state 4280) true =
      (do let next ← commitPositionRun state
          let result ← execute (submission.image .commit) fuel
            (outerFinish next (if remaining=0 then 4360 else 4280)) true
          return result.charge 150 8) := by
  have regs (reg : Reg) (ne : reg ≠ .x20) :
      (outerFinish state 4280).getReg reg=state.getReg reg := by
    simp [outerFinish,MachineState.getReg_setPC,MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm ne)]
  have ready : CommitLeafOracleReady (outerFinish state 4280) := by
    rcases invariant.oracleReady with ⟨a,b,c,d,e⟩
    exact ⟨(regs .x5 (by decide)).trans a,(regs .x10 (by decide)).trans b,
      (regs .x11 (by decide)).trans c,(regs .x12 (by decide)).trans d,
      (regs .x13 (by decide)).trans e⟩
  rw [commit_position _ rfl ((regs .x21 (by decide)).trans invariant.scratch) ready
    ((regs .x28 (by decide)).trans invariant.blockCounter)
    (fun word => by rw [regs .x18 (by decide)]; exact invariant.salts word.val (by omega))
    (fun word => by rw [regs .x23 (by decide)]; exact invariant.heap word.val (by omega))
    (fun word bounded => by rw [regs .x8 (by decide)]; exact invariant.message word (by omega))]
  have branch : (if BitVec.ult (state.getReg .x8+256) (state.getReg .x26) then
      (4280 : Word) else 4360)=(if remaining=0 then 4360 else 4280) := by
    rw [message_step_branch _ _ remaining invariant.messageProgress]
    by_cases empty : remaining=0 <;> simp [empty,Nat.pos_of_ne_zero]
  simp only [regs .x8 (by decide),regs .x26 (by decide),
    show (outerFinish state 4280).getReg .x20=0 by rfl,branch]
  change (do let next ← commitPositionRun ((state.setReg .x20 0).setPC 4280)
             let result ← execute (submission.image .commit) fuel
               (outerFinish next (if remaining=0 then 4360 else 4280)) true
             return result.charge 150 8) = _
  rw [outer_position_run_pc]
  exact outer_position_bind state 0 (if remaining=0 then 4360 else 4280)
    (fun finished => do
      let result ← execute (submission.image .commit) fuel finished true
      return result.charge 150 8)

/-- Every leaf is processed: 94 instructions, 150 cycles and eight queries. -/
theorem commit_leaves (state : MachineState) (remaining : Nat)
    (invariant : CommitLeavesInvariant state remaining) (fuel : Nat) :
    execute (submission.image .commit) (94*remaining+fuel)
      (outerFinish state (if remaining=0 then 4360 else 4280)) true =
      (do let finished ← commitLeaves state remaining
          let result ← execute (submission.image .commit) fuel (outerFinish finished 4360) true
          return result.charge (150*remaining) (8*remaining)) := by
  induction remaining generalizing state with
  | zero => simp [commitLeaves,Execution.charge]
  | succ remaining ih =>
    rw [show 94*(remaining+1)+fuel=94+(94*remaining+fuel) by omega]
    simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte]
    rw [outer_position_execute state remaining invariant]
    simp only [commitLeaves,bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro next reached
    rw [ih next (commit_leaves_next_invariant state next remaining invariant reached)]
    simp [Execution.charge,Nat.mul_add,Nat.add_comm,Nat.add_left_comm]

/-- The outer loop preserves the globally initialized syscall arguments. -/
theorem commit_leaves_oracle_ready (state : MachineState) (remaining : Nat)
    (invariant : CommitLeavesInvariant state remaining) (finished : MachineState)
    (reachable : finished ∈ support (commitLeaves state remaining)) :
    CommitLeafOracleReady finished := by
  induction remaining generalizing state with
  | zero =>
    simp only [commitLeaves,support_pure,Set.mem_singleton_iff] at reachable
    subst finished
    exact invariant.oracleReady
  | succ remaining ih =>
    simp only [commitLeaves,mem_support_bind_iff] at reachable
    obtain ⟨next,reached,rest⟩ := reachable
    exact ih next (commit_leaves_next_invariant state next remaining invariant reached) rest

/-- The leaf loop reaches the parent-building phase and preserves its pointers. -/
theorem commit_leaves_finished (state : MachineState) (remaining : Nat)
    (invariant : CommitLeavesInvariant state remaining) (finished : MachineState)
    (reachable : finished ∈ support (commitLeaves state remaining)) :
    finished.pc = 4364 ∧
    ∀ reg ∈ [Reg.x9, .x19, .x21, .x26], finished.getReg reg = state.getReg reg := by
  induction remaining generalizing state with
  | zero =>
    simp only [commitLeaves, support_pure, Set.mem_singleton_iff] at reachable
    subst finished
    exact ⟨by simpa using invariant.pc, fun _ _ => rfl⟩
  | succ remaining ih =>
    simp only [commitLeaves, mem_support_bind_iff] at reachable
    obtain ⟨next, reached, rest⟩ := reachable
    have done := ih next (commit_leaves_next_invariant state next remaining invariant reached) rest
    exact ⟨done.1, fun reg member => (done.2 reg member).trans
      ((commit_position_registers state next reached).2.2.2.2.2 reg (by simp only [List.mem_cons,List.not_mem_nil,or_false] at member ⊢; tauto))⟩

end CommitGolfCandidate
