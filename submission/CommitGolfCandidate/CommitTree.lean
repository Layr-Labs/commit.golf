import CommitGolfCandidate.CommitParents
import CommitGolfCandidate.CommitLoop

/-! The complete parent loop, followed by root output and successful HALT. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

def commitParents : MachineState → Nat → OracleComp World MachineState
  | state, 0 => pure state
  | state, remaining + 1 => do
      let answer ← World.query (.inr (commitParentQuery state))
      commitParents (commitParentNextState (commitParentState state answer)) remaining

/-- The parent heap is readable/writable for every node still to be computed. -/
def ParentBuffers (base : Word) (remaining : Nat) : Prop :=
  ∀ node, 0 < node → node ≤ remaining →
    rangeValid (base + (BitVec.ofNat 64 node <<< 6)) 64 = true ∧
    rangeValid (base + (BitVec.ofNat 64 node <<< 5)) 32 = true ∧
    (base + (BitVec.ofNat 64 node <<< 6)).toNat % 8 = 0 ∧
    (base + (BitVec.ofNat 64 node <<< 5)).toNat % 8 = 0

theorem commit_parent_step_counter (state : MachineState) (answer : BitVec 256) :
    (commitParentNextState (commitParentState state answer)).getReg .x20 = state.getReg .x20 - 1 := by
  change (commitParentState state answer).getReg .x20 - 1 = _
  rw [commit_parent_register state answer .x20 (by simp)]

theorem commit_parent_step_register (state : MachineState) (answer : BitVec 256) (reg : Reg)
    (member : reg ∈ [Reg.x9, .x19, .x21, .x26]) :
    (commitParentNextState (commitParentState state answer)).getReg reg = state.getReg reg := by
  have not20 : Reg.x20 ≠ reg := by intro h; subst reg; simp at member
  rw [commitParentNextState, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ not20,
    MachineState.getReg_setReg_ne _ _ _ _ (by intro h; subst reg; simp at member : Reg.x12 ≠ reg),
    MachineState.getReg_setReg_ne _ _ _ _ (by intro h; subst reg; simp at member : Reg.x10 ≠ reg)]
  apply commit_parent_register
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
  tauto

theorem commit_parent_step_pc (state : MachineState) (answer : BitVec 256) :
    (commitParentNextState (commitParentState state answer)).pc =
      if state.getReg .x20 - 1 = 0 then 4464 else 4444 := by
  change (if (commitParentState state answer).getReg .x20 - 1 = 0 then 4464 else 4444) = _
  rw [commit_parent_register state answer .x20 (by simp)]



theorem commit_parent_step_args (state : MachineState) (answer : BitVec 256)
    (args : ParentArgsReady state) :
    ParentArgsReady (commitParentNextState (commitParentState state answer)) := by
  have shift6 (base node : Word) : base+(node <<< 6)-64=base+((node-1) <<< 6) := by
    simp only [BitVec.shiftLeft_eq_mul_twoPow]
    change base+node*64-64=base+(node-1)*64
    rw [BitVec.mul_comm (x := node-1),BitVec.mul_sub]
    simp only [BitVec.mul_comm]
    rw [show (1 : Word)*64=64 by decide]
    rw [BitVec.sub_eq_add_neg,BitVec.sub_eq_add_neg,BitVec.add_assoc]
  have shift5 (base node : Word) : base+(node <<< 5)-32=base+((node-1) <<< 5) := by
    simp only [BitVec.shiftLeft_eq_mul_twoPow]
    change base+node*32-32=base+(node-1)*32
    rw [BitVec.mul_comm (x := node-1),BitVec.mul_sub]
    simp only [BitVec.mul_comm]
    rw [show (1 : Word)*32=32 by decide]
    rw [BitVec.sub_eq_add_neg,BitVec.sub_eq_add_neg,BitVec.add_assoc]
  have regs (reg : Reg) : (commitParentState state answer).getReg reg=state.getReg reg :=
    writeBits_register _ _ _ _
  have nextReg (current : MachineState) (reg : Reg) :
      (commitParentNextState current).getReg reg=
        if reg=.x10 then current.getReg .x10-64 else
        if reg=.x12 then current.getReg .x12-32 else
        if reg=.x20 then current.getReg .x20-1 else current.getReg reg := by
    cases reg <;> rfl
  unfold ParentArgsReady
  simp only [nextReg,regs,↓reduceIte]
  change state.getReg .x10-64=state.getReg .x9+((state.getReg .x20-1) <<< 6) ∧
    state.getReg .x12-32=state.getReg .x9+((state.getReg .x20-1) <<< 5)
  rw [args.1,args.2]
  exact ⟨shift6 _ _,shift5 _ _⟩

attribute [local irreducible] execute commitParentState commitParentNextState

/-- All internal nodes are processed in descending heap order. Each costs seven
instructions, fourteen cycles, and one query, independently of oracle answers. -/
theorem commit_parents (state : MachineState) (remaining : Nat) (bounded : remaining < 2 ^ 24)
    (pc : 0 < remaining → state.pc = 4444)
    (counter : state.getReg .x20 = BitVec.ofNat 64 remaining)
    (constants : state.getReg .x5 = 0 ∧ state.getReg .x11 = 64 ∧ state.getReg .x13 = 0)
    (args : ParentArgsReady state)
    (buffers : ParentBuffers (state.getReg .x9) remaining) (fuel : Nat) :
    execute (submission.image .commit) (5 * remaining + fuel) state true =
      (do let finished ← commitParents state remaining
          let result ← execute (submission.image .commit) fuel finished true
          return result.charge (12 * remaining) remaining) := by
  induction remaining generalizing state with
  | zero => simp [commitParents, Execution.charge]
  | succ remaining ih =>
    have current := buffers (remaining + 1) (by omega) (by omega)
    rw [← counter] at current
    have nextCounter (answer : BitVec 256) :
        (commitParentNextState (commitParentState state answer)).getReg .x20 = BitVec.ofNat 64 remaining := by
      rw [commit_parent_step_counter, counter]
      change BitVec.ofNat 64 (remaining + 1) - BitVec.ofNat 64 1 = _
      rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) (remaining + 1) 1 (by decide) (by omega)]
      congr 1
    have nextPC (answer : BitVec 256) (positive : 0 < remaining) :
        (commitParentNextState (commitParentState state answer)).pc = 4444 := by
      rw [commit_parent_step_pc]
      apply if_neg
      rw [← commit_parent_step_counter state answer, nextCounter]
      intro zero
      have equal := congrArg BitVec.toNat zero
      change remaining % 18446744073709551616 = 0 at equal
      omega
    have nextBuffers (answer : BitVec 256) :
        ParentBuffers ((commitParentNextState (commitParentState state answer)).getReg .x9) remaining := by
      rw [commit_parent_step_register state answer .x9 (by simp)]
      exact fun node positive bound => buffers node positive (by omega)
    rw [show 5 * (remaining + 1) + fuel = 5 + (5 * remaining + fuel) by omega,
      commit_parent state (pc (by omega)) args constants current.1 current.2.1 current.2.2.1 current.2.2.2]
    simp only [commitParents, bind_assoc]
    apply congrArg (fun continuation =>
      (liftM (World.query (.inr (commitParentQuery state))) : OracleComp World (BitVec 256)) >>= continuation)
    funext answer
    change BitVec 256 at answer
    have nextConstants :
        (commitParentNextState (commitParentState state answer)).getReg .x5 = 0 ∧
        (commitParentNextState (commitParentState state answer)).getReg .x11 = 64 ∧
        (commitParentNextState (commitParentState state answer)).getReg .x13 = 0 := by
      have preserved (reg : Reg) (member : reg ∈ [Reg.x5, .x11, .x13]) :
          (commitParentNextState (commitParentState state answer)).getReg reg = state.getReg reg := by
        have ne : Reg.x20 ≠ reg := by intro h; subst reg; simp at member
        rw [commitParentNextState, MachineState.getReg_setPC,
          MachineState.getReg_setReg_ne _ _ _ _ ne,
          MachineState.getReg_setReg_ne _ _ _ _ (by intro h; subst reg; simp at member : Reg.x12 ≠ reg),
          MachineState.getReg_setReg_ne _ _ _ _ (by intro h; subst reg; simp at member : Reg.x10 ≠ reg)]
        apply commit_parent_register
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
        tauto
      rw [preserved .x5 (by simp), preserved .x11 (by simp), preserved .x13 (by simp)]
      exact constants
    rw [ih _ (by omega) (nextPC answer) (nextCounter answer) nextConstants (commit_parent_step_args state answer args) (nextBuffers answer)]
    simp [Execution.charge, Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

theorem commit_parents_finished (state : MachineState) (remaining : Nat)
    (bounded : remaining < 2 ^ 24)
    (counter : state.getReg .x20 = BitVec.ofNat 64 remaining)
    (finished : MachineState) (reachable : finished ∈ support (commitParents state remaining)) :
    (0 < remaining → finished.pc = 4464) ∧
    ∀ reg ∈ [Reg.x9, .x19, .x21, .x26], finished.getReg reg = state.getReg reg := by
  induction remaining generalizing state with
  | zero =>
    simp only [commitParents, support_pure, Set.mem_singleton_iff] at reachable
    subst finished
    exact ⟨by omega, fun _ _ => rfl⟩
  | succ remaining ih =>
    simp only [commitParents, mem_support_bind_iff] at reachable
    obtain ⟨answer, _, reached⟩ := reachable
    change BitVec 256 at answer
    have nextCounter : (commitParentNextState (commitParentState state answer)).getReg .x20 =
        BitVec.ofNat 64 remaining := by
      rw [commit_parent_step_counter, counter]
      change BitVec.ofNat 64 (remaining + 1) - BitVec.ofNat 64 1 = _
      rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) (remaining + 1) 1 (by decide) (by omega)]
      congr 1
    have done := ih _ (by omega) nextCounter reached
    refine ⟨?_, fun reg member => (done.2 reg member).trans (commit_parent_step_register state answer reg member)⟩
    intro _
    by_cases empty : remaining = 0
    · subst remaining
      simp only [commitParents, support_pure, Set.mem_singleton_iff] at reached
      subst finished
      rw [commit_parent_step_pc, counter]
      rfl
    · exact done.1 (Nat.pos_of_ne_zero empty)

/-- Initialize fixed syscall constants and the descending internal-node counter once. -/
private def parentStartInstructions : List Instr :=
  [.ADDI .x5 .x0 0, .ADDI .x11 .x0 64, .ADDI .x13 .x0 0,
   .ADDI .x20 .x19 4095]

private def parentStartPrefix (state : MachineState) (count : Nat) : MachineState :=
  (parentStartInstructions.take count).foldl execInstrBr state

def commitParentsStartState (state : MachineState) : MachineState :=
  (commitParentInitState (parentStartPrefix state 4)).setPC
    (if state.getReg .x19 - 1 = 0 then 4464 else 4444)

theorem commit_parents_start_register (state : MachineState) (reg : Reg)
    (member : reg ∈ [Reg.x9, .x19, .x21, .x26]) :
    (commitParentsStartState state).getReg reg = state.getReg reg := by
  change (commitParentInitState (parentStartPrefix state 4)).getReg reg=state.getReg reg
  rw [commit_parent_init_register _ reg (by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member ⊢;tauto)]
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl <;>
    simp [parentStartPrefix,parentStartInstructions,execInstrBr,MachineState.getReg,
      MachineState.setPC,MachineState.setReg]

theorem commit_parents_start_counter (state : MachineState) :
    (commitParentsStartState state).getReg .x20=state.getReg .x19-1 := by
  change (commitParentInitState (parentStartPrefix state 4)).getReg .x20=_
  rw [commit_parent_init_register _ .x20 (by simp)]
  simp [parentStartPrefix,parentStartInstructions,execInstrBr,MachineState.getReg,
    MachineState.setPC,MachineState.setReg,signExtend12,BitVec.sub_eq_add_neg]

theorem commit_parents_start_memory (state : MachineState) :
    (commitParentsStartState state).mem = state.mem := rfl

theorem commit_parents_start_constants (state : MachineState) :
    (commitParentsStartState state).getReg .x5=0 ∧
    (commitParentsStartState state).getReg .x11=64 ∧
    (commitParentsStartState state).getReg .x13=0 := by
  simp only [commitParentsStartState,MachineState.getReg_setPC]
  rw [commit_parent_init_register _ .x5 (by simp),commit_parent_init_register _ .x11 (by simp),
    commit_parent_init_register _ .x13 (by simp)]
  simp [parentStartPrefix,parentStartInstructions,execInstrBr,MachineState.getReg,
    MachineState.setPC,MachineState.setReg,signExtend12]

private theorem parent_start_ready (state : MachineState) (ready : CommitLeafOracleReady state) :
    parentStartPrefix state 4 =
      (state.setReg .x20 (state.getReg .x19-1)).setPC (state.pc+16) := by
  cases state
  dsimp [CommitLeafOracleReady,StreamingOracleReady,MachineState.getReg] at ready
  dsimp [parentStartPrefix,parentStartInstructions,List.take,List.foldl,execInstrBr,
    signExtend12,MachineState.getReg,MachineState.setReg,MachineState.setPC]
  simp only [BitVec.sub_eq_add_neg]
  congr 1
  · funext reg
    cases reg <;> simp_all [BitVec.sub_eq_add_neg]
  · simp [BitVec.add_assoc]

theorem commit_parents_start (state : MachineState) (pc : state.pc=4420)
    (ready : CommitLeafOracleReady state) (nonempty : state.getReg .x19-1≠0) (fuel : Nat) :
    execute (submission.image .commit) (6+fuel) state true =
      (do let result ← execute (submission.image .commit) fuel (commitParentsStartState state) true
          return result.charge 6 0) := by
  let counter := (state.setReg .x20 (state.getReg .x19-1)).setPC 4424
  let initialized := (state.setReg .x20 (state.getReg .x19-1)).setPC 4428
  have f0 : fetch (submission.image .commit) state=some (.base (.ADDI .x20 .x19 4095)) := by
    apply commit_fetch _ 81 _ (by decide) pc; rfl
  have s0 : ordinaryStep state (.base (.ADDI .x20 .x19 4095))=some counter := by
    simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,signExtend12,
      counter,pc,BitVec.sub_eq_add_neg]
  have f1 : fetch (submission.image .commit) counter=some (.base (.BEQ .x20 .x0 40)) := by
    apply commit_fetch _ 82 _ (by decide) rfl; rfl
  have s1 : ordinaryStep counter (.base (.BEQ .x20 .x0 40))=some initialized := by
    simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,signExtend13,
      counter,initialized,MachineState.getReg,MachineState.setReg,MachineState.setPC]
    exact nonempty
  have done : commitParentInitState initialized=commitParentsStartState state := by
    unfold commitParentsStartState
    rw [parent_start_ready state ready,if_neg nonempty]
    cases state
    rfl
  rw [show 6+fuel=(4+fuel+1)+1 by omega,
    execute_ordinary_step _ _ _ _ _ _ f0 s0,execute_ordinary_step _ _ _ _ _ _ f1 s1,
    commit_parent_init initialized rfl,done]
  simp [instructionCycles,Execution.charge,← Nat.add_assoc]

theorem commit_parents_start_ready (state : MachineState) : ParentArgsReady (commitParentsStartState state) := by
  simpa only [ParentArgsReady,commitParentsStartState,MachineState.getReg_setPC] using
    (commit_parent_init_ready (parentStartPrefix state 4))

def commitExitState (state : MachineState) : MachineState :=
  ((state.setReg .x5 1).setReg .x10 0).setPC 4504

theorem commit_exit (state : MachineState) (pc : state.pc = 4496) (fuel : Nat) :
    execute (submission.image .commit) (3 + fuel) state true =
      pure ⟨.success, commitExitState state, 3, 0⟩ := by
  let next := (state.setReg .x5 1).setPC 4500
  have f0 : fetch (submission.image .commit) state = some (.base (.ADDI .x5 .x0 1)) := by
    apply commit_fetch _ 100 _ (by decide) pc; rfl
  have f1 : fetch (submission.image .commit) next = some (.base (.ADDI .x10 .x0 0)) := by
    apply commit_fetch _ 101 _ (by decide) rfl; rfl
  have f2 : fetch (submission.image .commit) (commitExitState state) = some (.base .ECALL) := by
    apply commit_fetch _ 102 _ (by decide) rfl; rfl
  have s0 : ordinaryStep state (.base (.ADDI .x5 .x0 1)) = some next := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      next, pc, MachineState.getReg]
  have s1 : ordinaryStep next (.base (.ADDI .x10 .x0 0)) = some (commitExitState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      next, commitExitState, MachineState.getReg, MachineState.setPC, MachineState.setReg]
  rw [Nat.add_comm 3 fuel]
  simp only [execute, f0, s0, f1, s1, f2, instructionCycles, bind_assoc, pure_bind]
  simp [commitExitState, MachineState.getReg, MachineState.setReg, MachineState.setPC, Execution.charge]

/-- Copy the root from heap node one into the public commitment buffer, then halt
successfully. This costs eleven cycles and makes no oracle queries. -/
theorem commit_root (state : MachineState) (pc : state.pc = 4464)
    (rootValid : ∀ word : Fin 4,
      accessValid (state.getReg .x9 + BitVec.ofNat 64 (32 + 8 * word.val)) 8 = true)
    (outputValid : ∀ word : Fin 4,
      accessValid (state.getReg .x26 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) :
    execute (submission.image .commit) (11 + fuel) state true =
      pure ⟨.success, commitExitState (commitCopyState state 92), 11, 0⟩ := by
  have nextPC : (commitCopyState state 92).pc = 4496 := by rw [commit_copy_pc, pc]; rfl
  rw [show 11 + fuel = 8 + (3 + fuel) by omega,
    commit_copy state 92 (Or.inr rfl) pc rootValid outputValid,
    commit_exit _ nextPC]
  rfl

/-- State distribution of the full tree-building phase, after salts are sampled. -/
def commitBody (state : MachineState) (count : Nat) : OracleComp World MachineState := do
  let leaves ← commitLeaves state count
  let parents ← commitParents (commitParentsStartState leaves) (count - 1)
  return commitExitState (commitCopyState parents 92)

attribute [local irreducible] commitLeaves commitParents commitCopyState

set_option maxRecDepth 4096 in
/-- Exact execution of all leaves, all internal nodes, and root output. Safety
conditions constrain addresses only; the theorem covers every message and salt. -/
theorem commit_body (state : MachineState) (count : Nat)
    (positive : 2 ≤ count) (bounded : count ≤ 2 ^ 24)
    (leaves : CommitLeavesInvariant state count)
    (total : state.getReg .x19 = BitVec.ofNat 64 count)
    (parents : ParentBuffers (state.getReg .x9) (count - 1))
    (rootValid : ∀ word : Fin 4,
      accessValid (state.getReg .x9 + BitVec.ofNat 64 (32 + 8 * word.val)) 8 = true)
    (outputValid : ∀ word : Fin 4,
      accessValid (state.getReg .x26 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) :
    execute (submission.image .commit) (40 * count + 12 + fuel) state true =
      (do let finished ← commitBody state count
          return ⟨.success, finished, 103 * count + 5, 9 * count - 1⟩) := by
  rw [show 40 * count + 12 + fuel =
    35 * count + (6 + (5 * (count - 1) + (11 + fuel))) by omega,
    commit_leaves state count leaves]
  simp only [commitBody, bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro hashed reached
  have leafDone := commit_leaves_finished state count leaves hashed reached
  let ready := commitParentsStartState hashed
  have readyRegister (reg : Reg) (member : reg ∈ [Reg.x9, .x19, .x26]) :
      ready.getReg reg = hashed.getReg reg := by
    apply commit_parents_start_register hashed reg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
    tauto
  have readyCount : ready.getReg .x20 = BitVec.ofNat 64 (count - 1) := by
    rw [commit_parents_start_counter]
    change hashed.getReg .x19 - 1 = _
    rw [leafDone.2 .x19 (by simp), total]
    change BitVec.ofNat 64 count - BitVec.ofNat 64 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) count 1 (by decide) (by omega)]
  have readyPC : 0 < count - 1 → ready.pc = 4444 := by
    intro _
    change (if hashed.getReg .x19 - 1 = 0 then 4464 else 4444) = _
    rw [leafDone.2 .x19 (by simp), total]
    apply if_neg
    change BitVec.ofNat 64 count - BitVec.ofNat 64 1 ≠ 0
    rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) count 1 (by decide) (by omega)]
    intro zero
    have equal := congrArg BitVec.toNat zero
    change (count - 1) % 18446744073709551616 = 0 at equal
    omega
  have readyHeap : ready.getReg .x9 = state.getReg .x9 :=
    (readyRegister .x9 (by simp)).trans (leafDone.2 .x9 (by simp))
  have readyOutput : ready.getReg .x26 = state.getReg .x26 :=
    (readyRegister .x26 (by simp)).trans (leafDone.2 .x26 (by simp))
  have readyBuffers : ParentBuffers (ready.getReg .x9) (count - 1) := by
    rw [readyHeap]; exact parents
  have leafReady := commit_leaves_oracle_ready state count leaves hashed reached
  have nonempty : hashed.getReg .x19-1≠0 := by
    rw [leafDone.2 .x19 (by simp),total]
    change BitVec.ofNat 64 count-BitVec.ofNat 64 1≠0
    rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) count 1 (by decide) (by omega)]
    intro zero
    have eq := congrArg BitVec.toNat zero
    change (count-1)%18446744073709551616=0 at eq
    omega
  rw [commit_parents_start hashed leafDone.1 leafReady nonempty,
    commit_parents ready (count - 1) (by omega) readyPC readyCount (commit_parents_start_constants hashed) (commit_parents_start_ready hashed) readyBuffers]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro finished reachedParents
  have parentDone := commit_parents_finished ready (count - 1) (by omega) readyCount finished reachedParents
  have root : ∀ word : Fin 4,
      accessValid (finished.getReg .x9 + BitVec.ofNat 64 (32 + 8 * word.val)) 8 = true := by
    rw [parentDone.2 .x9 (by simp), readyHeap]; exact rootValid
  have output : ∀ word : Fin 4,
      accessValid (finished.getReg .x26 + BitVec.ofNat 64 (8 * word.val)) 8 = true := by
    rw [parentDone.2 .x26 (by simp), readyOutput]; exact outputValid
  rw [commit_root finished (parentDone.1 (by omega)) root output]
  simp only [pure_bind, Execution.charge, Nat.add_zero]
  congr 1
  congr 1 <;> omega

end CommitGolfCandidate
