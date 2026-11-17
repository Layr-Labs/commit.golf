import CommitGolfCandidate.TwoPermutationWideParents

namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
attribute [local irreducible] execute

structure LongParentControl (image : Image) (base : Word) (span : Nat) where
  backOffset : BitVec 21
  backTarget : wideParentPC base span+4+signExtend21 backOffset=base
  branch : ∀ state : MachineState, state.pc=wideParentPC base span →
    fetch image state=some (.base (.BEQ .x12 .x9 8))
  jump : ∀ state : MachineState, state.pc=wideParentPC base span+4 →
    fetch image state=some (.base (.JAL .x0 backOffset))

def longParentNextPC (base : Word) (span remaining : Nat) : Word :=
  if remaining=0 then wideParentPC base span+8 else base

def longParentLatchCost (remaining : Nat) : Nat := if remaining=0 then 1 else 2

private theorem parent_at_zero (state : MachineState) (remaining : Nat)
    (limit : remaining<2^24) (regs : ParentRegs state remaining) :
    state.getReg .x12=state.getReg .x9 ↔ remaining=0 := by
  rw [regs.target,regs.heap]
  constructor
  · intro same
    have index := wordAddress_injective_of_bound (a := treeWord remaining) (b := treeWord 0)
      (by unfold treeWord; omega) (by decide) same
    unfold treeWord at index
    omega
  · rintro rfl
    rfl

theorem wide_parent_latch (image : Image) (base : Word) (span : Nat)
    (control : LongParentControl image base span) (remaining fuel : Nat) (state : MachineState)
    (bound : remaining<2^24) (regs : ParentRegs state remaining) (pc : state.pc=wideParentPC base span) :
    execute image (longParentLatchCost remaining+fuel) state true =
      (do let result ← execute image fuel (state.setPC (longParentNextPC base span remaining)) true
          return result.charge (longParentLatchCost remaining) 0) := by
  have equal := parent_at_zero state remaining bound regs
  by_cases last : remaining=0
  · have branch : ordinaryStep state (.base (.BEQ .x12 .x9 8)) =
        some (state.setPC (wideParentPC base span+8)) := by
      simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,pc,equal.mpr last,signExtend13]
    rw [longParentLatchCost,if_pos last,longParentNextPC,if_pos last,Nat.add_comm 1 fuel,
      CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (control.branch state pc) branch]
    rfl
  · let branchState := state.setPC (wideParentPC base span+4)
    have different : state.getReg .x12≠state.getReg .x9 := fun same => last (equal.mp same)
    have branch : ordinaryStep state (.base (.BEQ .x12 .x9 8))=some branchState := by
      simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,pc,different,branchState]
    have jump : ordinaryStep branchState (.base (.JAL .x0 control.backOffset)) =
        some (state.setPC base) := by
      simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,branchState,
        MachineState.setReg,MachineState.setPC]
      exact control.backTarget
    have branchPC : branchState.pc=wideParentPC base span+4 := rfl
    rw [longParentLatchCost,if_neg last,longParentNextPC,if_neg last,
      show 2+fuel=(fuel+1)+1 by omega,
      CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (control.branch state pc) branch,
      CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (control.jump branchState branchPC) jump]
    simp [instructionCycles,Execution.charge,←Nat.add_assoc]

def wideParentGroups (base : Word) (span : Nat) :
    Nat → MachineState → OracleComp World MachineState
  | 0, state => pure state
  | groups+1, state => do
    let body ← parentsTrace (span*groups) span state
    wideParentGroups base span groups (body.setPC (longParentNextPC base span (span*groups)))

private def wideCount (baseCost span groups : Nat) : Nat :=
  baseCost*span*groups + (if groups=0 then 0 else 2*groups-1)

private theorem wide_count_step (baseCost span groups : Nat) (positive : 0<span) :
    wideCount baseCost span (groups+1) =
      baseCost*span+longParentLatchCost (span*groups)+wideCount baseCost span groups := by
  cases groups with
  | zero => simp [wideCount,longParentLatchCost]
  | succ groups =>
    have nonzero : span*(groups+1)≠0 := Nat.ne_of_gt (Nat.mul_pos positive (Nat.succ_pos _))
    simp only [wideCount,longParentLatchCost,Nat.succ_ne_zero,ite_false,nonzero]
    rw [Nat.mul_succ (baseCost*span) (groups+1)]
    omega

theorem wide_group_execution (image : Image) (base : Word) (span : Nat)
    (fetches : ∀ i < span, ParentWordsAt image (wideParentPC base i))
    (control : LongParentControl image base span) (positive : 0<span)
    (groups fuel : Nat) (state : MachineState) (bound : span*groups<2^24)
    (regs : ParentRegs state (span*groups)) (pc : 0<groups → state.pc=base) :
    execute image (wideCount 3 span groups+fuel) state true =
      (do let out ← wideParentGroups base span groups state
          let result ← execute image fuel out true
          return result.charge (wideCount 10 span groups) (span*groups)) := by
  induction groups generalizing state with
  | zero => simp [wideParentGroups,wideCount,Execution.charge]
  | succ groups ih =>
    rw [Nat.mul_succ] at bound regs
    have enter : state.pc=wideParentPC base 0 := by
      rw [pc (by omega)]
      simp [wideParentPC]
    rw [wide_count_step 3 span groups positive,
      show 3*span+longParentLatchCost (span*groups)+wideCount 3 span groups+fuel =
        3*span+(longParentLatchCost (span*groups)+(wideCount 3 span groups+fuel)) by omega,
      wide_parent_segment image base span fetches (span*groups) span 0 _ state bound
        (by omega) regs enter]
    simp only [wideParentGroups,bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro body reached
    have after := wide_parent_segment_post base (span*groups) span 0 state regs enter reached
    have ending : body.pc=wideParentPC base span := by simpa only [Nat.zero_add] using after.2
    rw [wide_parent_latch image base span control (span*groups) _ body (by omega) after.1 ending]
    let next := body.setPC (longParentNextPC base span (span*groups))
    have continued : ParentRegs next (span*groups) :=
      ⟨after.1.source,after.1.target,after.1.selector,after.1.size,after.1.primitive,after.1.heap⟩
    have again (notLast : 0<groups) : next.pc=base := by
      have notZero : span*groups≠0 := Nat.ne_of_gt (Nat.mul_pos positive notLast)
      simp only [next,MachineState.setPC,longParentNextPC,notZero,ite_false]
    rw [show body.setPC (longParentNextPC base span (span*groups))=next from rfl,
      ih next (by omega) continued again,wide_count_step 10 span groups positive]
    simp [Execution.charge,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm,Nat.mul_succ]

theorem wide_groups_post (base : Word) (span groups : Nat) (state : MachineState)
    (positive : 0<span) (entry : 0<groups → state.pc=base)
    (regs : ParentRegs state (span*groups))
    {out : MachineState} (reached : out ∈ support (wideParentGroups base span groups state)) :
    ParentRegs out 0 ∧ (0<groups → out.pc=wideParentPC base span+8) := by
  induction groups generalizing state with
  | zero =>
    simp only [wideParentGroups,support_pure,Set.mem_singleton_iff] at reached
    subst out
    exact ⟨by simpa only [Nat.mul_zero] using regs,by omega⟩
  | succ groups ih =>
    simp only [wideParentGroups,mem_support_bind_iff] at reached
    obtain ⟨body,path,tail⟩ := reached
    have start : state.pc=wideParentPC base 0 := by
      rw [entry (by omega)]
      simp [wideParentPC]
    have ready : ParentRegs state (span*groups+span) := by simpa only [Nat.mul_succ] using regs
    have after := wide_parent_segment_post base (span*groups) span 0 state ready start path
    let next := body.setPC (longParentNextPC base span (span*groups))
    have stillReady : ParentRegs next (span*groups) :=
      ⟨after.1.source,after.1.target,after.1.selector,after.1.size,after.1.primitive,after.1.heap⟩
    have again (notLast : 0<groups) : next.pc=base := by
      have notZero : span*groups≠0 := Nat.ne_of_gt (Nat.mul_pos positive notLast)
      simp only [next,MachineState.setPC,longParentNextPC,notZero,ite_false]
    have rest := ih next again stillReady tail
    refine ⟨rest.1,fun _ => ?_⟩
    by_cases last : groups=0
    · subst groups
      simp only [wideParentGroups,support_pure,Set.mem_singleton_iff] at tail
      rw [tail]
      simp [longParentNextPC,MachineState.setPC]
    · exact rest.2 (Nat.pos_of_ne_zero last)

end TwoPermutationPrototype.RV64
