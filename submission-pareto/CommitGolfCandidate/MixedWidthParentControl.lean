import CommitGolfCandidate.MixedWidthParentCore

/-! Stop a full-width descending parent phase at an explicit nonzero boundary.
The boundary is the last *unprocessed* node, not the first full-width node.
-/
namespace TwoPermutationPrototype.RV64.FullWidth
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
attribute [local irreducible] execute parentAfter

structure ParentControl (image : Image) (base : Word) (span : Nat) where
  backOffset : BitVec 21
  backTarget : parentPC base span+4+signExtend21 backOffset=base
  branch : ∀ s : MachineState, s.pc=parentPC base span →
    fetch image s=some (.base (.BEQ .x12 .x17 8))
  jump : ∀ s : MachineState, s.pc=parentPC base span+4 →
    fetch image s=some (.base (.JAL .x0 backOffset))

def nextPC (base : Word) (span boundary remaining : Nat) : Word :=
  if remaining=boundary then parentPC base span+8 else base

def latchCost (boundary remaining : Nat) : Nat := if remaining=boundary then 1 else 2

theorem parent_keeps_stop (s : MachineState) (n : Nat) (reply : BitVec 256) :
    (parentAfter s n reply).getReg .x17=s.getReg .x17 := by
  simp only [parentAfter,execInstrBr,MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x10≠Reg.x17),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12≠Reg.x17)]
  exact CommitGolfCandidate.writeBits_register ..

theorem segment_keeps_stop (remaining count : Nat) (s out : MachineState)
    (hit : out ∈ support (parentsTrace remaining count s)) :
    out.getReg .x17=s.getReg .x17 := by
  induction count generalizing s with
  | zero =>
    simp only [parentsTrace,support_pure,Set.mem_singleton_iff] at hit
    subst out
    rfl
  | succ count ih =>
    simp only [parentsTrace,mem_support_bind_iff] at hit
    obtain ⟨answer,_,tail⟩ := hit
    exact (ih _ tail).trans (parent_keeps_stop s _ answer)

theorem parent_latch (image : Image) (base : Word) (span : Nat)
    (control : ParentControl image base span) (boundary remaining fuel : Nat) (s : MachineState)
    (bound : remaining<2^24) (boundaryBound : boundary<2^24)
    (regs : ParentRegs s remaining) (stop : s.getReg .x17=wordAddress (treeWord boundary))
    (pc : s.pc=parentPC base span) :
    execute image (latchCost boundary remaining+fuel) s true =
      (do let result ← execute image fuel (s.setPC (nextPC base span boundary remaining)) true
          return result.charge (latchCost boundary remaining) 0) := by
  have equal : s.getReg .x12=s.getReg .x17 ↔ remaining=boundary := by
    rw [regs.target,stop]
    constructor
    · intro same
      have index := wordAddress_injective_of_bound (a := treeWord remaining) (b := treeWord boundary)
        (by unfold treeWord; omega) (by unfold treeWord; omega) same
      unfold treeWord at index
      omega
    · rintro rfl
      rfl
  by_cases last : remaining=boundary
  · have branch : ordinaryStep s (.base (.BEQ .x12 .x17 8)) =
        some (s.setPC (parentPC base span+8)) := by
      simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,pc,equal.mpr last,signExtend13]
    rw [latchCost,if_pos last,nextPC,if_pos last,Nat.add_comm 1 fuel,
      CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (control.branch s pc) branch]
    rfl
  · let branchState := s.setPC (parentPC base span+4)
    have different : s.getReg .x12≠s.getReg .x17 := fun same => last (equal.mp same)
    have branch : ordinaryStep s (.base (.BEQ .x12 .x17 8))=some branchState := by
      simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,pc,different,branchState]
    have jump : ordinaryStep branchState (.base (.JAL .x0 control.backOffset)) =
        some (s.setPC base) := by
      simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,branchState,
        MachineState.setReg,MachineState.setPC]
      exact control.backTarget
    have branchPC : branchState.pc=parentPC base span+4 := rfl
    rw [latchCost,if_neg last,nextPC,if_neg last,
      show 2+fuel=(fuel+1)+1 by omega,
      CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (control.branch s pc) branch,
      CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (control.jump branchState branchPC) jump]
    simp [instructionCycles,Execution.charge,←Nat.add_assoc]

def parentGroups (base : Word) (span boundary : Nat) : Nat → MachineState → OracleComp World MachineState
  | 0, s => pure s
  | groups+1, s => do
    let body ← parentsTrace (boundary+span*groups) span s
    parentGroups base span boundary groups (body.setPC (nextPC base span boundary (boundary+span*groups)))

def phaseCount (perParent span groups : Nat) : Nat :=
  perParent*span*groups + (if groups=0 then 0 else 2*groups-1)

private theorem phase_count_step (perParent span groups boundary : Nat) (positive : 0<span) :
    phaseCount perParent span (groups+1) =
      perParent*span+latchCost boundary (boundary+span*groups)+phaseCount perParent span groups := by
  cases groups with
  | zero => simp [phaseCount,latchCost]
  | succ groups =>
    have different : boundary+span*(groups+1)≠boundary := by
      intro same
      have zero : span*(groups+1)=0 := Nat.add_left_cancel
        (show boundary+span*(groups+1)=boundary+0 from by simpa using same)
      exact Nat.ne_of_gt (Nat.mul_pos positive (Nat.succ_pos groups)) zero
    simp only [phaseCount,latchCost,Nat.succ_ne_zero,ite_false,different]
    rw [Nat.mul_succ (perParent*span) (groups+1)]
    omega

theorem group_execution (image : Image) (base : Word) (span boundary : Nat)
    (fetches : ∀ i < span, ParentFetched image (parentPC base i))
    (control : ParentControl image base span) (positive : 0<span)
    (groups fuel : Nat) (s : MachineState) (bound : boundary+span*groups<2^24)
    (regs : ParentRegs s (boundary+span*groups))
    (stop : s.getReg .x17=wordAddress (treeWord boundary)) (pc : 0<groups → s.pc=base) :
    execute image (phaseCount 3 span groups+fuel) s true =
      (do let out ← parentGroups base span boundary groups s
          let result ← execute image fuel out true
          return result.charge (phaseCount 10 span groups) (span*groups)) := by
  induction groups generalizing s with
  | zero => simp [parentGroups,phaseCount,Execution.charge]
  | succ groups ih =>
    rw [Nat.mul_succ] at bound
    have enter : s.pc=parentPC base 0 := by
      rw [pc (by omega)]
      simp [parentPC]
    have entryRegs : ParentRegs s ((boundary+span*groups)+span) := by
      simpa only [Nat.mul_succ,Nat.add_assoc] using regs
    rw [phase_count_step 3 span groups boundary positive,
      show 3*span+latchCost boundary (boundary+span*groups)+phaseCount 3 span groups+fuel =
        3*span+(latchCost boundary (boundary+span*groups)+(phaseCount 3 span groups+fuel)) by omega,
      parents_segment image base span fetches (boundary+span*groups) span 0 _ s
        (by omega) (by omega) entryRegs enter]
    simp only [parentGroups,bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro body reached
    have after := parents_post base (boundary+span*groups) span 0 s entryRegs enter reached
    have ending : body.pc=parentPC base span := by simpa only [Nat.zero_add] using after.2
    have stopped : body.getReg .x17=wordAddress (treeWord boundary) :=
      (segment_keeps_stop _ _ s body reached).trans stop
    rw [parent_latch image base span control boundary (boundary+span*groups) _ body
      (by omega) (by omega) after.1 stopped ending]
    let next := body.setPC (nextPC base span boundary (boundary+span*groups))
    have continued : ParentRegs next (boundary+span*groups) :=
      ⟨after.1.source,after.1.target,after.1.selector,after.1.size,after.1.primitive,after.1.heap⟩
    have nextStop : next.getReg .x17=wordAddress (treeWord boundary) := stopped
    have again (notLast : 0<groups) : next.pc=base := by
      have different : boundary+span*groups≠boundary := by
        have pos := Nat.mul_pos positive notLast
        omega
      simp only [next,MachineState.setPC,nextPC,different,ite_false]
    rw [show body.setPC (nextPC base span boundary (boundary+span*groups))=next from rfl,
      ih next (by omega) continued nextStop again,phase_count_step 10 span groups boundary positive]
    simp [Execution.charge,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm,Nat.mul_succ]


theorem parent_keeps_register (s : MachineState) (n : Nat) (reply : BitVec 256) (reg : Reg)
    (source : Reg.x10≠reg) (target : Reg.x12≠reg) :
    (parentAfter s n reply).getReg reg=s.getReg reg := by
  simp only [parentAfter,execInstrBr,MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ source,
    MachineState.getReg_setReg_ne _ _ _ _ target]
  exact CommitGolfCandidate.writeBits_register ..

theorem segment_keeps_register (remaining count : Nat) (s out : MachineState) (reg : Reg)
    (source : Reg.x10≠reg) (target : Reg.x12≠reg)
    (hit : out ∈ support (parentsTrace remaining count s)) :
    out.getReg reg=s.getReg reg := by
  induction count generalizing s with
  | zero =>
    simp only [parentsTrace,support_pure,Set.mem_singleton_iff] at hit
    subst out
    rfl
  | succ count ih =>
    simp only [parentsTrace,mem_support_bind_iff] at hit
    obtain ⟨answer,_,tail⟩ := hit
    exact (ih _ tail).trans (parent_keeps_register s _ answer reg source target)

theorem groups_keep_register (base : Word) (span boundary groups : Nat)
    (s out : MachineState) (reg : Reg) (source : Reg.x10≠reg) (target : Reg.x12≠reg)
    (hit : out ∈ support (parentGroups base span boundary groups s)) :
    out.getReg reg=s.getReg reg := by
  induction groups generalizing s with
  | zero =>
    simp only [parentGroups,support_pure,Set.mem_singleton_iff] at hit
    subst out
    rfl
  | succ groups ih =>
    simp only [parentGroups,mem_support_bind_iff] at hit
    obtain ⟨body,path,tail⟩ := hit
    exact (ih _ tail).trans (segment_keeps_register _ _ s body reg source target path)

theorem groups_post (base : Word) (span boundary groups : Nat) (s : MachineState)
    (positive : 0<span) (entry : 0<groups → s.pc=base)
    (regs : ParentRegs s (boundary+span*groups))
    {out : MachineState} (hit : out ∈ support (parentGroups base span boundary groups s)) :
    ParentRegs out boundary ∧ (0<groups → out.pc=parentPC base span+8) := by
  induction groups generalizing s with
  | zero =>
    simp only [parentGroups,support_pure,Set.mem_singleton_iff] at hit
    subst out
    exact ⟨by simpa only [Nat.mul_zero,Nat.add_zero] using regs,by omega⟩
  | succ groups ih =>
    simp only [parentGroups,mem_support_bind_iff] at hit
    obtain ⟨body,path,tail⟩ := hit
    have start : s.pc=parentPC base 0 := by
      rw [entry (by omega)]
      simp [parentPC]
    have ready : ParentRegs s ((boundary+span*groups)+span) := by
      simpa only [Nat.mul_succ,Nat.add_assoc] using regs
    have after := parents_post base (boundary+span*groups) span 0 s ready start path
    let next := body.setPC (nextPC base span boundary (boundary+span*groups))
    have stillReady : ParentRegs next (boundary+span*groups) :=
      ⟨after.1.source,after.1.target,after.1.selector,after.1.size,after.1.primitive,after.1.heap⟩
    have again (notLast : 0<groups) : next.pc=base := by
      have different : boundary+span*groups≠boundary := by
        have pos := Nat.mul_pos positive notLast
        omega
      simp only [next,MachineState.setPC,nextPC,different,ite_false]
    have rest := ih next again stillReady tail
    refine ⟨rest.1,fun _ => ?_⟩
    by_cases last : groups=0
    · subst groups
      simp only [parentGroups,support_pure,Set.mem_singleton_iff] at tail
      subst out
      simp [nextPC,MachineState.setPC]
    · exact rest.2 (by omega)

end TwoPermutationPrototype.RV64.FullWidth
