import CommitGolfCandidate.GroupedQStep
import CommitGolfCandidate.TwoPermutationCounted

/-!
# The level-21 loop

`l21Trace remaining count` runs the parents at positions `remaining+count .. remaining+1`;
`l21Groups base span groups` runs `groups` passes of `span` parents, each pass followed by the latch
`beq x10,x7,+8; jal x0,<base>` (taken only after the last parent, when `x10 = x7`).
-/

namespace TwoPermutationPrototype.Grouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.RV64
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
attribute [local irreducible] execute

def l21Trace (remaining : Nat) : Nat → MachineState → OracleComp World MachineState
  | 0, state => pure state
  | count+1, state => do
    let answer ← (liftM (World.query (.inr (.inl (l21Input state (remaining+(count+1)))))) : OracleComp World (BitVec 256))
    l21Trace remaining count (l21After state (remaining+(count+1)) answer)

theorem l21_segment (image : Image) (base : Word) (span : Nat)
    (fetches : ∀ i < span, L21WordsAt image (l21PC base i))
    (remaining count slot fuel : Nat) (s : MachineState)
    (bound : remaining+count ≤ 2097152) (inside : slot+count≤span)
    (regs : L21Regs s (remaining+count)) (pc : s.pc=l21PC base slot) :
    execute image (3*count+fuel) s true =
      (do let mid ← l21Trace remaining count s
          let result ← execute image fuel mid true
          return result.charge (10*count) count) := by
  induction count generalizing slot s with
  | zero => simp [l21Trace,Execution.charge]
  | succ count ih =>
    rw [show 3*(count+1)+fuel=3+(3*count+fuel) by omega,
      l21_parent_step image s _ _ _ pc bound regs (fetches slot (by omega))]
    simp only [l21Trace,bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro answer _
    have next := l21_next_regs s (remaining+count) answer (by simpa only [Nat.add_assoc] using regs)
    have atNext := (l21_after_pc s (remaining+(count+1)) answer).trans
      ((congrArg (·+12) pc).trans (l21_pc_succ base slot))
    rw [ih (slot+1) _ (by omega) (by omega) (by simpa only [Nat.add_assoc] using next) atNext]
    simp [Execution.charge,Nat.mul_succ,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

theorem l21_segment_post (base : Word) (remaining count slot : Nat)
    (s : MachineState) (regs : L21Regs s (remaining+count)) (pc : s.pc=l21PC base slot)
    {out : MachineState} (reached : out ∈ support (l21Trace remaining count s)) :
    L21Regs out remaining ∧ out.pc=l21PC base (slot+count) := by
  induction count generalizing slot s with
  | zero =>
    simp only [l21Trace,support_pure,Set.mem_singleton_iff] at reached
    subst out
    exact ⟨regs,pc⟩
  | succ count ih =>
    simp only [l21Trace,mem_support_bind_iff] at reached
    obtain ⟨answer,_,tail⟩ := reached
    have next := l21_next_regs s (remaining+count) answer (by simpa only [Nat.add_assoc] using regs)
    have atNext := (l21_after_pc s (remaining+(count+1)) answer).trans
      ((congrArg (·+12) pc).trans (l21_pc_succ base slot))
    rw [show slot+(count+1)=slot+1+count by omega]
    exact ih (slot+1) _ (by simpa only [Nat.add_assoc] using next) atNext tail

theorem l21_trace_keeps_register (remaining count : Nat) (s : MachineState) (reg : Reg)
    (keptSource : .x10≠reg) (keptTarget : .x12≠reg)
    {out : MachineState} (reached : out ∈ support (l21Trace remaining count s)) :
    out.getReg reg=s.getReg reg := by
  induction count generalizing s with
  | zero =>
    simp only [l21Trace,support_pure,Set.mem_singleton_iff] at reached
    subst out; rfl
  | succ count ih =>
    simp only [l21Trace,mem_support_bind_iff] at reached
    obtain ⟨answer,_,tail⟩ := reached
    exact (ih _ tail).trans (l21_keeps_register s _ answer reg keptSource keptTarget)

def l21NextPC (base : Word) (span remaining : Nat) : Word :=
  if remaining=0 then l21PC base span+8 else base

structure L21Control (image : Image) (base : Word) (span : Nat) where
  backOffset : BitVec 21
  backTarget : l21PC base span+4+signExtend21 backOffset=base
  branch : ∀ state : MachineState, state.pc=l21PC base span →
    fetch image state=some (.base (.BEQ .x10 .x7 8))
  jump : ∀ state : MachineState, state.pc=l21PC base span+4 →
    fetch image state=some (.base (.JAL .x0 backOffset))

private theorem l21_at_zero (state : MachineState) (remaining : Nat)
    (limit : remaining ≤ 2097152) (regs : L21Regs state remaining) :
    state.getReg .x10=state.getReg .x7 ↔ remaining=0 := by
  rw [regs.source,regs.stop]
  constructor
  · intro same
    have index := wordAddress_injective_of_bound (a := l21Source remaining) (b := l21Source 0)
      (by unfold l21Source unitFirst cellFirst unitStride; omega) (by decide) same
    unfold l21Source unitFirst cellFirst unitStride at index
    omega
  · rintro rfl
    rfl

theorem l21_latch (image : Image) (base : Word) (span : Nat)
    (control : L21Control image base span) (remaining fuel : Nat) (state : MachineState)
    (bound : remaining ≤ 2097152) (regs : L21Regs state remaining) (pc : state.pc=l21PC base span) :
    execute image (longParentLatchCost remaining+fuel) state true =
      (do let result ← execute image fuel (state.setPC (l21NextPC base span remaining)) true
          return result.charge (longParentLatchCost remaining) 0) := by
  have equal := l21_at_zero state remaining bound regs
  by_cases last : remaining=0
  · have branch : ordinaryStep state (.base (.BEQ .x10 .x7 8)) =
        some (state.setPC (l21PC base span+8)) := by
      simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,pc,equal.mpr last,signExtend13]
    rw [longParentLatchCost,if_pos last,l21NextPC,if_pos last,Nat.add_comm 1 fuel,
      CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (control.branch state pc) branch]
    rfl
  · let branchState := state.setPC (l21PC base span+4)
    have different : state.getReg .x10≠state.getReg .x7 := fun same => last (equal.mp same)
    have branch : ordinaryStep state (.base (.BEQ .x10 .x7 8))=some branchState := by
      simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,pc,different,branchState]
    have jump : ordinaryStep branchState (.base (.JAL .x0 control.backOffset)) =
        some (state.setPC base) := by
      simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,branchState,
        MachineState.setReg,MachineState.setPC]
      exact control.backTarget
    have branchPC : branchState.pc=l21PC base span+4 := rfl
    rw [longParentLatchCost,if_neg last,l21NextPC,if_neg last,
      show 2+fuel=(fuel+1)+1 by omega,
      CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (control.branch state pc) branch,
      CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (control.jump branchState branchPC) jump]
    simp [instructionCycles,Execution.charge,←Nat.add_assoc]

def l21Groups (base : Word) (span : Nat) :
    Nat → MachineState → OracleComp World MachineState
  | 0, state => pure state
  | groups+1, state => do
    let body ← l21Trace (span*groups) span state
    l21Groups base span groups (body.setPC (l21NextPC base span (span*groups)))

/-- Steps (`baseCost = 3`) or cycles (`baseCost = 10`) of `groups` passes of `span` parents with
their latches (2 per pass, 1 after the last). -/
def loopCount (baseCost span groups : Nat) : Nat :=
  baseCost*span*groups + (if groups=0 then 0 else 2*groups-1)

theorem loop_count_step (baseCost span groups : Nat) (positive : 0<span) :
    loopCount baseCost span (groups+1) =
      baseCost*span+longParentLatchCost (span*groups)+loopCount baseCost span groups := by
  cases groups with
  | zero => simp [loopCount,longParentLatchCost]
  | succ groups =>
    have nonzero : span*(groups+1)≠0 := Nat.ne_of_gt (Nat.mul_pos positive (Nat.succ_pos _))
    simp only [loopCount,longParentLatchCost,Nat.succ_ne_zero,ite_false,nonzero]
    rw [Nat.mul_succ (baseCost*span) (groups+1)]
    omega

theorem l21_group_execution (image : Image) (base : Word) (span : Nat)
    (fetches : ∀ i < span, L21WordsAt image (l21PC base i))
    (control : L21Control image base span) (positive : 0<span)
    (groups fuel : Nat) (state : MachineState) (bound : span*groups ≤ 2097152)
    (regs : L21Regs state (span*groups)) (pc : 0<groups → state.pc=base) :
    execute image (loopCount 3 span groups+fuel) state true =
      (do let out ← l21Groups base span groups state
          let result ← execute image fuel out true
          return result.charge (loopCount 10 span groups) (span*groups)) := by
  induction groups generalizing state with
  | zero => simp [l21Groups,loopCount,Execution.charge]
  | succ groups ih =>
    rw [Nat.mul_succ] at bound regs
    have enter : state.pc=l21PC base 0 := by
      rw [pc (by omega)]
      simp [l21PC]
    rw [loop_count_step 3 span groups positive,
      show 3*span+longParentLatchCost (span*groups)+loopCount 3 span groups+fuel =
        3*span+(longParentLatchCost (span*groups)+(loopCount 3 span groups+fuel)) by omega,
      l21_segment image base span fetches (span*groups) span 0 _ state bound
        (by omega) regs enter]
    simp only [l21Groups,bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro body reached
    have after := l21_segment_post base (span*groups) span 0 state regs enter reached
    have ending : body.pc=l21PC base span := by simpa only [Nat.zero_add] using after.2
    rw [l21_latch image base span control (span*groups) _ body (by omega) after.1 ending]
    let next := body.setPC (l21NextPC base span (span*groups))
    have continued : L21Regs next (span*groups) :=
      ⟨after.1.source,after.1.target,after.1.selector,after.1.size,after.1.primitive,after.1.heap,after.1.stop⟩
    have again (notLast : 0<groups) : next.pc=base := by
      have notZero : span*groups≠0 := Nat.ne_of_gt (Nat.mul_pos positive notLast)
      simp only [next,MachineState.setPC,l21NextPC,notZero,ite_false]
    rw [show body.setPC (l21NextPC base span (span*groups))=next from rfl,
      ih next (by omega) continued again,loop_count_step 10 span groups positive]
    simp [Execution.charge,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm,Nat.mul_succ]

theorem l21_groups_post (base : Word) (span groups : Nat) (state : MachineState)
    (positive : 0<span) (entry : 0<groups → state.pc=base)
    (regs : L21Regs state (span*groups))
    {out : MachineState} (reached : out ∈ support (l21Groups base span groups state)) :
    L21Regs out 0 ∧ (0<groups → out.pc=l21PC base span+8) := by
  induction groups generalizing state with
  | zero =>
    simp only [l21Groups,support_pure,Set.mem_singleton_iff] at reached
    subst out
    exact ⟨by simpa only [Nat.mul_zero] using regs,by omega⟩
  | succ groups ih =>
    simp only [l21Groups,mem_support_bind_iff] at reached
    obtain ⟨body,path,tail⟩ := reached
    have start : state.pc=l21PC base 0 := by
      rw [entry (by omega)]
      simp [l21PC]
    have ready : L21Regs state (span*groups+span) := by simpa only [Nat.mul_succ] using regs
    have after := l21_segment_post base (span*groups) span 0 state ready start path
    let next := body.setPC (l21NextPC base span (span*groups))
    have stillReady : L21Regs next (span*groups) :=
      ⟨after.1.source,after.1.target,after.1.selector,after.1.size,after.1.primitive,after.1.heap,after.1.stop⟩
    have again (notLast : 0<groups) : next.pc=base := by
      have notZero : span*groups≠0 := Nat.ne_of_gt (Nat.mul_pos positive notLast)
      simp only [next,MachineState.setPC,l21NextPC,notZero,ite_false]
    have rest := ih next again stillReady tail
    refine ⟨rest.1,fun _ => ?_⟩
    by_cases last : groups=0
    · subst groups
      simp only [l21Groups,support_pure,Set.mem_singleton_iff] at tail
      rw [tail]
      simp [l21NextPC,MachineState.setPC]
    · exact rest.2 (Nat.pos_of_ne_zero last)

theorem l21_groups_keeps_register (base : Word) (span groups : Nat) (state : MachineState) (reg : Reg)
    (keptSource : .x10≠reg) (keptTarget : .x12≠reg)
    {out : MachineState} (reached : out ∈ support (l21Groups base span groups state)) :
    out.getReg reg=state.getReg reg := by
  induction groups generalizing state with
  | zero =>
    simp only [l21Groups,support_pure,Set.mem_singleton_iff] at reached
    subst out; rfl
  | succ groups ih =>
    simp only [l21Groups,mem_support_bind_iff] at reached
    obtain ⟨body,path,tail⟩ := reached
    have rest := ih _ tail
    rw [MachineState.getReg_setPC] at rest
    exact rest.trans (l21_trace_keeps_register _ _ _ reg keptSource keptTarget path)

theorem counted_l21_trace (oracle : Oracle) (state : MachineState) (remaining count : Nat) :
    RunPublic oracle (l21Trace remaining count state) count := by
  induction count generalizing state with
  | zero => exact run_pure_public oracle state
  | succ count ih =>
    rw [l21Trace]
    simpa only [Nat.add_comm 1 count] using
      (run_bind_public oracle (liftM (World.query (.inr (.inl (l21Input state (remaining+(count+1)))))) :
        OracleComp World (BitVec 256))
        (fun answer => l21Trace remaining count (l21After state (remaining+(count+1)) answer))
        1 count (run_query_public ..) (fun _ => ih _))

theorem counted_l21_groups (oracle : Oracle) (base : Word) (span groups : Nat)
    (state : MachineState) :
    RunPublic oracle (l21Groups base span groups state) (span*groups) := by
  induction groups generalizing state with
  | zero => exact run_pure_public oracle state
  | succ groups ih =>
    rw [l21Groups, show span*(groups+1)=span+span*groups by rw [Nat.mul_succ,Nat.add_comm]]
    exact run_bind_public oracle _ _ span (span*groups) (counted_l21_trace ..) (fun out => ih _)

end TwoPermutationPrototype.Grouped
