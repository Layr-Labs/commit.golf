import CommitGolfCandidate.TwoPermutationWideLeafFetch

namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
attribute [local irreducible] execute wideCommitImage

def wideFinishReady (state : MachineState) : MachineState :=
  execInstrBr (execInstrBr state (.LUI .x7 1)) (.ADDI .x7 .x7 2048)

def wideBeforeEntry (state : MachineState) {bits : Nat} (coins : BitVec bits) : MachineState :=
  wideFinishReady (readyState state coins)

private def wideFinishOps : List Instr :=
  readyInstructions ++ [.LUI .x7 1,.ADDI .x7 .x7 2048]

private def wideReadyPrefix (state : MachineState) (i : Nat) : MachineState :=
  (wideFinishOps.take i).foldl execInstrBr state

private theorem wide_initial_run (state : MachineState) (atEntry : state.pc=4096) (fuel : Nat) :
    execute wideCommitImage (11+fuel) state true =
      (do let out ← execute wideCommitImage fuel (initialPrefix state 11) true
          return out.charge 11 0) := by
  apply CommitGolfCandidate.execute_unit_steps (states := initialPrefix state)
  intro i inside
  refine ⟨.base ((initialInstructions[i]?).getD .EBREAK),?_,?_,?_⟩
  · have pc : (initialPrefix state i).pc=BitVec.ofNat 64 (4096+4*i) := by
      interval_cases i <;>
        simp only [initialPrefix,initialInstructions,List.take,List.foldl,execInstrBr,MachineState.setPC,atEntry] <;> rfl
    have fetched := wide_fetch_initial ⟨i,by omega⟩ (initialPrefix state i) pc
    interval_cases i <;> exact fetched
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

private theorem wide_draw_run (state : MachineState) (pc : state.pc=4140) (r : SetupRegisters state)
    (fuel : Nat) :
    execute wideCommitImage (1+fuel) state true =
      (do let answer ← liftM ($ᵗ BitVec (8*(state.getReg .x11).toNat) : ProbComp (BitVec (8*(state.getReg .x11).toNat)))
          let out ← execute wideCommitImage fuel (writeBits state (wordAddress (leafSalt 0)) answer) true
          return out.charge 33554433 0) := by
  have fetched : fetch wideCommitImage state=some (.base .ECALL) :=
    wide_fetch_initial ⟨11,by decide⟩ state pc
  have valid : randomArgumentsValid state=true := by rw [randomArgumentsValid,r.target,r.size]; decide
  have cost : 1+((state.getReg .x11).toNat+7)/8=33554433 := by rw [r.size]; rfl
  rw [Nat.add_comm 1 fuel,execute,fetched]
  simp only [r.selector,valid,r.target,cost]
  rfl

private theorem wide_ready_run (state : MachineState) (atReady : state.pc=4144) (fuel : Nat) :
    execute wideCommitImage (6+fuel) state true =
      (do let out ← execute wideCommitImage fuel (wideFinishReady (readyPrefix state 4)) true
          return out.charge 6 0) := by
  have endState : wideReadyPrefix state 6 = wideFinishReady (readyPrefix state 4) := rfl
  rw [←endState]
  apply CommitGolfCandidate.execute_unit_steps (states := wideReadyPrefix state)
  intro i inside
  refine ⟨.base ((wideFinishOps[i]?).getD .EBREAK),?_,?_,?_⟩
  · have pc : (wideReadyPrefix state i).pc=BitVec.ofNat 64 (4096+4*(12+i)) := by
      interval_cases i <;>
        simp only [wideReadyPrefix,wideFinishOps,readyInstructions,List.cons_append,List.nil_append,List.take,List.foldl,
          execInstrBr,MachineState.setPC,atReady] <;> rfl
    have fetched := wide_fetch_initial ⟨12+i,by omega⟩ (wideReadyPrefix state i) pc
    interval_cases i <;> exact fetched
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem execute_wide_before_setup (state : MachineState) (entry : CommitEntry state) (fuel : Nat) :
    execute wideCommitImage (18+fuel) state true =
      (do let answer ← liftM ($ᵗ BitVec (8*((initialPrefix state 11).getReg .x11).toNat) :
            ProbComp (BitVec (8*((initialPrefix state 11).getReg .x11).toNat)))
          let out ← execute wideCommitImage fuel (wideBeforeEntry state answer) true
          return out.charge 33554450 0) := by
  rw [show 18+fuel=11+(1+(6+fuel)) by omega,wide_initial_run state entry.pc,
    wide_draw_run _ (setup_pc state entry.pc) (setup_registers state entry)]
  simp only [bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro answer _
  have pc : (writeBits (initialPrefix state 11) (wordAddress (leafSalt 0)) answer).pc=4144 := by
    rw [written_pc,setup_pc state entry.pc]
    rfl
  rw [wide_ready_run _ pc]
  simp [Execution.charge,←Nat.add_assoc,wideBeforeEntry,readyState]

private theorem wide_finish_register (state : MachineState) (reg : Reg)
    (kept : reg≠.x7) :
    (wideFinishReady state).getReg reg=state.getReg reg := by
  cases reg <;> first | exact False.elim (kept rfl) | rfl

theorem wide_before_state_register (state : MachineState) {bits : Nat} (coins : BitVec bits) (reg : Reg)
    (kept : reg≠.x7) :
    (wideBeforeEntry state coins).getReg reg=(readyState state coins).getReg reg :=
  wide_finish_register (readyState state coins) reg kept

private theorem wide_finish_memory (state : MachineState) :
    (wideFinishReady state).mem=state.mem := rfl

theorem wide_before_state_memory (state : MachineState) {bits : Nat} (coins : BitVec bits) :
    (wideBeforeEntry state coins).mem=(readyState state coins).mem :=
  wide_finish_memory (readyState state coins)

private theorem wide_finish_nonce_stride (state : MachineState) :
    (wideFinishReady state).getReg .x7=2048 := by
  have nonzero : Reg.x7≠.x0 := by decide
  simp only [wideFinishReady,execInstrBr,MachineState.getReg_setPC,MachineState.getReg_setReg_eq nonzero] <;> decide

theorem wide_before_state_entry (state : MachineState) (entry : CommitEntry state)
    {bits : Nat} (coins : BitVec bits) :
    (wideBeforeEntry state coins).pc=4168 ∧ (wideBeforeEntry state coins).getReg .x7=2048 := by
  have old := (post_random_regs state entry coins).1.pc
  constructor
  · change (readyState state coins).pc+4+4=_
    rw [old]
    rfl
  · exact wide_finish_nonce_stride (readyState state coins)

def wideReadyState (initial : MachineState) {bits : Nat} (coins : BitVec bits) : MachineState :=
  let s := wideBeforeEntry initial coins
  (s.setReg .x10 (s.getReg .x10+32)).setPC 6216

theorem wide_cursor_entry_run (s : MachineState) (pc : s.pc=4168) (fuel : Nat) :
    execute wideCommitImage (2+fuel) s true =
      (do let out ← execute wideCommitImage fuel ((s.setReg .x10 (s.getReg .x10+32)).setPC 6216) true
          return out.charge 2 0) := by
  let mid := execInstrBr s (.ADDI .x10 .x10 32)
  have mp : mid.pc=4172 := by change s.pc+4=_; rw [pc]; rfl
  have last : execInstrBr mid (.JAL .x0 2044) = (s.setReg .x10 (s.getReg .x10+32)).setPC 6216 := by
    simp [mid,execInstrBr,MachineState.setReg,MachineState.setPC,MachineState.getReg,pc,signExtend12,signExtend21]
  rw [show 2+fuel=(fuel+1)+1 by omega, CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _
    (wide_fetch_cursor_adjust s pc) rfl]
  change (do let r ← execute _ (fuel+1) mid true; return r.charge 1 0) = _
  rw [CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (wide_fetch_group_entry mid mp) rfl,last]
  simp [instructionCycles,bind_assoc,Execution.charge,←Nat.add_assoc]

theorem execute_wide_setup (initial : MachineState) (e : CommitEntry initial) (fuel : Nat) :
    execute wideCommitImage (20+fuel) initial true =
      (do let answer ← liftM ($ᵗ BitVec (8*((initialPrefix initial 11).getReg .x11).toNat) :
            ProbComp (BitVec (8*((initialPrefix initial 11).getReg .x11).toNat)))
          let out ← execute wideCommitImage fuel (wideReadyState initial answer) true
          return out.charge 33554452 0) := by
  rw [show 20+fuel=18+(2+fuel) by omega,execute_wide_before_setup initial e]
  apply bind_congr_of_forall_mem_support
  intro coins _
  rw [wide_cursor_entry_run _ (wide_before_state_entry initial e coins).1]
  simp [wideReadyState,Execution.charge,bind_assoc,←Nat.add_assoc]

theorem wide_ready_state_register (s : MachineState) {n : Nat} (c : BitVec n) (r : Reg)
    (keep : r≠.x7) (cursor : r≠.x10 := by decide) :
    (wideReadyState s c).getReg r = (readyState s c).getReg r := by
  rw [wideReadyState,MachineState.getReg_setPC,MachineState.getReg_setReg_ne _ _ _ _ cursor.symm]
  exact wide_before_state_register _ _ _ keep

theorem wide_ready_cursor (s : MachineState) {n : Nat} (c : BitVec n) :
    (wideReadyState s c).getReg .x10 = (readyState s c).getReg .x10 + 32 := by
  rw [wideReadyState,MachineState.getReg_setPC, MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0),
    wide_before_state_register s c .x10 (by decide)]

private theorem adjust_mem (s : MachineState) : ((s.setReg .x10 (s.getReg .x10+32)).setPC 6216).mem = s.mem := rfl

theorem wide_ready_state_memory (s : MachineState) {n : Nat} (c : BitVec n) :
    (wideReadyState s c).mem=(readyState s c).mem := by
  rw [wideReadyState,adjust_mem,wide_before_state_memory]

theorem wide_ready_state_entry (s : MachineState) (e : CommitEntry s) {n : Nat} (c : BitVec n) :
    (wideReadyState s c).pc=6216 ∧ (wideReadyState s c).getReg .x7=2048 := by
  refine ⟨rfl,?_⟩
  rw [wideReadyState,MachineState.getReg_setPC,MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x10 ≠ .x7)]
  exact (wide_before_state_entry _ e _).2

theorem execute_wide_parent_setup (state : MachineState) (atSetup : state.pc=18536) (fuel : Nat) :
    execute wideCommitImage (5+fuel) state true =
      (do let out ← execute wideCommitImage fuel (parentSetup state 5) true
          return out.charge 5 0) := by
  apply CommitGolfCandidate.execute_unit_steps (states := parentSetup state)
  intro i inside
  refine ⟨.base ((parentSetupOps[i]?).getD .EBREAK),?_,?_,?_⟩
  · have pc : (parentSetup state i).pc=BitVec.ofNat 64 (4096+4*(3610+i)) := by
      interval_cases i <;>
        simp only [parentSetup,parentSetupOps,List.take,List.foldl,execInstrBr,MachineState.setPC,atSetup] <;> rfl
    exact wide_fetch_parent_setup ⟨i,inside⟩ (parentSetup state i) pc
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem wide_parent_setup_ready (state : MachineState) (atSetup : state.pc=18536)
    (selector : state.getReg .x5=0) (heap : state.getReg .x9=4294971424)
    (stride : state.getReg .x19=536870912)
    (stop : state.getReg .x21=wordAddress (leafDest (2^24))) :
    ParentRegs (parentSetup state 5) (2^24-1) ∧ (parentSetup state 5).pc=18556 ∧
      (parentSetup state 5).getReg .x8=state.getReg .x8 := by
  refine ⟨⟨?_,?_,selector,rfl,rfl,heap⟩,?_,rfl⟩
  · change state.getReg .x21+signExtend12 4032=_
    rw [stop]
    rfl
  · change state.getReg .x21-state.getReg .x19+signExtend12 4064=_
    rw [stop,stride]
    rfl
  · change state.pc+4+4+4+4+4=_
    rw [atSetup]
    rfl

end TwoPermutationPrototype.RV64
