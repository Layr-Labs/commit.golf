import CommitGolfCandidate.TwoPermutationPackedLeafFetch

namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
attribute [local irreducible] execute packedWideCommitImage

def packed_wideFinishReady (state : MachineState) : MachineState :=
  execInstrBr (execInstrBr state (.SLLI .x7 .x13 11)) (.ADDI .x10 .x10 40)

def packed_wideReadyState (state : MachineState) {bits : Nat} (coins : BitVec bits) : MachineState :=
  packed_wideFinishReady (readyState state coins)

private theorem packed_wide_finish_register (state : MachineState) (reg : Reg)
    (kept : reg ∉ [Reg.x7,.x10]) :
    (packed_wideFinishReady state).getReg reg=state.getReg reg := by
  cases reg <;> first | rfl | simp at kept

theorem packed_wide_ready_state_register (state : MachineState) {bits : Nat} (coins : BitVec bits) (reg : Reg)
    (kept : reg ∉ [Reg.x7,.x10]) :
    (packed_wideReadyState state coins).getReg reg=(readyState state coins).getReg reg :=
  packed_wide_finish_register (readyState state coins) reg kept

private theorem packed_wide_finish_memory (state : MachineState) :
    (packed_wideFinishReady state).mem=state.mem := rfl

theorem packed_wide_ready_state_memory (state : MachineState) {bits : Nat} (coins : BitVec bits) :
    (packed_wideReadyState state coins).mem=(readyState state coins).mem :=
  packed_wide_finish_memory (readyState state coins)

theorem packed_wide_ready_source (state : MachineState) {bits : Nat} (coins : BitVec bits) :
    (packed_wideReadyState state coins).getReg .x10=(readyState state coins).getReg .x10+40 := rfl

theorem packed_wide_ready_state_entry (state : MachineState) (entry : CommitEntry state)
    {bits : Nat} (coins : BitVec bits) :
    (packed_wideReadyState state coins).pc=4168 ∧ (packed_wideReadyState state coins).getReg .x7=2048 := by
  have old := (post_random_regs state entry coins).1.pc
  constructor
  · change (readyState state coins).pc+4+4=_
    rw [old]
    rfl
  · change ((readyState state coins).getReg .x13 <<< (11 : Nat)) = _
    rw [(post_random_regs state entry coins).1.primitive]
    rfl

theorem packed_execute_wide_parent_setup (state : MachineState) (atSetup : state.pc=184736) (fuel : Nat) :
    execute packedWideCommitImage (5+fuel) state true =
      (do let out ← execute packedWideCommitImage fuel (parentSetup state 5) true
          return out.charge 5 0) := by
  apply CommitGolfCandidate.execute_unit_steps (states := parentSetup state)
  intro i inside
  refine ⟨.base ((parentSetupOps[i]?).getD .EBREAK),?_,?_,?_⟩
  · have pc : (parentSetup state i).pc=BitVec.ofNat 64 (4096+4*(45160+i)) := by
      interval_cases i <;>
        simp only [parentSetup,parentSetupOps,List.take,List.foldl,execInstrBr,MachineState.setPC,atSetup] <;> rfl
    exact packed_wide_fetch_parent_setup ⟨i,inside⟩ (parentSetup state i) pc
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem packed_wide_parent_setup_ready (state : MachineState) (atSetup : state.pc=184736)
    (selector : state.getReg .x5=0) (heap : state.getReg .x9=4294971424)
    (stride : state.getReg .x19=536870912)
    (stop : state.getReg .x21=wordAddress (leafDest (2^24))) :
    ParentRegs (parentSetup state 5) (2^24-1) ∧ (parentSetup state 5).pc=184756 ∧
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
