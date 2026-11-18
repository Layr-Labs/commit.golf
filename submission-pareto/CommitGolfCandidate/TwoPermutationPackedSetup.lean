import CommitGolfCandidate.TwoPermutationPackedLeafFetch

/-! Prelude of the production commitment: the shared sixteen setup words, then seven words that
form the 4096-byte block advance in `x7`, shift the heap and nonce bases 2048 bytes into their
first blocks, and place the message end in `x28`. -/
namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
attribute [local irreducible] execute packedWideCommitImage

def packed_wideFinishReady (state : MachineState) : MachineState :=
  packed_wideFinishOps.foldl execInstrBr state

def packed_wideReadyState (state : MachineState) {bits : Nat} (coins : BitVec bits) : MachineState :=
  packed_wideFinishReady (readyState state coins)

private def packed_wideTailOps : List Instr :=
  readyInstructions ++ packed_wideFinishOps

private def packed_wideReadyPrefix (state : MachineState) (i : Nat) : MachineState :=
  (packed_wideTailOps.take i).foldl execInstrBr state

private theorem packed_wide_initial_run (state : MachineState) (atEntry : state.pc=4096) (fuel : Nat) :
    execute packedWideCommitImage (11+fuel) state true =
      (do let out ← execute packedWideCommitImage fuel (initialPrefix state 11) true
          return out.charge 11 0) := by
  apply CommitGolfCandidate.execute_unit_steps (states := initialPrefix state)
  intro i inside
  refine ⟨.base ((initialInstructions[i]?).getD .EBREAK),?_,?_,?_⟩
  · have pc : (initialPrefix state i).pc=BitVec.ofNat 64 (4096+4*i) := by
      interval_cases i <;>
        simp only [initialPrefix,initialInstructions,List.take,List.foldl,execInstrBr,MachineState.setPC,atEntry] <;> rfl
    have fetched := packed_wide_fetch_initial ⟨i,by omega⟩ (initialPrefix state i) pc
    interval_cases i <;> exact fetched
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

private theorem packed_wide_draw_run (state : MachineState) (pc : state.pc=4140) (r : SetupRegisters state)
    (fuel : Nat) :
    execute packedWideCommitImage (1+fuel) state true =
      (do let answer ← liftM ($ᵗ BitVec (8*(state.getReg .x11).toNat) : ProbComp (BitVec (8*(state.getReg .x11).toNat)))
          let out ← execute packedWideCommitImage fuel (writeBits state (wordAddress (leafSalt 0)) answer) true
          return out.charge 33554433 0) := by
  have fetched : fetch packedWideCommitImage state=some (.base .ECALL) :=
    packed_wide_fetch_initial ⟨11,by decide⟩ state pc
  have valid : randomArgumentsValid state=true := by rw [randomArgumentsValid,r.target,r.size]; decide
  have cost : 1+((state.getReg .x11).toNat+7)/8=33554433 := by rw [r.size]; rfl
  rw [Nat.add_comm 1 fuel,execute,fetched]
  simp only [r.selector,valid,r.target,cost]
  rfl

private theorem tail_end (state : MachineState) :
    packed_wideReadyPrefix state 11 = packed_wideFinishReady (readyPrefix state 4) := by
  simp only [packed_wideReadyPrefix,packed_wideTailOps,packed_wideFinishReady,readyPrefix,readyInstructions,
    packed_wideFinishOps,List.take_succ_cons,List.take_zero,List.cons_append,List.nil_append,
    List.foldl_cons,List.foldl_nil]

private theorem packed_wide_ready_run (state : MachineState) (atReady : state.pc=4144) (fuel : Nat) :
    execute packedWideCommitImage (11+fuel) state true =
      (do let out ← execute packedWideCommitImage fuel (packed_wideFinishReady (readyPrefix state 4)) true
          return out.charge 11 0) := by
  rw [←tail_end]
  apply CommitGolfCandidate.execute_unit_steps (states := packed_wideReadyPrefix state)
  intro i inside
  refine ⟨.base ((packed_wideTailOps[i]?).getD .EBREAK),?_,?_,?_⟩
  · have pc : (packed_wideReadyPrefix state i).pc=BitVec.ofNat 64 (4096+4*(12+i)) := by
      interval_cases i <;>
        simp only [packed_wideReadyPrefix,packed_wideTailOps,packed_wideFinishOps,readyInstructions,List.cons_append,List.nil_append,List.take,List.foldl,
          execInstrBr,MachineState.setPC,atReady] <;> rfl
    have fetched := packed_wide_fetch_initial ⟨12+i,by omega⟩ (packed_wideReadyPrefix state i) pc
    interval_cases i <;> exact fetched
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem packed_execute_wide_setup (state : MachineState) (entry : CommitEntry state) (fuel : Nat) :
    execute packedWideCommitImage (23+fuel) state true =
      (do let answer ← liftM ($ᵗ BitVec (8*((initialPrefix state 11).getReg .x11).toNat) :
            ProbComp (BitVec (8*((initialPrefix state 11).getReg .x11).toNat)))
          let out ← execute packedWideCommitImage fuel (packed_wideReadyState state answer) true
          return out.charge 33554455 0) := by
  rw [show 23+fuel=11+(1+(11+fuel)) by omega,packed_wide_initial_run state entry.pc,
    packed_wide_draw_run _ (setup_pc state entry.pc) (setup_registers state entry)]
  simp only [bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro answer _
  have pc : (writeBits (initialPrefix state 11) (wordAddress (leafSalt 0)) answer).pc=4144 := by
    rw [written_pc,setup_pc state entry.pc]
    rfl
  rw [packed_wide_ready_run _ pc]
  simp [Execution.charge,←Nat.add_assoc,packed_wideReadyState,readyState]

private theorem shamt11 : ((11 : BitVec 6)).toNat = 11 := rfl
private theorem shamt1 : ((1 : BitVec 6)).toNat = 1 := rfl
private theorem shamt32 : ((32 : BitVec 6)).toNat = 32 := rfl
private theorem imm40 : signExtend12 (40 : BitVec 12) = (40 : Word) := by decide

/-- Register, pc and memory effect of the seven finishing words on an arbitrary state. -/
private theorem finish_effect (r : MachineState) :
    (packed_wideFinishReady r).getReg .x10 = r.getReg .x10 + 40 ∧
    (packed_wideFinishReady r).getReg .x20 = r.getReg .x20 + (r.getReg .x13 <<< (11:Nat)) ∧
    (packed_wideFinishReady r).getReg .x22 = r.getReg .x22 + (r.getReg .x13 <<< (11:Nat)) ∧
    (packed_wideFinishReady r).getReg .x7 = (r.getReg .x13 <<< (11:Nat)) <<< (1:Nat) ∧
    (packed_wideFinishReady r).getReg .x28 = (r.getReg .x13 <<< (32:Nat)) + (r.getReg .x10 + 40) ∧
    (packed_wideFinishReady r).pc = r.pc + 28 ∧
    (packed_wideFinishReady r).mem = r.mem ∧
    ∀ reg : Reg, reg ∉ [Reg.x7,.x10,.x20,.x22,.x28] → (packed_wideFinishReady r).getReg reg = r.getReg reg := by
  simp only [packed_wideFinishReady,packed_wideFinishOps,List.foldl_cons,List.foldl_nil,execInstrBr,
    shamt11,shamt1,shamt32,imm40]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals try intro reg kept
  all_goals try (simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at kept)
  all_goals try (cases reg)
  all_goals first
    | (exfalso; simp at kept; done)
    | (simp (config := {decide := true}) [MachineState.setPC,MachineState.setReg,MachineState.getReg,BitVec.add_assoc]; done)

theorem packed_wide_ready_state_register (state : MachineState) {bits : Nat} (coins : BitVec bits) (reg : Reg)
    (kept : reg ∉ [Reg.x7,.x10,.x20,.x22,.x28]) :
    (packed_wideReadyState state coins).getReg reg=(readyState state coins).getReg reg :=
  (finish_effect (readyState state coins)).2.2.2.2.2.2.2 reg kept

theorem packed_wide_ready_state_memory (state : MachineState) {bits : Nat} (coins : BitVec bits) :
    (packed_wideReadyState state coins).mem=(readyState state coins).mem :=
  (finish_effect (readyState state coins)).2.2.2.2.2.2.1

/-- Register values produced by the seven finishing words, in terms of the shared ready state. -/
theorem packed_wide_ready_shifted (state : MachineState) {bits : Nat} (coins : BitVec bits)
    (primitive : (readyState state coins).getReg .x13=1) :
    (packed_wideReadyState state coins).getReg .x10=(readyState state coins).getReg .x10+40 ∧
    (packed_wideReadyState state coins).getReg .x20=(readyState state coins).getReg .x20+2048 ∧
    (packed_wideReadyState state coins).getReg .x22=(readyState state coins).getReg .x22+2048 ∧
    (packed_wideReadyState state coins).getReg .x7=4096 ∧
    (packed_wideReadyState state coins).getReg .x28=4294967296+((readyState state coins).getReg .x10+40) ∧
    (packed_wideReadyState state coins).pc=(readyState state coins).pc+28 := by
  obtain ⟨a,b,c,d,e,f,_⟩ := finish_effect (readyState state coins)
  rw [primitive] at b c d e
  exact ⟨a,b,c,d,e,f⟩

theorem packed_wide_ready_source (state : MachineState) {bits : Nat} (coins : BitVec bits) :
    (packed_wideReadyState state coins).getReg .x10=(readyState state coins).getReg .x10+40 :=
  (finish_effect (readyState state coins)).1

theorem packed_wide_ready_state_entry (state : MachineState) (entry : CommitEntry state)
    {bits : Nat} (coins : BitVec bits) :
    (packed_wideReadyState state coins).pc=4188 ∧ (packed_wideReadyState state coins).getReg .x7=4096 := by
  obtain ⟨_,_,_,stride,_,pc⟩ := packed_wide_ready_shifted state coins (post_random_regs state entry coins).1.primitive
  refine ⟨?_,stride⟩
  rw [pc,(post_random_regs state entry coins).1.pc]
  rfl

theorem packed_execute_wide_parent_setup (state : MachineState) (atSetup : state.pc=184612) (fuel : Nat) :
    execute packedWideCommitImage (5+fuel) state true =
      (do let out ← execute packedWideCommitImage fuel (parentSetup state 5) true
          return out.charge 5 0) := by
  apply CommitGolfCandidate.execute_unit_steps (states := parentSetup state)
  intro i inside
  refine ⟨.base ((parentSetupOps[i]?).getD .EBREAK),?_,?_,?_⟩
  · have pc : (parentSetup state i).pc=BitVec.ofNat 64 (4096+4*(45129+i)) := by
      interval_cases i <;>
        simp only [parentSetup,parentSetupOps,List.take,List.foldl,execInstrBr,MachineState.setPC,atSetup] <;> rfl
    exact packed_wide_fetch_parent_setup ⟨i,inside⟩ (parentSetup state i) pc
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem packed_wide_parent_setup_ready (state : MachineState) (atSetup : state.pc=184612)
    (selector : state.getReg .x5=0) (heap : state.getReg .x9=4294971424)
    (stride : state.getReg .x19=536870912)
    (stop : state.getReg .x21=wordAddress (leafDest (2^24))) :
    ParentRegs (parentSetup state 5) (2^24-1) ∧ (parentSetup state 5).pc=184632 ∧
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
