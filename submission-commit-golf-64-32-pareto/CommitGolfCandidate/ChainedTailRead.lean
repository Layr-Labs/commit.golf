import CommitGolfCandidate.ChainedTailExtract

/-! Guarded inverse-field parsing, with exact native execution charges. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
attribute [local irreducible] execute

def tailNeedsByte (s : MachineState) : Bool := BitVec.ult (s.getReg .x25) (s.getReg .x26)
def tailReadGuard (s : MachineState) : MachineState := execInstrBr s (.BGEU .x25 .x26 24)

theorem tail_read_guard_pc (s : MachineState) :
    (tailReadGuard s).pc = if ¬tailNeedsByte s then s.pc+24 else s.pc+4 := by
  change (if ¬tailNeedsByte s then s.setPC (s.pc+24) else s.setPC (s.pc+4)).pc = _
  split <;> rfl

theorem tail_read_guard_register (s : MachineState) (reg : Reg) :
    (tailReadGuard s).getReg reg = s.getReg reg := by
  by_cases enough : ¬tailNeedsByte s
  · have same : tailReadGuard s = s.setPC (s.pc+24) := ite_eq_left enough
    exact (congrArg (fun st : MachineState => st.getReg reg) same).trans MachineState.getReg_setPC
  · have same : tailReadGuard s = s.setPC (s.pc+4) := ite_eq_right enough
    exact (congrArg (fun st : MachineState => st.getReg reg) same).trans MachineState.getReg_setPC

theorem tail_read_guard_memory (s : MachineState) (query : Word) :
    (tailReadGuard s).getMem query = s.getMem query := by
  by_cases enough : ¬tailNeedsByte s
  · have same : tailReadGuard s = s.setPC (s.pc+24) := ite_eq_left enough
    exact (congrArg (fun st : MachineState => st.getMem query) same).trans MachineState.getMem_setPC
  · have same : tailReadGuard s = s.setPC (s.pc+4) := ite_eq_right enough
    exact (congrArg (fun st : MachineState => st.getMem query) same).trans MachineState.getMem_setPC

def tailReadLoaded (s : MachineState) : MachineState :=
  if tailNeedsByte s then tailRefillPrefix (tailReadGuard s) 5 else tailReadGuard s
def tailReadState (s : MachineState) : MachineState := tailExtractPrefix (tailReadLoaded s) 6
def tailReadCycles (s : MachineState) : Nat := if tailNeedsByte s then 12 else 7

theorem tail_read_loaded_pc (s : MachineState) : (tailReadLoaded s).pc = s.pc+24 := by
  unfold tailReadLoaded
  split
  · rw [tail_refill_pc _ 5 (by decide),tail_read_guard_pc,ite_eq_right (by tauto),BitVec.add_assoc]
    rfl
  · rw [tail_read_guard_pc,ite_eq_left (by assumption)]

theorem tail_read_execution (image : Image) (base : Word) (code : TailReadAt image base)
    (s : MachineState) (pc : s.pc = base)
    (valid : tailNeedsByte s → accessValid (s.getReg .x20) 1 = true) (fuel : Nat) (coins : Bool) :
    execute image (tailReadCycles s+fuel) s coins =
      (do let result ← execute image fuel (tailReadState s) coins
          return result.charge (tailReadCycles s) 0) := by
  have fetched : fetch image s = some (.base (.BGEU .x25 .x26 24)) := by
    apply code ⟨0,by decide⟩
    simpa using pc
  have ordinary : ordinaryStep s (.base (.BGEU .x25 .x26 24)) = some (tailReadGuard s) := rfl
  have loaded : (tailReadLoaded s).pc = base+24 := by rw [tail_read_loaded_pc,pc]
  by_cases needs : tailNeedsByte s
  · have nextPc : (tailReadGuard s).pc = base+4 := by
      rw [tail_read_guard_pc,ite_eq_right (by tauto),pc]
    have access : accessValid ((tailReadGuard s).getReg .x20) 1 = true := by
      rw [tail_read_guard_register]
      exact valid needs
    have unpacked : (tailRefillPrefix (tailReadGuard s) 5).pc = base+24 := by
      simpa only [tailReadLoaded,ite_eq_left needs] using loaded
    rw [tailReadCycles,ite_eq_left needs,show 12+fuel = (5+(6+fuel))+1 by omega,
      execute_ordinary_step image _ _ _ (5+(6+fuel)) coins fetched ordinary,
      tail_refill_execution image base code _ nextPc access,
      tail_extract_execution image base code _ unpacked]
    simp [tailReadState,tailReadLoaded,needs,Execution.charge,instructionCycles,Nat.add_left_comm,Nat.add_comm]
  · have nextPc : (tailReadGuard s).pc = base+24 := by rw [tail_read_guard_pc,ite_eq_left needs,pc]
    rw [tailReadCycles,ite_eq_right needs,show 7+fuel = (6+fuel)+1 by omega,
      execute_ordinary_step image _ _ _ (6+fuel) coins fetched ordinary,
      tail_extract_execution image base code _ nextPc]
    simp [tailReadState,tailReadLoaded,needs,Execution.charge,instructionCycles,Nat.add_left_comm,Nat.add_comm]

theorem tail_read_end_pc (s : MachineState) : (tailReadState s).pc = s.pc+48 := by
  rw [tailReadState,tail_extract_pc _ 6 (by decide),tail_read_loaded_pc,BitVec.add_assoc]
  rfl

theorem tail_read_memory (s : MachineState) (query : Word) :
    (tailReadState s).getMem query = s.getMem query := by
  rw [tailReadState,tail_extract_memory]
  unfold tailReadLoaded
  split
  · rw [tail_refill_memory,tail_read_guard_memory]
  · exact tail_read_guard_memory s query

theorem tail_read_byte (s : MachineState) (query : Word) : (tailReadState s).getByte query = s.getByte query := by
  simp only [MachineState.getByte,tail_read_memory]

theorem tail_read_loaded_frame (s : MachineState) (reg : Reg) (pointer : reg ≠ .x20)
    (buffer : reg ≠ .x23) (value : reg ≠ .x24) (count : reg ≠ .x25) :
    (tailReadLoaded s).getReg reg = s.getReg reg := by
  unfold tailReadLoaded
  split
  · rw [tail_refill_frame _ reg pointer buffer value count,tail_read_guard_register]
  · exact tail_read_guard_register s reg

theorem tail_read_frame (s : MachineState) (reg : Reg) (pointer : reg ≠ .x20)
    (buffer : reg ≠ .x23) (value : reg ≠ .x24) (count : reg ≠ .x25) (mask : reg ≠ .x28) :
    (tailReadState s).getReg reg = s.getReg reg := by
  rw [tailReadState,tail_extract_frame _ reg buffer value count mask,
    tail_read_loaded_frame s reg pointer buffer value count]

end CommitGolfCandidate.Chained.Native
