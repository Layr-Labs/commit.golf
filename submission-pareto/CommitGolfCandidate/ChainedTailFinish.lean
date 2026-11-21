import CommitGolfCandidate.ChainedTailEmitFrame

/-! Emit the final partial byte, but write nothing for an empty remainder. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
attribute [local irreducible] execute

def tailFinishOps : List Instr := [.BEQ .x25 .x0 12,.SB .x20 .x23 0,.ADDI .x20 .x20 1]
def tailFinishWords : List (BitVec 32) := [0x000c8663,0x017a0023,0x001a0a13]
def tailFinishImage : Image := ⟨tailFinishWords,[]⟩
def tailFinishOp (index : Nat) : Instr := (tailFinishOps[index]?).getD .EBREAK

theorem tail_finish_decode : ∀ i : Fin 3,
    (tailFinishWords[i.val]?).bind decodeInstruction = some (.base (tailFinishOp i.val)) := by
  intro i
  fin_cases i <;> rfl

def TailFinishAt (image : Image) (base : Word) : Prop :=
  ∀ i : Fin 3, ∀ s : MachineState, s.pc = base+BitVec.ofNat 64 (4*i.val) →
    fetch image s = some (.base (tailFinishOp i.val))

theorem tail_finish_at : TailFinishAt tailFinishImage 4096 := by
  intro i s pc
  apply cap_image_fetch tailFinishImage s i.val _ (by have := i.isLt; omega)
  · change s.pc = BitVec.ofNat 64 4096+BitVec.ofNat 64 (4*i.val) at pc
    rw [←BitVec.ofNat_add] at pc
    exact pc
  · exact tail_finish_decode i

def tailEmpty (s : MachineState) : Bool := s.getReg .x25 == 0
def tailFinishGuard (s : MachineState) : MachineState := execInstrBr s (.BEQ .x25 .x0 12)

theorem tail_finish_guard_pc (s : MachineState) :
    (tailFinishGuard s).pc = if tailEmpty s then s.pc+12 else s.pc+4 := by
  change (if tailEmpty s then s.setPC (s.pc+12) else s.setPC (s.pc+4)).pc = _
  split <;> rfl

theorem tail_finish_guard_register (s : MachineState) (reg : Reg) :
    (tailFinishGuard s).getReg reg = s.getReg reg := by
  by_cases empty : tailEmpty s
  · have same : tailFinishGuard s = s.setPC (s.pc+12) := ite_eq_left empty
    exact (congrArg (fun st : MachineState => st.getReg reg) same).trans MachineState.getReg_setPC
  · have same : tailFinishGuard s = s.setPC (s.pc+4) := ite_eq_right empty
    exact (congrArg (fun st : MachineState => st.getReg reg) same).trans MachineState.getReg_setPC

theorem tail_finish_guard_memory (s : MachineState) (query : Word) :
    (tailFinishGuard s).getMem query = s.getMem query := by
  by_cases empty : tailEmpty s
  · have same : tailFinishGuard s = s.setPC (s.pc+12) := ite_eq_left empty
    exact (congrArg (fun st : MachineState => st.getMem query) same).trans MachineState.getMem_setPC
  · have same : tailFinishGuard s = s.setPC (s.pc+4) := ite_eq_right empty
    exact (congrArg (fun st : MachineState => st.getMem query) same).trans MachineState.getMem_setPC

theorem tail_finish_write_execution (image : Image) (base : Word) (code : TailFinishAt image base)
    (s : MachineState) (pc : s.pc = base+4) (valid : accessValid (s.getReg .x20) 1 = true)
    (fuel : Nat) (coins : Bool) :
    execute image (2+fuel) s coins =
      (do let result ← execute image fuel (tailFlushPrefix s 2) coins
          return result.charge 2 0) := by
  apply execute_unit_steps (states := tailFlushPrefix s)
  intro i inside
  refine ⟨.base (tailFlushOp i),?_,?_,?_⟩
  · have op : tailFinishOp (1+i) = tailFlushOp i := by interval_cases i <;> rfl
    have location : (tailFlushPrefix s i).pc = base+BitVec.ofNat 64 (4*(1+i)) := by
      rw [tail_flush_pc s i (by omega),pc,Nat.mul_add,BitVec.ofNat_add,BitVec.add_assoc]
      rfl
    simpa only [op] using code ⟨1+i,by omega⟩ _ location
  · interval_cases i
    · simpa [ordinaryStep,memoryArgumentsValid,memAccess,tailFlushPrefix,tailFlushOp,tailFlushOps,signExtend12] using valid
    · rfl
  · interval_cases i <;> rfl

def tailFinishState (s : MachineState) : MachineState :=
  if tailEmpty s then tailFinishGuard s else tailFlushPrefix (tailFinishGuard s) 2

def tailFinishCycles (s : MachineState) : Nat := if tailEmpty s then 1 else 3

theorem tail_finish_execution (image : Image) (base : Word) (code : TailFinishAt image base)
    (s : MachineState) (pc : s.pc = base)
    (valid : ¬tailEmpty s → accessValid (s.getReg .x20) 1 = true) (fuel : Nat) (coins : Bool) :
    execute image (tailFinishCycles s+fuel) s coins =
      (do let result ← execute image fuel (tailFinishState s) coins
          return result.charge (tailFinishCycles s) 0) := by
  have fetched : fetch image s = some (.base (.BEQ .x25 .x0 12)) := by
    apply code ⟨0,by decide⟩
    simpa using pc
  have ordinary : ordinaryStep s (.base (.BEQ .x25 .x0 12)) = some (tailFinishGuard s) := rfl
  by_cases empty : tailEmpty s
  · rw [tailFinishCycles,ite_eq_left empty,show 1+fuel = fuel+1 by omega,
      execute_ordinary_step image _ _ _ fuel coins fetched ordinary]
    simp [tailFinishState,empty,Execution.charge,instructionCycles]
  · have nextPc : (tailFinishGuard s).pc = base+4 := by rw [tail_finish_guard_pc,ite_eq_right empty,pc]
    have access : accessValid ((tailFinishGuard s).getReg .x20) 1 = true := by
      rw [tail_finish_guard_register]
      exact valid empty
    rw [tailFinishCycles,ite_eq_right empty,show 3+fuel = (2+fuel)+1 by omega,
      execute_ordinary_step image _ _ _ (2+fuel) coins fetched ordinary,
      tail_finish_write_execution image base code _ nextPc access]
    simp [tailFinishState,empty,Execution.charge,instructionCycles,Nat.add_left_comm,Nat.add_comm]

theorem tail_finish_end_pc (s : MachineState) : (tailFinishState s).pc = s.pc+12 := by
  unfold tailFinishState
  split
  · rw [tail_finish_guard_pc,ite_eq_left (by assumption)]
  · rw [tail_flush_pc _ 2 (by decide),tail_finish_guard_pc,ite_eq_right (by assumption),BitVec.add_assoc]
    rfl

theorem tail_finish_byte (s : MachineState) (query : Word) : (tailFinishState s).getByte query =
    if tailEmpty s then s.getByte query
    else if query = s.getReg .x20 then (s.getReg .x23).setWidth 8 else s.getByte query := by
  have guard (q : Word) : (tailFinishGuard s).getByte q = s.getByte q := by
    simp only [MachineState.getByte,tail_finish_guard_memory]
  unfold tailFinishState
  split
  · exact guard query
  · change (tailFlushPrefix (tailFinishGuard s) 4).getByte query = _
    rw [tail_flush_byte,tail_finish_guard_register,tail_finish_guard_register,guard]

theorem tail_finish_pointer (s : MachineState) : (tailFinishState s).getReg .x20 =
    if tailEmpty s then s.getReg .x20 else s.getReg .x20+1 := by
  unfold tailFinishState
  split
  · exact tail_finish_guard_register s .x20
  · change (tailFlushPrefix (tailFinishGuard s) 4).getReg .x20 = _
    rw [tail_flush_pointer,tail_finish_guard_register]

theorem tail_finish_frame (s : MachineState) (reg : Reg) (pointer : reg ≠ .x20) :
    (tailFinishState s).getReg reg = s.getReg reg := by
  have writes (st : MachineState) : (tailFlushPrefix st 2).getReg reg = st.getReg reg := by
    cases reg <;> first | contradiction | rfl
  unfold tailFinishState
  split
  · exact tail_finish_guard_register s reg
  · rw [writes,tail_finish_guard_register]

theorem tail_partial_canonical (buffer bits : Nat) (bounded : buffer < 2^bits) :
    (BitVec.ofNat 64 buffer |>.setWidth 8).toNat < 2^bits := by
  rw [BitVec.setWidth_ofNat_of_le (by decide),BitVec.toNat_ofNat]
  exact lt_of_le_of_lt (Nat.mod_le _ _) bounded

end CommitGolfCandidate.Chained.Native
