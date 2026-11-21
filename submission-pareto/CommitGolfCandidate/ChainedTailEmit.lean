import CommitGolfCandidate.ChainedTailFlush

/-! Append a field and flush at most one complete byte, with an actual native guard. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
attribute [local irreducible] execute

def tailEmitOps : List Instr := tailAppendOps ++ [.BLTU .x25 .x27 20] ++ tailFlushOps
def tailEmitWords : List (BitVec 32) := tailAppendWords ++ [0x01bcea63] ++ tailFlushWords
def tailEmitImage : Image := ⟨tailEmitWords,[]⟩
def tailEmitOp (index : Nat) : Instr := (tailEmitOps[index]?).getD .EBREAK

theorem tail_emit_decode : ∀ i : Fin 8,
    (tailEmitWords[i.val]?).bind decodeInstruction = some (.base (tailEmitOp i.val)) := by
  intro i
  fin_cases i <;> rfl

def TailEmitAt (image : Image) (base : Word) : Prop :=
  ∀ i : Fin 8, ∀ s : MachineState, s.pc = base+BitVec.ofNat 64 (4*i.val) →
    fetch image s = some (.base (tailEmitOp i.val))

theorem tail_emit_at : TailEmitAt tailEmitImage 4096 := by
  intro i s pc
  apply cap_image_fetch tailEmitImage s i.val _ (by have := i.isLt; omega)
  · change s.pc = BitVec.ofNat 64 4096+BitVec.ofNat 64 (4*i.val) at pc
    rw [←BitVec.ofNat_add] at pc
    exact pc
  · exact tail_emit_decode i

theorem TailEmitAt.append {image : Image} {base : Word} (code : TailEmitAt image base) : TailAppendAt image base := by
  intro i s pc
  have op : tailEmitOp i.val = tailAppendOp i.val := by fin_cases i <;> rfl
  simpa only [op] using code ⟨i.val,by have := i.isLt; omega⟩ s pc

theorem TailEmitAt.flush {image : Image} {base : Word} (code : TailEmitAt image base) : TailFlushAt image (base+16) := by
  intro i s pc
  have op : tailEmitOp (4+i.val) = tailFlushOp i.val := by fin_cases i <;> rfl
  have location : s.pc = base+BitVec.ofNat 64 (4*(4+i.val)) := by
    rw [pc,Nat.mul_add,BitVec.ofNat_add,BitVec.add_assoc]
    rfl
  simpa only [op] using code ⟨4+i.val,by have := i.isLt; omega⟩ s location

def tailGuard (s : MachineState) : MachineState := execInstrBr s (.BLTU .x25 .x27 20)
def tailSkips (s : MachineState) : Bool := BitVec.ult (s.getReg .x25) (s.getReg .x27)

theorem tail_guard_pc (s : MachineState) :
    (tailGuard s).pc = if tailSkips s then s.pc+20 else s.pc+4 := by
  change (if tailSkips s then s.setPC (s.pc+20) else s.setPC (s.pc+4)).pc = _
  split <;> rfl

theorem tail_guard_register (s : MachineState) (reg : Reg) : (tailGuard s).getReg reg = s.getReg reg := by
  by_cases skip : tailSkips s
  · have same : tailGuard s = s.setPC (s.pc+20) := ite_eq_left skip
    exact (congrArg (fun st : MachineState => st.getReg reg) same).trans MachineState.getReg_setPC
  · have same : tailGuard s = s.setPC (s.pc+4) := ite_eq_right skip
    exact (congrArg (fun st : MachineState => st.getReg reg) same).trans MachineState.getReg_setPC

theorem tail_guard_memory (s : MachineState) (query : Word) : (tailGuard s).getMem query = s.getMem query := by
  by_cases skip : tailSkips s
  · have same : tailGuard s = s.setPC (s.pc+20) := ite_eq_left skip
    exact (congrArg (fun st : MachineState => st.getMem query) same).trans MachineState.getMem_setPC
  · have same : tailGuard s = s.setPC (s.pc+4) := ite_eq_right skip
    exact (congrArg (fun st : MachineState => st.getMem query) same).trans MachineState.getMem_setPC

def tailEmitState (s : MachineState) : MachineState :=
  let appended := tailAppendPrefix s 3
  if tailSkips appended then tailGuard appended else tailFlushPrefix (tailGuard appended) 4

def tailEmitCycles (s : MachineState) : Nat := if tailSkips (tailAppendPrefix s 3) then 4 else 8

theorem tail_emit_execution (image : Image) (base : Word) (code : TailEmitAt image base)
    (s : MachineState) (pc : s.pc = base)
    (valid : ¬tailSkips (tailAppendPrefix s 3) → accessValid (s.getReg .x20) 1 = true)
    (fuel : Nat) (coins : Bool) :
    execute image (tailEmitCycles s+fuel) s coins =
      (do let result ← execute image fuel (tailEmitState s) coins
          return result.charge (tailEmitCycles s) 0) := by
  have fetched : fetch image (tailAppendPrefix s 3) = some (.base (.BLTU .x25 .x27 20)) := by
    apply code ⟨3,by decide⟩
    rw [tail_append_pc s 3 (by decide),pc]
  have ordinary : ordinaryStep (tailAppendPrefix s 3) (.base (.BLTU .x25 .x27 20)) =
      some (tailGuard (tailAppendPrefix s 3)) := rfl
  by_cases skip : tailSkips (tailAppendPrefix s 3)
  · rw [tailEmitCycles,ite_eq_left skip,show 4+fuel = 3+(fuel+1) by omega,
      tail_append_execution image base code.append s pc,
      execute_ordinary_step image _ _ _ fuel coins fetched ordinary]
    simp [tailEmitState,skip,Execution.charge,instructionCycles,Nat.add_assoc,Nat.add_comm]
  · have nextPc : (tailGuard (tailAppendPrefix s 3)).pc = base+16 := by
      rw [tail_guard_pc,ite_eq_right skip,tail_append_pc s 3 (by decide),pc,BitVec.add_assoc]
      rfl
    have access : accessValid ((tailGuard (tailAppendPrefix s 3)).getReg .x20) 1 = true := by
      rw [tail_guard_register,tail_append_frame s .x20 (by decide) (by decide) (by decide)]
      exact valid skip
    rw [tailEmitCycles,ite_eq_right skip,show 8+fuel = 3+((4+fuel)+1) by omega,
      tail_append_execution image base code.append s pc,
      execute_ordinary_step image _ _ _ (4+fuel) coins fetched ordinary,
      tail_flush_execution image (base+16) code.flush _ nextPc access]
    simp [tailEmitState,skip,Execution.charge,instructionCycles,Nat.add_left_comm,Nat.add_comm]

theorem tail_emit_end_pc (s : MachineState) : (tailEmitState s).pc = s.pc+32 := by
  unfold tailEmitState
  dsimp only
  split
  · rw [tail_guard_pc,ite_eq_left (by assumption),tail_append_pc s 3 (by decide),BitVec.add_assoc]
    rfl
  · rw [tail_flush_pc _ 4 (by decide),tail_guard_pc,ite_eq_right (by assumption),
      tail_append_pc s 3 (by decide),BitVec.add_assoc,BitVec.add_assoc]
    rfl

end CommitGolfCandidate.Chained.Native
