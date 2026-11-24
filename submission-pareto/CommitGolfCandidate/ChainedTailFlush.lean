import CommitGolfCandidate.ChainedTailAppend
import CommitGolfCandidate.WriteMemory

/-! Flush one accumulated byte; the caller branches here only when at least eight bits are ready. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192

def tailFlushOps : List Instr :=
  [.SB .x20 .x23 0,.ADDI .x20 .x20 1,.SRLI .x23 .x23 8,.ADDI .x25 .x25 4088]
def tailFlushWords : List (BitVec 32) := [0x017a0023,0x001a0a13,0x008bdb93,0xff8c8c93]
def tailFlushImage : Image := ⟨tailFlushWords,[]⟩
def tailFlushOp (index : Nat) : Instr := (tailFlushOps[index]?).getD .EBREAK
def tailFlushPrefix (s : MachineState) (count : Nat) : MachineState :=
  (tailFlushOps.take count).foldl execInstrBr s

theorem tail_flush_decode : ∀ i : Fin 4,
    (tailFlushWords[i.val]?).bind decodeInstruction = some (.base (tailFlushOp i.val)) := by
  intro i
  fin_cases i <;> rfl

def TailFlushAt (image : Image) (base : Word) : Prop :=
  ∀ i : Fin 4, ∀ s : MachineState, s.pc = base+BitVec.ofNat 64 (4*i.val) →
    fetch image s = some (.base (tailFlushOp i.val))

theorem tail_flush_at : TailFlushAt tailFlushImage 4096 := by
  intro i s pc
  apply cap_image_fetch tailFlushImage s i.val _ (by have := i.isLt; omega)
  · change s.pc = BitVec.ofNat 64 4096+BitVec.ofNat 64 (4*i.val) at pc
    rw [←BitVec.ofNat_add] at pc
    exact pc
  · exact tail_flush_decode i

theorem tail_flush_byte (s : MachineState) (query : Word) :
    (tailFlushPrefix s 4).getByte query =
      if query = s.getReg .x20 then (s.getReg .x23).setWidth 8 else s.getByte query := by
  change (s.setByte (s.getReg .x20+0#64) ((s.getReg .x23).truncate 8)).getByte query = _
  rw [BitVec.add_zero,CommitGolfCandidate.set_byte_read]

theorem tail_flush_value (s : MachineState) :
    (tailFlushPrefix s 4).getReg .x23 = s.getReg .x23 >>> 8 := rfl

theorem tail_flush_pointer (s : MachineState) :
    (tailFlushPrefix s 4).getReg .x20 = s.getReg .x20+1 := rfl

theorem tail_flush_count (s : MachineState) :
    (tailFlushPrefix s 4).getReg .x25 = s.getReg .x25-8 := by
  change s.getReg .x25+signExtend12 4088 = s.getReg .x25-8
  rw [BitVec.sub_eq_add_neg]
  rfl

theorem tail_flush_frame (s : MachineState) (reg : Reg)
    (pointer : reg ≠ .x20) (value : reg ≠ .x23) (count : reg ≠ .x25) :
    (tailFlushPrefix s 4).getReg reg = s.getReg reg := by
  cases reg <;> first | contradiction | rfl

private theorem prefix_succ (s : MachineState) (count : Nat) (inside : count < 4) :
    tailFlushPrefix s (count+1) = execInstrBr (tailFlushPrefix s count) (tailFlushOp count) := by
  interval_cases count <;> rfl

theorem tail_flush_pc (s : MachineState) (count : Nat) (small : count ≤ 4) :
    (tailFlushPrefix s count).pc = s.pc+BitVec.ofNat 64 (4*count) := by
  induction count with
  | zero => simp [tailFlushPrefix]
  | succ count ih =>
    rw [prefix_succ s count (by omega)]
    have step : (execInstrBr (tailFlushPrefix s count) (tailFlushOp count)).pc =
        (tailFlushPrefix s count).pc+4 := by
      have inside : count < 4 := by omega
      interval_cases count <;> rfl
    rw [step,ih (by omega),BitVec.add_assoc]
    congr 1
    change BitVec.ofNat 64 (4*count)+BitVec.ofNat 64 4 = _
    rw [←BitVec.ofNat_add]
    congr 1

theorem tail_flush_execution (image : Image) (base : Word) (code : TailFlushAt image base)
    (s : MachineState) (pc : s.pc = base) (valid : accessValid (s.getReg .x20) 1 = true)
    (fuel : Nat) (coins : Bool) :
    execute image (4+fuel) s coins =
      (do let result ← execute image fuel (tailFlushPrefix s 4) coins
          return result.charge 4 0) := by
  apply execute_unit_steps (states := tailFlushPrefix s)
  intro i inside
  refine ⟨.base (tailFlushOp i),?_,?_,?_⟩
  · apply code ⟨i,inside⟩
    rw [tail_flush_pc s i (by omega),pc]
  · rw [prefix_succ s i inside]
    interval_cases i
    · simpa [ordinaryStep,memoryArgumentsValid,memAccess,tailFlushPrefix,tailFlushOp,tailFlushOps,signExtend12] using valid
    all_goals rfl
  · interval_cases i <;> rfl

theorem tail_flush_bad_address (s : MachineState) (bad : accessValid (s.getReg .x20) 1 = false) :
    ordinaryStep s (.base (.SB .x20 .x23 0)) = none := by
  simp [ordinaryStep,memoryArgumentsValid,memAccess,signExtend12,bad]

end CommitGolfCandidate.Chained.Native
