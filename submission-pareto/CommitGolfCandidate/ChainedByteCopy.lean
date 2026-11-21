import CommitGolfCandidate.ChainedPayloadExecution

/-! Straight-line byte copying for the low part of a split-width field. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
attribute [local irreducible] execute

def byteCopyOps : List Instr :=
  [.LBU .x11 .x5 0,.SB .x6 .x11 0,.ADDI .x5 .x5 1,.ADDI .x6 .x6 1]
def byteCopyWords : List (BitVec 32) := [0x0002c583,0x00b30023,0x00128293,0x00130313]
def byteCopyImage : Image := ⟨byteCopyWords,[]⟩
def byteCopyOp (index : Nat) : Instr := (byteCopyOps[index]?).getD .EBREAK
def byteCopyPrefix (s : MachineState) (count : Nat) : MachineState :=
  (byteCopyOps.take count).foldl execInstrBr s

theorem byte_copy_decode : ∀ i : Fin 4,
    (byteCopyWords[i.val]?).bind decodeInstruction=some (.base (byteCopyOp i.val)) := by
  intro i
  fin_cases i <;> rfl

def ByteCopyAt (image : Image) (base : Word) : Prop :=
  ∀ i : Fin 4, ∀ s : MachineState, s.pc=base+BitVec.ofNat 64 (4*i.val) →
    fetch image s=some (.base (byteCopyOp i.val))

theorem byte_copy_at : ByteCopyAt byteCopyImage 4096 := by
  intro i s pc
  apply cap_image_fetch byteCopyImage s i.val _ (by have := i.isLt; omega)
  · change s.pc=BitVec.ofNat 64 4096+BitVec.ofNat 64 (4*i.val) at pc
    rw [←BitVec.ofNat_add] at pc
    exact pc
  · exact byte_copy_decode i

theorem byte_copy_byte (s : MachineState) (query : Word) :
    (byteCopyPrefix s 4).getByte query=
      if query=s.getReg .x6 then s.getByte (s.getReg .x5) else s.getByte query := by
  change (s.setByte (s.getReg .x6+0#64) (((s.getByte (s.getReg .x5+0#64)).zeroExtend 64).truncate 8)).getByte query=_
  simp only [BitVec.add_zero,BitVec.zeroExtend_eq_setWidth]
  simp [CommitGolfCandidate.set_byte_read]

theorem byte_copy_source (s : MachineState) : (byteCopyPrefix s 4).getReg .x5=s.getReg .x5+1 := rfl
theorem byte_copy_destination (s : MachineState) : (byteCopyPrefix s 4).getReg .x6=s.getReg .x6+1 := rfl

theorem byte_copy_frame (s : MachineState) (reg : Reg) (source : reg≠.x5)
    (destination : reg≠.x6) (temporary : reg≠.x11) : (byteCopyPrefix s 4).getReg reg=s.getReg reg := by
  cases reg <;> first | contradiction | rfl

private theorem prefix_succ (s : MachineState) (count : Nat) (inside : count<4) :
    byteCopyPrefix s (count+1)=execInstrBr (byteCopyPrefix s count) (byteCopyOp count) := by
  interval_cases count <;> rfl

theorem byte_copy_pc (s : MachineState) (count : Nat) (small : count≤4) :
    (byteCopyPrefix s count).pc=s.pc+BitVec.ofNat 64 (4*count) := by
  induction count with
  | zero => simp [byteCopyPrefix]
  | succ count ih =>
    rw [prefix_succ s count (by omega)]
    have step : (execInstrBr (byteCopyPrefix s count) (byteCopyOp count)).pc=(byteCopyPrefix s count).pc+4 := by
      have inside : count<4 := by omega
      interval_cases count <;> rfl
    rw [step,ih (by omega),BitVec.add_assoc]
    congr 1
    change BitVec.ofNat 64 (4*count)+BitVec.ofNat 64 4=_
    rw [←BitVec.ofNat_add]
    congr 1

theorem byte_copy_execution (image : Image) (base : Word) (code : ByteCopyAt image base)
    (s : MachineState) (pc : s.pc=base) (source : accessValid (s.getReg .x5) 1=true)
    (destination : accessValid (s.getReg .x6) 1=true) (fuel : Nat) (coins : Bool) :
    execute image (4+fuel) s coins=
      (do let result ← execute image fuel (byteCopyPrefix s 4) coins
          return result.charge 4 0) := by
  apply execute_unit_steps (states := byteCopyPrefix s)
  intro i inside
  refine ⟨.base (byteCopyOp i),?_,?_,?_⟩
  · apply code ⟨i,inside⟩
    rw [byte_copy_pc s i (by omega),pc]
  · rw [prefix_succ s i inside]
    interval_cases i
    · simpa [ordinaryStep,memoryArgumentsValid,memAccess,byteCopyPrefix,byteCopyOp,byteCopyOps,signExtend12] using source
    · have valid : memoryArgumentsValid (byteCopyPrefix s 1) (.SB .x6 .x11 0)=true := by
        change accessValid (s.getReg .x6+0#64) 1=true
        simpa using destination
      change ordinaryStep (byteCopyPrefix s 1) (.base (.SB .x6 .x11 0))=_
      simp only [ordinaryStep,valid,↓reduceIte]
      rfl
    all_goals rfl
  · interval_cases i <;> rfl

theorem byte_copy_bad_source (s : MachineState) (bad : accessValid (s.getReg .x5) 1=false) :
    ordinaryStep s (.base (.LBU .x11 .x5 0))=none := by
  simp [ordinaryStep,memoryArgumentsValid,memAccess,signExtend12,bad]

end CommitGolfCandidate.Chained.Native
