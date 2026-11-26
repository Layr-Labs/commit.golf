import CommitGolfCandidate.ChainedLowCopy

/-! Restore a parsed high byte and advance the unpacked-field and scratch cursors. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
attribute [local irreducible] execute

def inverseFieldTailOps : List Instr :=
  [.LBU .x11 .x7 0,.SB .x6 .x11 0,.ADD .x6 .x6 .x9,.ADDI .x7 .x7 2]
def inverseFieldTailWords : List (BitVec 32) := [0x0003c583,0x00b30023,0x00930333,0x00238393]
def inverseFieldTailImage : Image := ⟨inverseFieldTailWords,[]⟩
def inverseFieldTailOp (index : Nat) : Instr := (inverseFieldTailOps[index]?).getD .EBREAK
def inverseFieldTailPrefix (s : MachineState) (count : Nat) : MachineState :=
  (inverseFieldTailOps.take count).foldl execInstrBr s

theorem inverse_field_tail_decode : ∀ i : Fin 4,
    (inverseFieldTailWords[i.val]?).bind decodeInstruction=some (.base (inverseFieldTailOp i.val)) := by
  intro i
  fin_cases i <;> rfl

def InverseFieldTailAt (image : Image) (base : Word) : Prop :=
  ∀ i : Fin 4, ∀ s : MachineState, s.pc=base+BitVec.ofNat 64 (4*i.val) →
    fetch image s=some (.base (inverseFieldTailOp i.val))

theorem inverse_field_tail_at : InverseFieldTailAt inverseFieldTailImage 4096 := by
  intro i s pc
  apply cap_image_fetch inverseFieldTailImage s i.val _ (by have := i.isLt; omega)
  · change s.pc=BitVec.ofNat 64 4096+BitVec.ofNat 64 (4*i.val) at pc
    rw [←BitVec.ofNat_add] at pc
    exact pc
  · exact inverse_field_tail_decode i

theorem inverse_field_tail_byte (s : MachineState) (query : Word) :
    (inverseFieldTailPrefix s 4).getByte query=
      if query=s.getReg .x6 then s.getByte (s.getReg .x7) else s.getByte query := by
  change (s.setByte (s.getReg .x6+0#64)
    (((s.getByte (s.getReg .x7+0#64)).zeroExtend 64).truncate 8)).getByte query=_
  simp only [BitVec.add_zero,BitVec.zeroExtend_eq_setWidth]
  simp [CommitGolfCandidate.set_byte_read]

theorem inverse_field_tail_destination (s : MachineState) :
    (inverseFieldTailPrefix s 4).getReg .x6=s.getReg .x6+s.getReg .x9 := rfl

theorem inverse_field_tail_descriptor (s : MachineState) :
    (inverseFieldTailPrefix s 4).getReg .x7=s.getReg .x7+2 := rfl

theorem inverse_field_tail_frame (s : MachineState) (reg : Reg) (destination : reg≠.x6)
    (descriptor : reg≠.x7) (temporary : reg≠.x11) :
    (inverseFieldTailPrefix s 4).getReg reg=s.getReg reg := by
  cases reg <;> first | contradiction | rfl

private theorem prefix_succ (s : MachineState) (count : Nat) (inside : count<4) :
    inverseFieldTailPrefix s (count+1)=execInstrBr (inverseFieldTailPrefix s count) (inverseFieldTailOp count) := by
  interval_cases count <;> rfl

theorem inverse_field_tail_pc (s : MachineState) (count : Nat) (small : count≤4) :
    (inverseFieldTailPrefix s count).pc=s.pc+BitVec.ofNat 64 (4*count) := by
  induction count with
  | zero => simp [inverseFieldTailPrefix]
  | succ count ih =>
    rw [prefix_succ s count (by omega)]
    have step : (execInstrBr (inverseFieldTailPrefix s count) (inverseFieldTailOp count)).pc=
        (inverseFieldTailPrefix s count).pc+4 := by
      have bounded : count<4 := by omega
      interval_cases count <;> rfl
    rw [step,ih (by omega),BitVec.add_assoc]
    congr 1
    change BitVec.ofNat 64 (4*count)+BitVec.ofNat 64 4=_
    rw [←BitVec.ofNat_add]
    congr 1

theorem inverse_field_tail_execution (image : Image) (base : Word) (code : InverseFieldTailAt image base)
    (s : MachineState) (pc : s.pc=base) (source : accessValid (s.getReg .x7) 1=true)
    (destination : accessValid (s.getReg .x6) 1=true) (fuel : Nat) (coins : Bool) :
    execute image (4+fuel) s coins=
      (do let result ← execute image fuel (inverseFieldTailPrefix s 4) coins
          return result.charge 4 0) := by
  apply execute_unit_steps (states := inverseFieldTailPrefix s)
  intro i inside
  refine ⟨.base (inverseFieldTailOp i),?_,?_,?_⟩
  · apply code ⟨i,inside⟩
    rw [inverse_field_tail_pc s i (by omega),pc]
  · rw [prefix_succ s i inside]
    interval_cases i
    · simpa [ordinaryStep,memoryArgumentsValid,memAccess,inverseFieldTailPrefix,
        inverseFieldTailOp,inverseFieldTailOps,signExtend12] using source
    · have valid : memoryArgumentsValid (inverseFieldTailPrefix s 1) (.SB .x6 .x11 0)=true := by
        change accessValid (s.getReg .x6+0#64) 1=true
        simpa using destination
      change ordinaryStep (inverseFieldTailPrefix s 1) (.base (.SB .x6 .x11 0))=_
      simp only [ordinaryStep,valid,↓reduceIte]
      rfl
    all_goals rfl
  · interval_cases i <;> rfl

end CommitGolfCandidate.Chained.Native
