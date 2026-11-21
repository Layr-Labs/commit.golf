import CommitGolfCandidate.ChainedByteCopy

/-! Build one native value/width descriptor from a raw field's final byte. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
attribute [local irreducible] execute

def fieldDescriptorOps : List Instr :=
  [.LBU .x11 .x5 0,.SB .x7 .x11 0,.SB .x7 .x10 1,.ADDI .x7 .x7 2,.ADD .x5 .x5 .x9]
def fieldDescriptorWords : List (BitVec 32) := [0x0002c583,0x00b38023,0x00a380a3,0x00238393,0x009282b3]
def fieldDescriptorImage : Image := ⟨fieldDescriptorWords,[]⟩
def fieldDescriptorOp (index : Nat) : Instr := (fieldDescriptorOps[index]?).getD .EBREAK
def fieldDescriptorPrefix (s : MachineState) (count : Nat) : MachineState :=
  (fieldDescriptorOps.take count).foldl execInstrBr s

theorem field_descriptor_decode : ∀ i : Fin 5,
    (fieldDescriptorWords[i.val]?).bind decodeInstruction=some (.base (fieldDescriptorOp i.val)) := by
  intro i
  fin_cases i <;> rfl

def FieldDescriptorAt (image : Image) (base : Word) : Prop :=
  ∀ i : Fin 5, ∀ s : MachineState, s.pc=base+BitVec.ofNat 64 (4*i.val) →
    fetch image s=some (.base (fieldDescriptorOp i.val))

theorem field_descriptor_at : FieldDescriptorAt fieldDescriptorImage 4096 := by
  intro i s pc
  apply cap_image_fetch fieldDescriptorImage s i.val _ (by have := i.isLt; omega)
  · change s.pc=BitVec.ofNat 64 4096+BitVec.ofNat 64 (4*i.val) at pc
    rw [←BitVec.ofNat_add] at pc
    exact pc
  · exact field_descriptor_decode i

theorem field_descriptor_byte (s : MachineState) (query : Word) :
    (fieldDescriptorPrefix s 5).getByte query=
      if query=s.getReg .x7+1 then (s.getReg .x10).setWidth 8 else
        if query=s.getReg .x7 then s.getByte (s.getReg .x5) else s.getByte query := by
  change ((s.setByte (s.getReg .x7+0#64) (((s.getByte (s.getReg .x5+0#64)).zeroExtend 64).truncate 8)).setByte
    (s.getReg .x7+1#64) ((s.getReg .x10).truncate 8)).getByte query=_
  simp only [BitVec.add_zero,BitVec.zeroExtend_eq_setWidth]
  simp [CommitGolfCandidate.set_byte_read]

theorem field_descriptor_source (s : MachineState) :
    (fieldDescriptorPrefix s 5).getReg .x5=s.getReg .x5+s.getReg .x9 := rfl
theorem field_descriptor_pointer (s : MachineState) :
    (fieldDescriptorPrefix s 5).getReg .x7=s.getReg .x7+2 := rfl

theorem field_descriptor_frame (s : MachineState) (reg : Reg) (source : reg≠.x5)
    (descriptor : reg≠.x7) (temporary : reg≠.x11) : (fieldDescriptorPrefix s 5).getReg reg=s.getReg reg := by
  cases reg <;> first | contradiction | rfl

theorem field_descriptor_memory (s : MachineState) (back : List Bool)
    (value : s.getByte (s.getReg .x5)=tailBitsWord 8 back)
    (width : s.getReg .x10=BitVec.ofNat 64 back.length) :
    BytesAt (fieldDescriptorPrefix s 5) (s.getReg .x7) (descriptorBytes [back]) := by
  intro index inside
  have bound : index<2 := by simpa [descriptorBytes] using inside
  interval_cases index <;> rw [field_descriptor_byte]
  · simp [descriptorBytes,value]
  · simp [descriptorBytes,width]

private theorem prefix_succ (s : MachineState) (count : Nat) (inside : count<5) :
    fieldDescriptorPrefix s (count+1)=execInstrBr (fieldDescriptorPrefix s count) (fieldDescriptorOp count) := by
  interval_cases count <;> rfl

theorem field_descriptor_pc (s : MachineState) (count : Nat) (small : count≤5) :
    (fieldDescriptorPrefix s count).pc=s.pc+BitVec.ofNat 64 (4*count) := by
  induction count with
  | zero => simp [fieldDescriptorPrefix]
  | succ count ih =>
    rw [prefix_succ s count (by omega)]
    have step : (execInstrBr (fieldDescriptorPrefix s count) (fieldDescriptorOp count)).pc=(fieldDescriptorPrefix s count).pc+4 := by
      have inside : count<5 := by omega
      interval_cases count <;> rfl
    rw [step,ih (by omega),BitVec.add_assoc]
    congr 1
    change BitVec.ofNat 64 (4*count)+BitVec.ofNat 64 4=_
    rw [←BitVec.ofNat_add]
    congr 1

theorem field_descriptor_execution (image : Image) (base : Word) (code : FieldDescriptorAt image base)
    (s : MachineState) (pc : s.pc=base) (source : accessValid (s.getReg .x5) 1=true)
    (value : accessValid (s.getReg .x7) 1=true) (width : accessValid (s.getReg .x7+1) 1=true)
    (fuel : Nat) (coins : Bool) :
    execute image (5+fuel) s coins=
      (do let result ← execute image fuel (fieldDescriptorPrefix s 5) coins
          return result.charge 5 0) := by
  apply execute_unit_steps (states := fieldDescriptorPrefix s)
  intro i inside
  refine ⟨.base (fieldDescriptorOp i),?_,?_,?_⟩
  · apply code ⟨i,inside⟩
    rw [field_descriptor_pc s i (by omega),pc]
  · rw [prefix_succ s i inside]
    interval_cases i
    · simpa [ordinaryStep,memoryArgumentsValid,memAccess,fieldDescriptorPrefix,fieldDescriptorOp,fieldDescriptorOps,signExtend12] using source
    · have valid : memoryArgumentsValid (fieldDescriptorPrefix s 1) (.SB .x7 .x11 0)=true := by
        change accessValid (s.getReg .x7+0#64) 1=true
        simpa using value
      change ordinaryStep (fieldDescriptorPrefix s 1) (.base (.SB .x7 .x11 0))=_
      simp only [ordinaryStep,valid,↓reduceIte]
      rfl
    · have valid : memoryArgumentsValid (fieldDescriptorPrefix s 2) (.SB .x7 .x10 1)=true := by
        exact width
      change ordinaryStep (fieldDescriptorPrefix s 2) (.base (.SB .x7 .x10 1))=_
      simp only [ordinaryStep,valid,↓reduceIte]
      rfl
    all_goals rfl
  · interval_cases i <;> rfl

end CommitGolfCandidate.Chained.Native
