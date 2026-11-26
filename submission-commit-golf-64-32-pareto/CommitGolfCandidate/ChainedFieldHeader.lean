import CommitGolfCandidate.ChainedRawField

/-! Native trusted skip/width initialization before each field constructor. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
attribute [local irreducible] execute

def fieldHeaderOps (skip : Fin 4) (width : Fin 7) : List Instr :=
  [.ADDI .x9 .x0 (BitVec.ofNat 12 skip.val),.ADDI .x10 .x0 (BitVec.ofNat 12 width.val)]
def fieldHeaderOp (skip : Fin 4) (width : Fin 7) (index : Nat) : Instr :=
  ((fieldHeaderOps skip width)[index]?).getD .EBREAK
def fieldHeaderPrefix (skip : Fin 4) (width : Fin 7) (s : MachineState) (count : Nat) : MachineState :=
  ((fieldHeaderOps skip width).take count).foldl execInstrBr s

theorem field_header_skip (skip : Fin 4) (width : Fin 7) (s : MachineState) :
    (fieldHeaderPrefix skip width s 2).getReg .x9=BitVec.ofNat 64 skip.val := by
  fin_cases skip <;> rfl

theorem field_header_width (skip : Fin 4) (width : Fin 7) (s : MachineState) :
    (fieldHeaderPrefix skip width s 2).getReg .x10=BitVec.ofNat 64 width.val := by
  fin_cases width <;> rfl

theorem field_header_frame (skip : Fin 4) (width : Fin 7) (s : MachineState) (reg : Reg)
    (notSkip : reg≠.x9) (notWidth : reg≠.x10) :
    (fieldHeaderPrefix skip width s 2).getReg reg=s.getReg reg := by
  cases reg <;> first | contradiction | rfl

theorem field_header_byte (skip : Fin 4) (width : Fin 7) (s : MachineState) (query : Word) :
    (fieldHeaderPrefix skip width s 2).getByte query=s.getByte query := rfl

theorem field_header_pc (skip : Fin 4) (width : Fin 7) (s : MachineState) (count : Nat) (small : count≤2) :
    (fieldHeaderPrefix skip width s count).pc=s.pc+BitVec.ofNat 64 (4*count) := by
  interval_cases count
  · simp [fieldHeaderPrefix]
  · rfl
  · change (s.pc+4#64)+4#64=s.pc+8#64
    rw [BitVec.add_assoc]
    rfl

def FieldHeaderAt (image : Image) (base : Word) (skip : Fin 4) (width : Fin 7) : Prop :=
  ∀ i : Fin 2, ∀ s : MachineState, s.pc=base+BitVec.ofNat 64 (4*i.val) →
    fetch image s=some (.base (fieldHeaderOp skip width i.val))

theorem field_header_execution (image : Image) (base : Word) (skip : Fin 4) (width : Fin 7)
    (code : FieldHeaderAt image base skip width) (s : MachineState) (pc : s.pc=base)
    (fuel : Nat) (coins : Bool) :
    execute image (2+fuel) s coins=
      (do let result ← execute image fuel (fieldHeaderPrefix skip width s 2) coins
          return result.charge 2 0) := by
  apply execute_unit_steps (states := fieldHeaderPrefix skip width s)
  intro i inside
  refine ⟨.base (fieldHeaderOp skip width i),?_,?_,?_⟩
  · apply code ⟨i,inside⟩
    rw [field_header_pc skip width s i (by omega),pc]
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

def preparedFieldState (skip : Fin 4) (width : Fin 7) (n : Nat) (s : MachineState) : MachineState :=
  fieldBuildState n (fieldHeaderPrefix skip width s 2)

theorem prepared_field_execution (image : Image) (base : Word) (skip : Fin 4) (width : Fin 7)
    (n : Nat) (header : FieldHeaderAt image base skip width)
    (copyCode : LowCopyAt image (base+8) n)
    (descriptor : FieldDescriptorAt image ((base+8)+BitVec.ofNat 64 (16*n)))
    (s : MachineState) (pc : s.pc=base)
    (source : (s.getReg .x5).toNat+n+1≤MEMORY_BYTES)
    (destination : (s.getReg .x6).toNat+n≤MEMORY_BYTES)
    (scratch : (s.getReg .x7).toNat+2≤MEMORY_BYTES) (fuel : Nat) (coins : Bool) :
    execute image (4*n+7+fuel) s coins=
      (do let result ← execute image fuel (preparedFieldState skip width n s) coins
          return result.charge (4*n+7) 0) := by
  let readyState := fieldHeaderPrefix skip width s 2
  have ready := field_build_access n readyState
    (by simpa only [readyState,field_header_frame skip width s .x5 (by decide) (by decide)] using source)
    (by simpa only [readyState,field_header_frame skip width s .x6 (by decide) (by decide)] using destination)
    (by simpa only [readyState,field_header_frame skip width s .x7 (by decide) (by decide)] using scratch)
  have nextPC : readyState.pc=base+8 := by
    change (fieldHeaderPrefix skip width s 2).pc=base+8
    rw [field_header_pc skip width s 2 (by decide),pc]
    rfl
  rw [show 4*n+7+fuel=2+(4*n+5+fuel) by omega,
    field_header_execution image base skip width header s pc,
    field_build_execution image (base+8) n copyCode descriptor readyState nextPC
      ready.1 ready.2.1 ready.2.2.1 ready.2.2.2]
  simp [preparedFieldState,readyState,Execution.charge,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  simp only [show 2+(4*n+5)=4*n+7 by omega]

theorem prepared_raw_field (skip : Fin 4) (width : Fin 7)
    (low padding rest : Proof) (high : List Bool) (s : MachineState)
    (source destination scratch : Nat)
    (sourceReg : s.getReg .x5=BitVec.ofNat 64 source)
    (destinationReg : s.getReg .x6=BitVec.ofNat 64 destination)
    (scratchReg : s.getReg .x7=BitVec.ofNat 64 scratch)
    (correctSkip : skip.val=1+padding.length) (correctWidth : width.val=high.length)
    (memory : BytesAt s (BitVec.ofNat 64 source) (low++tailBitsWord 8 high::(padding++rest)))
    (ordered : destination≤source)
    (separate : source+low.length+1+padding.length+rest.length≤scratch)
    (room : scratch+2<2^64) :
    BytesAt (preparedFieldState skip width low.length s) (BitVec.ofNat 64 destination) low ∧
    BytesAt (preparedFieldState skip width low.length s) (BitVec.ofNat 64 scratch) (descriptorBytes [high]) ∧
    BytesAt (preparedFieldState skip width low.length s)
      (BitVec.ofNat 64 (source+low.length+1+padding.length)) rest ∧
    (preparedFieldState skip width low.length s).getReg .x5=BitVec.ofNat 64 (source+low.length+1+padding.length) ∧
    (preparedFieldState skip width low.length s).getReg .x6=BitVec.ofNat 64 (destination+low.length) ∧
    (preparedFieldState skip width low.length s).getReg .x7=BitVec.ofNat 64 (scratch+2) := by
  unfold preparedFieldState
  apply native_raw_field low padding rest high (fieldHeaderPrefix skip width s 2) source destination scratch
  · rw [field_header_frame skip width s .x5 (by decide) (by decide),sourceReg]
  · rw [field_header_frame skip width s .x6 (by decide) (by decide),destinationReg]
  · rw [field_header_frame skip width s .x7 (by decide) (by decide),scratchReg]
  · rw [field_header_skip,correctSkip]
  · rw [field_header_width,correctWidth]
  · intro index inside
    rw [field_header_byte]
    exact memory index inside
  · exact ordered
  · exact separate
  · exact room

end CommitGolfCandidate.Chained.Native
