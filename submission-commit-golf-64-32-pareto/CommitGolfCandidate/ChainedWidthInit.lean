import CommitGolfCandidate.ChainedParsedPayload
import CommitGolfCandidate.ChainedInverseRecordCode

/-! Trusted odd-byte width initialization without reading untrusted proof bytes. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
attribute [local irreducible] execute

def widthInitOps (width : Fin 7) : List Instr :=
  [.ADDI .x10 .x0 (BitVec.ofNat 12 width.val),.SB .x7 .x10 1,.ADDI .x7 .x7 2]
def widthInitWords (width : Fin 7) : List (BitVec 32) :=
  [BitVec.ofNat 32 (0x00000513+1048576*width.val),0x00a380a3,0x00238393]
def widthInitImage (width : Fin 7) : Image := ⟨widthInitWords width,[]⟩
def widthInitPrefix (width : Fin 7) (s : MachineState) (count : Nat) : MachineState :=
  ((widthInitOps width).take count).foldl execInstrBr s

theorem width_init_decode (width : Fin 7) (index : Fin 3) :
    ((widthInitWords width)[index.val]?).bind decodeInstruction=
      some (.base ((widthInitOps width).getD index.val .EBREAK)) := by
  fin_cases width <;> fin_cases index <;> rfl

theorem width_init_at (width : Fin 7) : OpsAt (widthInitImage width) 4096 (widthInitOps width) := by
  intro index inside s pc
  have bound : index<3 := inside
  apply cap_image_fetch (widthInitImage width) s index _ (by omega)
  · change s.pc=BitVec.ofNat 64 4096+BitVec.ofNat 64 (4*index) at pc
    rwa [←BitVec.ofNat_add] at pc
  · exact width_init_decode width ⟨index,bound⟩

theorem width_init_byte (width : Fin 7) (s : MachineState) (query : Word) :
    (widthInitPrefix width s 3).getByte query=
      if query=s.getReg .x7+1 then BitVec.ofNat 8 width.val else s.getByte query := by
  have value : ((0#64+signExtend12 (BitVec.ofNat 12 width.val)).truncate 8)=BitVec.ofNat 8 width.val := by
    fin_cases width <;> rfl
  change (s.setByte (s.getReg .x7+1#64)
    ((0#64+signExtend12 (BitVec.ofNat 12 width.val)).truncate 8)).getByte query=_
  rw [value]
  rw [show (1 : Word)=1#64 from rfl]
  simp only [CommitGolfCandidate.set_byte_read]

theorem width_init_pointer (width : Fin 7) (s : MachineState) :
    (widthInitPrefix width s 3).getReg .x7=s.getReg .x7+2 := rfl

theorem width_init_register (width : Fin 7) (s : MachineState) (reg : Reg)
    (pointer : reg≠.x7) (temporary : reg≠.x10) :
    (widthInitPrefix width s 3).getReg reg=s.getReg reg := by
  cases reg <;> first | contradiction | rfl

theorem width_init_pc (width : Fin 7) (s : MachineState) (count : Nat) (bound : count≤3) :
    (widthInitPrefix width s count).pc=s.pc+BitVec.ofNat 64 (4*count) := by
  interval_cases count
  · simp [widthInitPrefix]
  · rfl
  · change (s.pc+4#64)+4#64=s.pc+8#64
    rw [BitVec.add_assoc]; rfl
  · change ((s.pc+4#64)+4#64)+4#64=s.pc+12#64
    rw [BitVec.add_assoc,BitVec.add_assoc]; rfl

theorem width_init_execution (image : Image) (base : Word) (width : Fin 7)
    (code : OpsAt image base (widthInitOps width)) (s : MachineState) (pc : s.pc=base)
    (access : accessValid (s.getReg .x7+1) 1=true) (fuel : Nat) (coins : Bool) :
    execute image (3+fuel) s coins=
      (do let result ← execute image fuel (widthInitPrefix width s 3) coins
          return result.charge 3 0) := by
  apply execute_unit_steps (states := widthInitPrefix width s)
  intro index inside
  refine ⟨.base ((widthInitOps width).getD index .EBREAK),?_,?_,?_⟩
  · apply code index inside
    rw [width_init_pc width s index (by omega),pc]
  · interval_cases index
    · rfl
    · have valid : memoryArgumentsValid (widthInitPrefix width s 1) (.SB .x7 .x10 1)=true := access
      change ordinaryStep (widthInitPrefix width s 1) (.base (.SB .x7 .x10 1))=_
      simp only [ordinaryStep,valid,↓reduceIte]
      rfl
    · rfl
  · interval_cases index <;> rfl

end CommitGolfCandidate.Chained.Native
