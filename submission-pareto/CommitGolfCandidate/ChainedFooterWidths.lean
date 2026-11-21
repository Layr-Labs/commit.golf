import CommitGolfCandidate.ChainedRecordWidths
import CommitGolfCandidate.ChainedFooterHeader

/-! Runtime footer width selection writes only the odd metadata byte. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
attribute [local irreducible] execute

def widthStoreOps : List Instr := [.SB .x7 .x10 1,.ADDI .x7 .x7 2]
def widthStorePrefix (s : MachineState) (count : Nat) : MachineState :=
  (widthStoreOps.take count).foldl execInstrBr s

theorem width_store_byte (s : MachineState) (query : Word) :
    (widthStorePrefix s 2).getByte query=
      if query=s.getReg .x7+1 then (s.getReg .x10).truncate 8 else s.getByte query := by
  change (s.setByte (s.getReg .x7+1#64) ((s.getReg .x10).truncate 8)).getByte query=_
  rw [show (1 : Word)=1#64 from rfl]
  simp only [CommitGolfCandidate.set_byte_read]

theorem width_store_pointer (s : MachineState) : (widthStorePrefix s 2).getReg .x7=s.getReg .x7+2 := rfl
theorem width_store_register (s : MachineState) (reg : Reg) (different : reg≠.x7) :
    (widthStorePrefix s 2).getReg reg=s.getReg reg := by
  cases reg <;> first | contradiction | rfl
theorem width_store_pc (s : MachineState) : (widthStorePrefix s 2).pc=s.pc+8 := by
  change (s.pc+4#64)+4#64=s.pc+8
  rw [BitVec.add_assoc]
  rfl

theorem width_store_execution (image : Image) (base : Word) (code : OpsAt image base widthStoreOps)
    (s : MachineState) (pc : s.pc=base) (access : accessValid (s.getReg .x7+1) 1=true)
    (fuel : Nat) (coins : Bool) :
    execute image (2+fuel) s coins=
      (do let result ← execute image fuel (widthStorePrefix s 2) coins
          return result.charge 2 0) := by
  apply execute_unit_steps (states := widthStorePrefix s)
  intro index inside
  refine ⟨.base (widthStoreOps.getD index .EBREAK),?_,?_,?_⟩
  · apply code index inside
    interval_cases index
    · simpa [widthStorePrefix] using pc
    · change s.pc+4#64=base+4#64
      rw [pc]
  · interval_cases index
    · have valid : memoryArgumentsValid s (.SB .x7 .x10 1)=true := access
      change ordinaryStep s (.base (.SB .x7 .x10 1))=_
      simp only [ordinaryStep,valid,↓reduceIte]
      rfl
    · rfl
  · interval_cases index <;> rfl

def footerWidthsOps : List Instr := footerHeaderOps++widthStoreOps
def footerWidthsWords : List (BitVec 32) :=
  [0x00200513,0x01df7463,0x00600513,0x00100493,0x00a380a3,0x00238393]
def footerWidthsImage : Image := ⟨footerWidthsWords,[]⟩
def footerWidthsState (s : MachineState) : MachineState := widthStorePrefix (footerHeaderState s) 2

theorem footer_widths_decode (index : Fin 6) :
    (footerWidthsWords[index.val]?).bind decodeInstruction=
      some (.base (footerWidthsOps.getD index.val .EBREAK)) := by
  fin_cases index <;> rfl

theorem footer_widths_at : OpsAt footerWidthsImage 4096 footerWidthsOps := by
  intro index inside s pc
  have bound : index<6 := inside
  apply cap_image_fetch footerWidthsImage s index _ (by omega)
  · change s.pc=BitVec.ofNat 64 4096+BitVec.ofNat 64 (4*index) at pc
    rwa [←BitVec.ofNat_add] at pc
  · exact footer_widths_decode ⟨index,bound⟩

theorem footer_widths_byte (s : MachineState) (node : Nat) (fit : node<2^64)
    (cursor : s.getReg .x30=BitVec.ofNat 64 node) (limit : s.getReg .x29=256) (query : Word) :
    (footerWidthsState s).getByte query=
      if query=s.getReg .x7+1 then BitVec.ofNat 8 (InteriorCodec.footerWidth node-232) else s.getByte query := by
  rw [footerWidthsState,width_store_byte,footer_header_register s .x7 (by decide) (by decide),
    footer_header_width s node fit cursor limit,footer_header_byte]
  have narrow : (BitVec.ofNat 64 (InteriorCodec.footerWidth node-232)).truncate 8=
      BitVec.ofNat 8 (InteriorCodec.footerWidth node-232) := by
    unfold InteriorCodec.footerWidth
    split <;> rfl
  rw [narrow]

theorem footer_widths_register (s : MachineState) (reg : Reg)
    (pointer : reg≠.x7) (skip : reg≠.x9) (temporary : reg≠.x10) :
    (footerWidthsState s).getReg reg=s.getReg reg := by
  rw [footerWidthsState,width_store_register _ reg pointer,footer_header_register s reg skip temporary]

theorem footer_widths_pointer (s : MachineState) : (footerWidthsState s).getReg .x7=s.getReg .x7+2 := by
  rw [footerWidthsState,width_store_pointer,footer_header_register s .x7 (by decide) (by decide)]

theorem footer_widths_execution (image : Image) (base : Word) (code : OpsAt image base footerWidthsOps)
    (s : MachineState) (pc : s.pc=base) (access : accessValid (s.getReg .x7+1) 1=true)
    (fuel : Nat) (coins : Bool) :
    execute image (footerHeaderCycles s+2+fuel) s coins=
      (do let result ← execute image fuel (footerWidthsState s) coins
          return result.charge (footerHeaderCycles s+2) 0) := by
  have header := ops_at_left image base footerHeaderOps widthStoreOps code
  have tail := ops_at_right image base footerHeaderOps widthStoreOps code
  change OpsAt image (base+16) widthStoreOps at tail
  have nextPC : (footerHeaderState s).pc=base+16 := by rw [footer_header_pc,pc]
  have nextAccess : accessValid ((footerHeaderState s).getReg .x7+1) 1=true := by
    rwa [footer_header_register s .x7 (by decide) (by decide)]
  rw [show footerHeaderCycles s+2+fuel=footerHeaderCycles s+(2+fuel) by omega,
    footer_header_execution image base header s pc,
    width_store_execution image (base+16) tail (footerHeaderState s) nextPC nextAccess]
  simp [footerWidthsState,Execution.charge,Nat.add_assoc]

end CommitGolfCandidate.Chained.Native
