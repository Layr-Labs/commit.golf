import CommitGolfCandidate.ChainedContinuationCode

/-! Contiguous 238-bit child packing with the height above the 476-bit seed. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def firstPackOps : List Instr := [
  .LD .x20 .x14 0,
  .LD .x21 .x14 8,
  .LD .x22 .x14 16,
  .LD .x23 .x14 24,
  .LD .x24 .x14 32,
  .LD .x25 .x14 40,
  .LD .x26 .x14 48,
  .LD .x27 .x14 56,
  .SD .x10 .x20 0,
  .SD .x10 .x21 8,
  .SD .x10 .x22 16,
  .SLLI .x28 .x24 46,
  .OR .x28 .x23 .x28,
  .SD .x10 .x28 24,
  .SRLI .x28 .x24 18,
  .SLLI .x29 .x25 46,
  .OR .x28 .x28 .x29,
  .SD .x10 .x28 32,
  .SRLI .x28 .x25 18,
  .SLLI .x29 .x26 46,
  .OR .x28 .x28 .x29,
  .SD .x10 .x28 40,
  .SRLI .x28 .x26 18,
  .SLLI .x29 .x27 46,
  .OR .x28 .x28 .x29,
  .SD .x10 .x28 48,
  .SRLI .x28 .x27 18,
  .SLLI .x29 .x17 28,
  .OR .x28 .x28 .x29,
  .SD .x10 .x28 56,
  .JALR .x0 .x1 0]

def firstPackWords : List (BitVec 32) := [
  0x00073a03,0x00873a83,0x01073b03,0x01873b83,0x02073c03,0x02873c83,0x03073d03,0x03873d83,0x01453023,0x01553423,0x01653823,0x02ec1e13,0x01cbee33,0x01c53c23,0x012c5e13,0x02ec9e93,0x01de6e33,0x03c53023,0x012cde13,0x02ed1e93,0x01de6e33,0x03c53423,0x012d5e13,0x02ed9e93,0x01de6e33,0x03c53823,0x012dde13,0x01c89e93,0x01de6e33,0x03c53c23,0x00008067]

def firstPackImage : Image := ⟨firstPackWords,[]⟩
def firstPackOp (index : Nat) : Instr := (firstPackOps[index]?).getD .EBREAK
def firstPackPrefix (s : MachineState) (count : Nat) : MachineState :=
  (firstPackOps.take count).foldl execInstrBr s

theorem first_pack_decode : ∀ i : Fin 31,
    (firstPackWords[i.val]?).bind decodeInstruction = some (.base (firstPackOp i.val)) := by
  intro i
  fin_cases i <;> rfl

def FirstPackAt (image : Image) (base : Word) : Prop :=
  ∀ i : Fin 31, ∀ s : MachineState, s.pc = base+BitVec.ofNat 64 (4*i.val) →
    fetch image s = some (.base (firstPackOp i.val))

theorem first_pack_at : FirstPackAt firstPackImage 4096 := by
  intro i s pc
  apply cap_image_fetch firstPackImage s i.val _ (by have := i.isLt; omega)
  · change s.pc = BitVec.ofNat 64 4096+BitVec.ofNat 64 (4*i.val) at pc
    rw [← BitVec.ofNat_add] at pc
    exact pc
  · exact first_pack_decode i

end CommitGolfCandidate.Chained.Native
