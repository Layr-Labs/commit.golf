import CommitGolfCandidate.ChainedTailFinish

/-! Read a variable-width field, refilling one byte only when necessary. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def tailRefillOps : List Instr := [
  .LBU .x24 .x20 0,.SLL .x24 .x24 .x25,.OR .x23 .x23 .x24,
  .ADDI .x25 .x25 8,.ADDI .x20 .x20 1]
def tailExtractOps : List Instr := [
  .ADDI .x28 .x0 1,.SLL .x28 .x28 .x26,.ADDI .x28 .x28 4095,
  .AND .x24 .x23 .x28,.SRL .x23 .x23 .x26,.SUB .x25 .x25 .x26]
def tailReadOps : List Instr := [.BGEU .x25 .x26 24] ++ tailRefillOps ++ tailExtractOps
def tailReadWords : List (BitVec 32) := [
  0x01acfc63,0x000a4c03,0x019c1c33,0x018bebb3,0x008c8c93,0x001a0a13,
  0x00100e13,0x01ae1e33,0xfffe0e13,0x01cbfc33,0x01abdbb3,0x41ac8cb3]
def tailReadImage : Image := ⟨tailReadWords,[]⟩
def tailReadOp (index : Nat) : Instr := (tailReadOps[index]?).getD .EBREAK
def tailRefillOp (index : Nat) : Instr := (tailRefillOps[index]?).getD .EBREAK
def tailExtractOp (index : Nat) : Instr := (tailExtractOps[index]?).getD .EBREAK
def tailRefillPrefix (s : MachineState) (count : Nat) : MachineState :=
  (tailRefillOps.take count).foldl execInstrBr s
def tailExtractPrefix (s : MachineState) (count : Nat) : MachineState :=
  (tailExtractOps.take count).foldl execInstrBr s

theorem tail_read_decode : ∀ i : Fin 12,
    (tailReadWords[i.val]?).bind decodeInstruction = some (.base (tailReadOp i.val)) := by
  intro i
  fin_cases i <;> rfl

def TailReadAt (image : Image) (base : Word) : Prop :=
  ∀ i : Fin 12, ∀ s : MachineState, s.pc = base+BitVec.ofNat 64 (4*i.val) →
    fetch image s = some (.base (tailReadOp i.val))

theorem tail_read_at : TailReadAt tailReadImage 4096 := by
  intro i s pc
  apply cap_image_fetch tailReadImage s i.val _ (by have := i.isLt; omega)
  · change s.pc = BitVec.ofNat 64 4096+BitVec.ofNat 64 (4*i.val) at pc
    rw [←BitVec.ofNat_add] at pc
    exact pc
  · exact tail_read_decode i

end CommitGolfCandidate.Chained.Native
