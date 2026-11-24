import CommitGolfCandidate.TwoPermutationPackedFetchBase

/-! Full-width continuation calls, followed by one final digest mask. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def continuationOps : List Instr := [
  .BEQ .x18 .x0 60,
  .SLLI .x29 .x17 3,
  .SUB .x29 .x29 .x17,
  .SD .x10 .x29 32,
  .SD .x10 .x0 40,
  .SD .x10 .x0 48,
  .ADDI .x30 .x0 1,
  .SLLI .x30 .x30 63,
  .SD .x10 .x30 56,
  .ECALL,
  .LD .x29 .x10 32,
  .ADDI .x29 .x29 1,
  .SD .x10 .x29 32,
  .ADDI .x18 .x18 4095,
  .BNE .x18 .x0 8172,
  .LD .x29 .x10 24,
  .AND .x29 .x29 .x16,
  .SD .x10 .x29 24,
  .JALR .x0 .x1 0]

def continuationWords : List (BitVec 32) := [
  0x02090e63,0x00389e93,0x411e8eb3,0x03d53023,0x02053423,0x02053823,
  0x00100f13,0x03ff1f13,0x03e53c23,0x00000073,0x02053e83,0x001e8e93,
  0x03d53023,0xfff90913,0xfe0916e3,0x01853e83,0x010efeb3,0x01d53c23,0x00008067]

def continuationImage : Image := ⟨continuationWords,[]⟩

def continuationOp (index : Nat) : Instr := (continuationOps[index]?).getD .EBREAK

theorem continuation_decode : ∀ i : Fin 19,
    (continuationWords[i.val]?).bind decodeInstruction = some (.base (continuationOp i.val)) := by
  intro i
  fin_cases i <;> rfl

def ContinuationAt (image : Image) (base : Word) : Prop :=
  ∀ i : Fin 19, ∀ s : MachineState, s.pc = base+BitVec.ofNat 64 (4*i.val) →
    fetch image s = some (.base (continuationOp i.val))

theorem continuation_at : ContinuationAt continuationImage 4096 := by
  intro i s pc
  apply cap_image_fetch continuationImage s i.val _ (by have := i.isLt; omega)
  · change s.pc = BitVec.ofNat 64 4096+BitVec.ofNat 64 (4*i.val) at pc
    rw [← BitVec.ofNat_add] at pc
    exact pc
  · exact continuation_decode i

def ordinaryPrefix (s : MachineState) (offset count : Nat) : MachineState :=
  ((continuationOps.drop offset).take count).foldl execInstrBr s

def continuationInstructions (remaining : Nat) : Nat := if remaining = 0 then 5 else 13+6*remaining
def continuationCycles (remaining : Nat) : Nat := if remaining = 0 then 5 else 13+13*remaining

end CommitGolfCandidate.Chained.Native
