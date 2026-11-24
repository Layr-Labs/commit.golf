import CommitGolfCandidate.ChainedFirstPackCode
import CommitGolfCandidate.ChainedSchedule

/-! The chained parent phase: descending heap levels, shared hashing, root copy. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def parentInitOps : List Instr := [
  .ADDI .x6 .x10 0, .ADDI .x7 .x12 0, .SRLI .x4 .x19 1,
  .ADDI .x10 .x0 256, .ADDI .x12 .x10 0]

def parentLevelOps (h : Height) : List Instr := [
  .ADDI .x17 .x0 (BitVec.ofNat 12 h.val),
  .ADDI .x16 .x0 4095, .SRLI .x16 .x16 (BitVec.ofNat 6 (256-width h)),
  .ADD .x15 .x9 .x4, .ADDI .x15 .x15 4064,
  .ADDI .x14 .x6 0, .ADDI .x18 .x0 (BitVec.ofNat 12 (calls h-1)),
  .JAL .x19 (BitVec.ofNat 21 (1936-80*h.val)),
  .LD .x20 .x10 0, .SD .x7 .x20 0,
  .LD .x20 .x10 8, .SD .x7 .x20 8,
  .LD .x20 .x10 16, .SD .x7 .x20 16,
  .LD .x20 .x10 24, .SD .x7 .x20 24,
  .ADDI .x6 .x6 4032, .ADDI .x7 .x7 4064,
  .BNE .x7 .x15 8140, .SRLI .x4 .x4 1]

def parentRootOps : List Instr := [
  .LD .x31 .x9 32, .SD .x8 .x31 0, .LD .x31 .x9 40, .SD .x8 .x31 8,
  .LD .x31 .x9 48, .SD .x8 .x31 16, .LD .x31 .x9 56, .SD .x8 .x31 24,
  .ADDI .x5 .x0 1, .ADDI .x10 .x0 0, .ECALL]

def parentHashOps : List Instr := [
  .JAL .x1 16, .ECALL, .ADDI .x1 .x19 0, .JAL .x0 128]

def chainedParentOps : List Instr :=
  parentInitOps ++ (List.finRange 24).flatMap parentLevelOps ++ parentRootOps ++
    parentHashOps ++ firstPackOps ++ continuationOps

def parentInitWords : List (BitVec 32) :=
  [0x00050313,0x00060393,0x0019d213,0x10000513,0x00050613]

def parentLevelWords (h : Height) : List (BitVec 32) := [
  BitVec.ofNat 32 (0x00000893+2^20*h.val),
  0xfff00813, BitVec.ofNat 32 (0x00085813+2^20*(256-width h)),
  0x004487b3,0xfe078793,0x00030713,
  BitVec.ofNat 32 (0x00000913+2^20*(calls h-1)),
  BitVec.ofNat 32 (0x000009ef+2^21*((1936-80*h.val)/2)),
  0x00053a03,0x0143b023,0x00853a03,0x0143b423,
  0x01053a03,0x0143b823,0x01853a03,0x0143bc23,
  0xfc030313,0xfe038393,0xfcf396e3,0x00125213]

def parentRootWords : List (BitVec 32) := [
  0x0204bf83,0x01f43023,0x0284bf83,0x01f43423,0x0304bf83,0x01f43823,
  0x0384bf83,0x01f43c23,0x00100293,0x00000513,0x00000073]

def parentHashWords : List (BitVec 32) := [0x010000ef,0x00000073,0x00098093,0x0800006f]

def chainedParentWords : List (BitVec 32) :=
  parentInitWords ++ (List.finRange 24).flatMap parentLevelWords ++ parentRootWords ++
    parentHashWords ++ firstPackWords ++ continuationWords

def chainedParentOp (index : Nat) : Instr := (chainedParentOps[index]?).getD .EBREAK

theorem parent_init_decode : ∀ i : Fin 5,
    (parentInitWords[i.val]?).bind decodeInstruction = some (.base ((parentInitOps[i.val]?).getD .EBREAK)) := by
  intro i
  fin_cases i <;> rfl

theorem parent_level_decode : ∀ h : Height, ∀ i : Fin 20,
    (parentLevelWords h)[i.val]?.bind decodeInstruction =
      some (.base (((parentLevelOps h)[i.val]?).getD .EBREAK)) := by
  intro h i
  fin_cases h <;> fin_cases i <;> rfl

theorem parent_root_decode : ∀ i : Fin 11,
    (parentRootWords[i.val]?).bind decodeInstruction = some (.base ((parentRootOps[i.val]?).getD .EBREAK)) := by
  intro i
  fin_cases i <;> rfl

theorem parent_hash_decode : ∀ i : Fin 4,
    (parentHashWords[i.val]?).bind decodeInstruction = some (.base ((parentHashOps[i.val]?).getD .EBREAK)) := by
  intro i
  fin_cases i <;> rfl

theorem chained_parent_lengths : chainedParentWords.length = 550 ∧ chainedParentOps.length = 550 := by
  decide +kernel

theorem chained_parent_decode : ∀ i : Fin 550,
    (chainedParentWords[i.val]?).bind decodeInstruction = some (.base (chainedParentOp i.val)) := by
  intro i
  fin_cases i <;> rfl

def ChainedParentAt (image : Image) (base : Word) : Prop :=
  ∀ i : Fin 550, ∀ s : MachineState, s.pc = base+BitVec.ofNat 64 (4*i.val) →
    fetch image s = some (.base (chainedParentOp i.val))

end CommitGolfCandidate.Chained.Native
