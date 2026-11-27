import CommitGolfCandidate.Stage3cGates
namespace CommitGolfCandidate.Chained.BinaryMachine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 16000
set_option maxHeartbeats 8000000
set_option Elab.async false

/-- Even slots advance the destination by 32 bytes, odd slots by 64. -/
def ptrDstImm (odd : Bool) : BitVec 12 := if odd then 64 else 32

/-- One running-pointer parent. Width 238 is dormant on this image and live for the narrower levels. -/
def PtrSlot (n width : Nat) (odd : Bool) : Prop :=
  decoded n = some (.base .ECALL) ∧
  (width = 256 →
    decoded (n+1) = some (.base (.ADDI .x10 .x10 96)) ∧
    decoded (n+2) = some (.base (.ADDI .x12 .x12 (ptrDstImm odd)))) ∧
  (width = 240 →
    decoded (n+1) = some (.base (.SH .x12 .x0 30)) ∧
    decoded (n+2) = some (.base (.ADDI .x10 .x10 96)) ∧
    decoded (n+3) = some (.base (.ADDI .x12 .x12 (ptrDstImm odd)))) ∧
  (width = 238 →
    decoded (n+1) = some (.base (.LHU .x31 .x12 28)) ∧
    decoded (n+2) = some (.base (.AND .x31 .x31 .x30)) ∧
    decoded (n+3) = some (.base (.SW .x12 .x31 28)) ∧
    decoded (n+4) = some (.base (.ADDI .x10 .x10 96)) ∧
    decoded (n+5) = some (.base (.ADDI .x12 .x12 (ptrDstImm odd))))
instance (n width : Nat) (odd : Bool) : Decidable (PtrSlot n width odd) := by
  unfold PtrSlot; infer_instance

def PtrLoop (d : Height) : Prop :=
  (∀ i : Fin 128, PtrSlot (mainPC d + laneWords d * i.val) (wireWidth d) (decide (i.val % 2 = 1))) ∧
  decoded (mainPC d + 128 * laneWords d) = some (.base (.ADDI .x20 .x20 4095)) ∧
  mainPC d + 128 * laneWords d + 2 = passEnd d ∧
  Gate false (mainPC d) (passEnd d)
instance (d : Height) : Decidable (PtrLoop d) := by unfold PtrLoop; infer_instance

def PtrStraight (d : Height) : Prop :=
  (∀ i : Fin 64, i.val < count d →
    PtrSlot (tailPC d + laneWords d * i.val) (wireWidth d) (decide (i.val % 2 = 1))) ∧
  tailPC d + count d * laneWords d = passEnd d
instance (d : Height) : Decidable (PtrStraight d) := by unfold PtrStraight; infer_instance

theorem pointer_sites : ∀ d : Height, ¬chained d →
    (d.val = 23 → decoded (tailPC d) = some (.base .ECALL) ∧ tailPC d + 1 = passEnd d) ∧
    (tileSize d ≠ 0 → PtrLoop d) ∧
    (tileSize d = 0 ∧ d.val ≠ 23 → count d ≤ 64 ∧ PtrStraight d) := by
  decide +kernel

end CommitGolfCandidate.Chained.BinaryMachine
