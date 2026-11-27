import CommitGolfCandidate.Stage3cCode
namespace CommitGolfCandidate.Chained.BinaryMachine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000
set_option Elab.async false

/-- Signed 12-bit encoding of a cursor offset stored as a bias-2048 immediate. -/
def immRaw (off : Nat) : Nat := if off ≥ 2048 then off - 2048 else off + 2048

def srcOff (n c : Nat) : Nat :=
  let m := n % 16
  let pair := (n % 32) / 2
  let odd := n % 2
  match c with
  | 0 => 256 * m
  | 1 => 256 * m + 64
  | 2 => 256 * m + 160
  | _ => 184 * pair + (if odd = 0 then 0 else 88)

def dstOff (n c : Nat) : Nat :=
  let m := n % 16
  let r := n % 32
  let pair := r / 2
  let odd := r % 2
  match c with
  | 0 => 256 * m + 64
  | 1 => 184 * pair + (if odd = 0 then 0 else 120)
  | 2 => 184 * pair + (if odd = 0 then 0 else 120) + 32
  | _ => 96 * pair + 32 * odd

def srcReg (c : Nat) : Reg := if c = 3 then .x22 else .x21
def dstReg (c : Nat) : Reg := if c = 0 then .x21 else if c = 3 then .x23 else .x22

def callInstr (n c part : Nat) : Instr :=
  match part with
  | 0 => .ADDI .x10 (srcReg c) (BitVec.ofNat 12 (immRaw (srcOff n c)))
  | 1 => .ADDI .x12 (dstReg c) (BitVec.ofNat 12 (immRaw (dstOff n c)))
  | _ => .ECALL

/-- Static instruction at offset `i` inside the 1555-word leaf tile.
Four groups of 32 leaves. Each group is 388 words, except the last, which keeps
the back-edge. -/
def tileOp (i : Nat) : Instr :=
  let g := if i < 1164 then i / 388 else 3
  let k := if i < 1164 then i % 388 else i - 1164
  let n := g * 32
  if k < 192 then callInstr (n + k / 12) (k % 12 / 3) (k % 12 % 3)
  else if k = 192 then .ADD .x21 .x21 .x25
  else if k < 385 then
    let t := k - 193
    callInstr (n + 16 + t / 12) (t % 12 / 3) (t % 12 % 3)
  else
    match k - 385 with
    | 0 => .ADD .x21 .x21 .x25
    | 1 => .ADD .x22 .x22 .x26
    | 2 => .ADDI .x23 .x23 (BitVec.ofNat 12 1536)
    | 3 => .ADDI .x20 .x20 (BitVec.ofNat 12 4095)
    | 4 => .BEQ .x20 .x0 (BitVec.ofNat 13 8)
    | _ => .JAL .x0 (BitVec.ofNat 21 2090936)

theorem tile_span : 4123 + 1555 = 5678 := by decide

theorem origins_agree (j : Fin 128) :
    4123 + 12 * j.val + j.val / 16 + 2 * (j.val / 32) =
      4123 + (j.val / 32) * 388 +
        (if j.val % 32 < 16 then 12 * (j.val % 32)
         else 193 + 12 * (j.val % 32 - 16)) := by
  revert j
  decide

theorem tile_decode : ∀ i : Fin 1555,
    decoded (4123 + i.val) = some (.base (tileOp i.val)) := by
  decide +kernel

end CommitGolfCandidate.Chained.BinaryMachine
