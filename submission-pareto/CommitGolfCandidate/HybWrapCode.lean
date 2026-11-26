import CommitGolfCandidate.QuadCheckImage
import CommitGolfCandidate.QOpeningImage
import CommitGolfCandidate.CheckActions

/-! The hybrid checker wrapper (check-image words 464-2141) as a structured program.

Word 0 jumps to word 464. Absolute word layout:
- 464-471: empty test (`x16 = 0` → 2138), `x30 = 816k + 1696`, length test (`x17 ≠ x30` → 2141);
- 472-477: `x24-x29 := x10-x15`;
- 478-482: `x6` = the level-13 table of the proof, `x7 = H + 136`;
- 483-960: the table copy, 26 groups of two nodes and one half group to slots 3 and 4;
- 961-1164: the hashes of levels 14-19 (55 calls) and the clear of ragged slots 4;
- 1165-1180: pointers to the last compact record (`x8`), donor record (`x9`), index word (`x18`),
  count `x19`, buffer `x20`, constants `x4 = 5`, `x30 = 96`, `x5 = 368`;
- 1181-2083: one record (copy to the buffer, salt, 19 levels, virtual index, latch);
- 2084-2137: zero 20 words past the records, `x17 = 2456k`, `x6 = 2456`, restore, zero, jump to 1;
- 2138-2140: empty case; 2141: reject (jump to the donor's reject at word 364). -/

namespace TwoPermutationPrototype.HybWrap
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64

set_option maxRecDepth 100000

def H : Nat := 268435456
def BUF : Nat := 269484032

/-- Nodes of level `L` (levels 16-22). -/
def count : Nat → Nat
  | 13 => 53 | 14 => 27 | 15 => 14 | 16 => 7 | 17 => 4 | 18 => 2 | _ => 1

/-- Scratch base of the level-`L` groups. -/
def HB : Nat → Nat
  | 13 => 268435456 | 14 => 268445392 | 15 => 268450544 | 16 => 268453120 | 17 => 268454592
  | 18 => 268455328 | _ => 268455696

def hi20 (v : Nat) : BitVec 20 := BitVec.ofNat 20 ((v+2048)/4096)
def lo12 (v : Nat) : BitVec 12 := BitVec.ofNat 12 (v % 4096)
def liCode (rd : Reg) (v : Nat) : List Instr := [.LUI rd (hi20 v), .ADDI rd rd (lo12 v)]

def copyPairs (src dst : Reg) (a b n : Nat) : List Instr :=
  (List.range n).flatMap fun m => [.LD .x31 src (BitVec.ofNat 12 (a+8*m)), .SD dst .x31 (BitVec.ofNat 12 (b+8*m))]

def zeroStores (base : Reg) (n : Nat) : List Instr :=
  (List.range n).map fun m => .SD base .x0 (BitVec.ofNat 12 (8*m))

def entryCode : List Instr :=
  [.BNE .x16 .x0 8, .JAL .x0 6692, .ADDI .x30 .x0 816, .MUL .x30 .x16 .x30, .ADDI .x30 .x30 1696,
   .ADDI .x30 .x30 0, .BEQ .x17 .x30 8, .JAL .x0 6680]

def saveCode : List Instr :=
  [.ADDI .x24 .x10 0, .ADDI .x25 .x11 0, .ADDI .x26 .x12 0, .ADDI .x27 .x13 0, .ADDI .x28 .x14 0,
   .ADDI .x29 .x15 0]

def tableSetup : List Instr := [.ADDI .x30 .x30 2400, .ADDI .x30 .x30 0, .ADD .x6 .x29 .x30] ++ liCode .x7 (H+136)

def tableGroup : List Instr := copyPairs .x6 .x7 0 0 8 ++ [.ADDI .x6 .x6 64, .ADDI .x7 .x7 368]

def tableHalf : List Instr := copyPairs .x6 .x7 0 0 4 ++ [.ADDI .x6 .x6 32, .ADDI .x7 .x7 368]

def tableCode : List Instr := ((List.range 26).flatMap fun _ => tableGroup) ++ tableHalf

def hashSetup : List Instr := [.ADDI .x11 .x0 200, .ADDI .x13 .x0 1, .ADDI .x5 .x0 0]

def hashCall (j : Nat) : List Instr :=
  [.ECALL, .ADDI .x10 .x10 368, .ADDI .x12 .x12 (if j % 2 = 0 then 32 else 336)]

def hashLevel (L : Nat) : List Instr :=
  liCode .x10 (HB (L-1)) ++ liCode .x12 (HB L + 136) ++ (List.range (count L)).flatMap hashCall ++
    (if count L % 2 = 1 then zeroStores .x12 4 else [])

def hashCode : List Instr := (List.range 6).flatMap fun i => hashLevel (14+i)

def expSetup : List Instr :=
  [.ADDI .x31 .x16 4095, .ADDI .x8 .x0 816, .MUL .x8 .x31 .x8, .ADD .x8 .x29 .x8] ++ liCode .x9 2456 ++
  [.MUL .x9 .x31 .x9, .ADD .x9 .x29 .x9, .SLLI .x18 .x31 3, .ADD .x18 .x27 .x18, .ADDI .x19 .x16 0] ++
  liCode .x20 BUF ++ [.ADDI .x4 .x0 5, .ADDI .x30 .x0 96, .ADDI .x5 .x0 368]

def recordCopy : List Instr := copyPairs .x8 .x20 0 0 102

def saltCode : List Instr :=
  [.LD .x31 .x20 0, .SD .x9 .x31 0, .LD .x31 .x20 8, .SD .x9 .x31 8, .LD .x21 .x18 0, .ADDI .x22 .x21 0,
   .ADDI .x23 .x0 0, .ADDI .x1 .x0 1, .ADDI .x7 .x9 24]

def pentaHead : List Instr :=
  [.REMU .x3 .x22 .x4, .DIVU .x22 .x22 .x4, .MUL .x12 .x3 .x1, .ADD .x23 .x23 .x12, .MUL .x1 .x1 .x4]

def pentaLevel (k : Nat) : List Instr :=
  pentaHead ++ copyPairs .x20 .x7 (16+128*k) 0 16 ++ [.ADDI .x7 .x7 128]

def binHead : List Instr :=
  [.ANDI .x3 .x22 1, .SRLI .x22 .x22 1, .ADDI .x12 .x3 3, .MUL .x12 .x12 .x1, .ADD .x23 .x23 .x12,
   .MUL .x1 .x1 .x4] ++ zeroStores .x7 16 ++ [.MUL .x6 .x3 .x30, .ADD .x6 .x6 .x7]

def binLow (k : Nat) : List Instr := binHead ++ copyPairs .x20 .x6 (528+32*(k-4)) 0 4 ++ [.ADDI .x7 .x7 128]

def upSource (k : Nat) : List Instr :=
  liCode .x11 (HB k + 168) ++ [.MUL .x10 .x22 .x5, .ADD .x10 .x10 .x11, .SLLI .x12 .x3 5, .SUB .x10 .x10 .x12]

def binHigh (k : Nat) : List Instr := binHead ++ upSource k ++ copyPairs .x10 .x6 0 0 4 ++ [.ADDI .x7 .x7 128]

def levelCode (k : Nat) : List Instr := if k < 4 then pentaLevel k else if k < 13 then binLow k else binHigh k

def levelsCode : List Instr := (List.range 19).flatMap levelCode

def latchCode : List Instr :=
  [.SD .x9 .x23 16, .ADDI .x8 .x8 3280, .ADDI .x9 .x9 2868, .ADDI .x9 .x9 2868, .ADDI .x18 .x18 4088,
   .ADDI .x19 .x19 4095, .BNE .x19 .x0 4584]

def restoreRegs : List Instr :=
  [.ADDI .x10 .x24 0, .ADDI .x11 .x25 0, .ADDI .x12 .x26 0, .ADDI .x13 .x27 0, .ADDI .x14 .x28 0,
   .ADDI .x15 .x29 0]

def zeroedRegs : List Reg :=
  [.x1, .x3, .x4, .x5, .x7, .x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29,
   .x30, .x31]

def tailCode : List Instr :=
  liCode .x17 2456 ++ [.MUL .x17 .x16 .x17, .ADD .x6 .x29 .x17] ++ zeroStores .x6 20 ++ liCode .x6 2456 ++
    restoreRegs ++ zeroedRegs.map (fun r => .ADDI r .x0 0) ++ [.JAL .x0 2088608]

def emptyCode : List Instr := liCode .x6 2456 ++ [.JAL .x0 2088596]

def rejectCode : List Instr := [.JAL .x0 2090044]

def wrapCode : List Instr :=
  entryCode ++ saveCode ++ tableSetup ++ tableCode ++ hashSetup ++ hashCode ++ expSetup ++ recordCopy ++
    saltCode ++ levelsCode ++ latchCode ++ tailCode ++ emptyCode ++ rejectCode

theorem wrap_code_length : wrapCode.length = 1678 := by decide

/-! ### The image carries the wrapper -/

private theorem base_of_decode (w : BitVec 32) (instr : Instr) (h : QOpening.decodeBase w = some instr) :
    decodeInstruction w = some (.base instr) := by
  unfold QOpening.decodeBase at h
  cases hd : decodeInstruction w with
  | none => simp [hd] at h
  | some r =>
    cases r with
    | base b =>
      simp only [hd, Option.bind_some, Option.some.injEq] at h
      rw [h]
    | word op rd rs₁ rs₂ => simp [hd] at h
    | sraiw rd rs sh => simp [hd] at h

set_option maxHeartbeats 4000000 in
private theorem wrap_list :
    (Quad.Checker.quadCheckImage.code.drop 464).map QOpening.decodeBase = wrapCode.map some := by
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem entry_decoded :
    (Quad.Checker.quadCheckImage.code[0]?).bind QOpening.decodeBase = some (.JAL .x0 1856) := by
  decide +kernel

/-- An image carrying the wrapper at words 464-2141 and the entry jump at word 0. -/
structure WrapImage (img : Image) : Prop where
  entry : (img.code[0]?).bind decodeInstruction = some (.base (.JAL .x0 1856))
  words : ∀ i < 1678, (img.code[464+i]?).bind decodeInstruction = (wrapCode[i]?).map Instruction.base

theorem quad_wrap_image : WrapImage Quad.Checker.quadCheckImage where
  entry := by
    have h := entry_decoded
    cases hc : Quad.Checker.quadCheckImage.code[0]? with
    | none => rw [hc] at h; cases h
    | some w =>
      rw [hc, Option.bind_some] at h
      rw [Option.bind_some]
      exact base_of_decode w _ h
  words := by
    intro i hi
    have h : (Quad.Checker.quadCheckImage.code[464+i]?).bind QOpening.decodeBase = wrapCode[i]? := by
      have e := congrArg (fun l => l[i]?) wrap_list
      simp only [List.getElem?_map, List.getElem?_drop] at e
      cases hc : Quad.Checker.quadCheckImage.code[464+i]? <;> cases hw : wrapCode[i]? <;> simp_all
    have hw : wrapCode[i]? = some (wrapCode[i]'(by rw [wrap_code_length]; exact hi)) :=
      List.getElem?_eq_getElem _
    rw [hw] at h ⊢
    cases hc : Quad.Checker.quadCheckImage.code[464+i]? with
    | none => rw [hc] at h; cases h
    | some w =>
      rw [hc, Option.bind_some] at h
      rw [Option.bind_some, Option.map_some]
      exact base_of_decode w _ h

end TwoPermutationPrototype.HybWrap
