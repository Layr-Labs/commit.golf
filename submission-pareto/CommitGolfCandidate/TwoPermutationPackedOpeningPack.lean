import CommitGolfCandidate.TwoPermutationPackedOpeningImage
import CommitGolfCandidate.TwoPermutationOpeningCapImage
import CommitGolfCandidate.WriteMemory
import CommitGolfCandidate.ProofCodec
import CommitGolfCandidate.RegisterPreservation

/-! The opener's pack postpass: the common exit block jumps to code appended at word 1435
that rewrites the unpacked proof buffer in place into `ProofCodec.pack`. -/
namespace TwoPermutationPrototype.PackedOpening.Pack
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192

def packCode : List Instr := [
  .ADDI .x7 .x0 48, .MUL .x7 .x16 .x7, .SUB .x8 .x11 .x7, .ADDI .x9 .x0 30, .DIVU .x8 .x8 .x9, .ADDI .x18 .x0 1,
  .SLLI .x18 .x18 33, .ADD .x18 .x18 .x20, .ADDI .x19 .x8 3, .SRLI .x19 .x19 2, .SLLI .x19 .x19 2, .ADDI .x9 .x0 15,
  .MUL .x9 .x16 .x9, .ADDI .x22 .x0 0, .BEQ .x22 .x19 112, .ADDI .x23 .x0 0, .BGEU .x22 .x8 88, .BGEU .x22 .x9 48,
  .ADDI .x24 .x0 15, .DIVU .x25 .x22 .x24, .MUL .x26 .x25 .x24, .SUB .x26 .x22 .x26, .ADDI .x24 .x0 498, .MUL .x25 .x25 .x24,
  .ADDI .x25 .x25 48, .ADDI .x24 .x0 30, .MUL .x26 .x26 .x24, .ADD .x25 .x25 .x26, .JAL .x0 28, .SUB .x26 .x22 .x9,
  .ADDI .x24 .x0 30, .MUL .x26 .x26 .x24, .ADDI .x24 .x0 498, .MUL .x25 .x16 .x24, .ADD .x25 .x25 .x26, .ADD .x25 .x25 .x20,
  .LBU .x23 .x25 29, .ANDI .x23 .x23 63, .ADD .x24 .x18 .x22, .SB .x24 .x23 0, .ADDI .x22 .x22 1, .JAL .x0 2097044,
  .ADDI .x24 .x0 29, .MUL .x27 .x8 .x24, .ADD .x27 .x27 .x7, .ADDI .x29 .x0 483, .MUL .x29 .x16 .x29, .ADDI .x22 .x0 0,
  .BEQ .x22 .x27 160, .BGEU .x22 .x29 88, .ADDI .x24 .x0 483, .DIVU .x25 .x22 .x24, .MUL .x26 .x25 .x24, .SUB .x26 .x22 .x26,
  .ADDI .x24 .x0 498, .MUL .x25 .x25 .x24, .ADDI .x24 .x0 48, .BLTU .x26 .x24 48, .SUB .x26 .x26 .x24, .ADDI .x24 .x0 29,
  .DIVU .x28 .x26 .x24, .MUL .x30 .x28 .x24, .SUB .x26 .x26 .x30, .ADDI .x24 .x0 30, .MUL .x28 .x28 .x24, .ADD .x25 .x25 .x28,
  .ADDI .x25 .x25 48, .ADD .x25 .x25 .x26, .JAL .x0 56, .ADD .x25 .x25 .x26, .JAL .x0 48, .SUB .x26 .x22 .x29,
  .ADDI .x24 .x0 29, .DIVU .x28 .x26 .x24, .MUL .x30 .x28 .x24, .SUB .x26 .x26 .x30, .ADDI .x24 .x0 30, .MUL .x28 .x28 .x24,
  .ADDI .x24 .x0 498, .MUL .x25 .x16 .x24, .ADD .x25 .x25 .x28, .ADD .x25 .x25 .x26, .ADD .x25 .x25 .x20, .LBU .x23 .x25 0,
  .ADD .x24 .x22 .x20, .SB .x24 .x23 0, .ADDI .x22 .x22 1, .JAL .x0 2096996, .ADDI .x22 .x0 0, .ADD .x26 .x27 .x20,
  .BEQ .x22 .x19 80, .ADD .x25 .x18 .x22, .LBU .x23 .x25 0, .LBU .x24 .x25 1, .SLLI .x24 .x24 6, .OR .x23 .x23 .x24,
  .LBU .x24 .x25 2, .SLLI .x24 .x24 12, .OR .x23 .x23 .x24, .LBU .x24 .x25 3, .SLLI .x24 .x24 18, .OR .x23 .x23 .x24,
  .SB .x26 .x23 0, .SRLI .x23 .x23 8, .SB .x26 .x23 1, .SRLI .x23 .x23 8, .SB .x26 .x23 2, .ADDI .x26 .x26 3,
  .ADDI .x22 .x22 4, .JAL .x0 2097076, .SRLI .x24 .x19 2, .ADD .x23 .x24 .x24, .ADD .x24 .x23 .x24, .ADD .x11 .x27 .x24,
  .ECALL]

theorem pack_code_length : packCode.length = 115 := rfl

private theorem table :
    (openingImage.code.drop 1435).map Opening.decodeBase = packCode.map some := by decide

/-- Program counter of packer word `t`. -/
def pcOf (t : Nat) : Word := BitVec.ofNat 64 (4096 + 4 * (1435 + t))

theorem fetch_pack (s : MachineState) (t : Nat) (ht : t < 115) (pc : s.pc = pcOf t) :
    fetch openingImage s = some (.base (packCode.getD t .NOP)) := by
  have atWord := congrArg (fun xs : List (Option Instr) => xs[t]?) table
  simp only [List.getElem?_map, List.getElem?_drop] at atWord
  have hp : packCode[t]? = some (packCode.getD t .NOP) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [pack_code_length]; exact ht)]
    rfl
  rw [hp] at atWord
  apply packed_fetch_raw s (1435 + t) _ (by omega) pc
  cases hw : openingImage.code[1435 + t]? with
  | none => simp [hw] at atWord
  | some w =>
    simp only [hw, Option.map_some, Option.some.injEq] at atWord
    cases hi : decodeInstruction w with
    | none => simp [Opening.decodeBase, hi] at atWord
    | some op =>
      cases op <;> simp [Opening.decodeBase, hi] at atWord <;> simp [hi, atWord]

/-- Fuel `steps`, cost `cycles`, no oracle calls. -/
def Runs (a b : MachineState) (steps cycles : Nat) : Prop :=
  ∀ fuel coins, execute openingImage (steps + fuel) a coins =
    (do let result ← execute openingImage fuel b coins
        return result.charge cycles 0)

theorem Runs.refl (s : MachineState) : Runs s s 0 0 := by
  intro fuel coins
  simp [Execution.charge]

theorem Runs.trans {a b c : MachineState} {s1 c1 s2 c2 : Nat}
    (first : Runs a b s1 c1) (second : Runs b c s2 c2) : Runs a c (s1 + s2) (c1 + c2) := by
  intro fuel coins
  rw [Nat.add_assoc, first (s2 + fuel) coins, second fuel coins]
  simp [Execution.charge, ← Nat.add_assoc, Nat.add_comm c1 c2]

theorem Runs.cast {a b : MachineState} {s1 c1 s2 c2 : Nat} (run : Runs a b s1 c1)
    (hs : s1 = s2) (hc : c1 = c2) : Runs a b s2 c2 := hs ▸ hc ▸ run

def ordinaryInstr : Instr → Bool
  | .ECALL | .EBREAK | .CSRS _ _ | .LI _ _ | .MV _ _ | .NOP => false
  | _ => true

theorem ordinary_step_eq (s : MachineState) (i : Instr) (ord : ordinaryInstr i = true)
    (valid : memoryArgumentsValid s i = true) :
    ordinaryStep s (.base i) = some (execInstrBr s i) := by
  cases i <;> simp_all [ordinaryStep, ordinaryInstr]

def instrAt (t : Nat) : Instr := packCode.getD t .NOP

@[simp] theorem instrAt_0 : instrAt 0 = .ADDI .x7 .x0 48 := rfl
@[simp] theorem instrAt_1 : instrAt 1 = .MUL .x7 .x16 .x7 := rfl
@[simp] theorem instrAt_2 : instrAt 2 = .SUB .x8 .x11 .x7 := rfl
@[simp] theorem instrAt_3 : instrAt 3 = .ADDI .x9 .x0 30 := rfl
@[simp] theorem instrAt_4 : instrAt 4 = .DIVU .x8 .x8 .x9 := rfl
@[simp] theorem instrAt_5 : instrAt 5 = .ADDI .x18 .x0 1 := rfl
@[simp] theorem instrAt_6 : instrAt 6 = .SLLI .x18 .x18 33 := rfl
@[simp] theorem instrAt_7 : instrAt 7 = .ADD .x18 .x18 .x20 := rfl
@[simp] theorem instrAt_8 : instrAt 8 = .ADDI .x19 .x8 3 := rfl
@[simp] theorem instrAt_9 : instrAt 9 = .SRLI .x19 .x19 2 := rfl
@[simp] theorem instrAt_10 : instrAt 10 = .SLLI .x19 .x19 2 := rfl
@[simp] theorem instrAt_11 : instrAt 11 = .ADDI .x9 .x0 15 := rfl
@[simp] theorem instrAt_12 : instrAt 12 = .MUL .x9 .x16 .x9 := rfl
@[simp] theorem instrAt_13 : instrAt 13 = .ADDI .x22 .x0 0 := rfl
@[simp] theorem instrAt_14 : instrAt 14 = .BEQ .x22 .x19 112 := rfl
@[simp] theorem instrAt_15 : instrAt 15 = .ADDI .x23 .x0 0 := rfl
@[simp] theorem instrAt_16 : instrAt 16 = .BGEU .x22 .x8 88 := rfl
@[simp] theorem instrAt_17 : instrAt 17 = .BGEU .x22 .x9 48 := rfl
@[simp] theorem instrAt_18 : instrAt 18 = .ADDI .x24 .x0 15 := rfl
@[simp] theorem instrAt_19 : instrAt 19 = .DIVU .x25 .x22 .x24 := rfl
@[simp] theorem instrAt_20 : instrAt 20 = .MUL .x26 .x25 .x24 := rfl
@[simp] theorem instrAt_21 : instrAt 21 = .SUB .x26 .x22 .x26 := rfl
@[simp] theorem instrAt_22 : instrAt 22 = .ADDI .x24 .x0 498 := rfl
@[simp] theorem instrAt_23 : instrAt 23 = .MUL .x25 .x25 .x24 := rfl
@[simp] theorem instrAt_24 : instrAt 24 = .ADDI .x25 .x25 48 := rfl
@[simp] theorem instrAt_25 : instrAt 25 = .ADDI .x24 .x0 30 := rfl
@[simp] theorem instrAt_26 : instrAt 26 = .MUL .x26 .x26 .x24 := rfl
@[simp] theorem instrAt_27 : instrAt 27 = .ADD .x25 .x25 .x26 := rfl
@[simp] theorem instrAt_28 : instrAt 28 = .JAL .x0 28 := rfl
@[simp] theorem instrAt_29 : instrAt 29 = .SUB .x26 .x22 .x9 := rfl
@[simp] theorem instrAt_30 : instrAt 30 = .ADDI .x24 .x0 30 := rfl
@[simp] theorem instrAt_31 : instrAt 31 = .MUL .x26 .x26 .x24 := rfl
@[simp] theorem instrAt_32 : instrAt 32 = .ADDI .x24 .x0 498 := rfl
@[simp] theorem instrAt_33 : instrAt 33 = .MUL .x25 .x16 .x24 := rfl
@[simp] theorem instrAt_34 : instrAt 34 = .ADD .x25 .x25 .x26 := rfl
@[simp] theorem instrAt_35 : instrAt 35 = .ADD .x25 .x25 .x20 := rfl
@[simp] theorem instrAt_36 : instrAt 36 = .LBU .x23 .x25 29 := rfl
@[simp] theorem instrAt_37 : instrAt 37 = .ANDI .x23 .x23 63 := rfl
@[simp] theorem instrAt_38 : instrAt 38 = .ADD .x24 .x18 .x22 := rfl
@[simp] theorem instrAt_39 : instrAt 39 = .SB .x24 .x23 0 := rfl
@[simp] theorem instrAt_40 : instrAt 40 = .ADDI .x22 .x22 1 := rfl
@[simp] theorem instrAt_41 : instrAt 41 = .JAL .x0 2097044 := rfl
@[simp] theorem instrAt_42 : instrAt 42 = .ADDI .x24 .x0 29 := rfl
@[simp] theorem instrAt_43 : instrAt 43 = .MUL .x27 .x8 .x24 := rfl
@[simp] theorem instrAt_44 : instrAt 44 = .ADD .x27 .x27 .x7 := rfl
@[simp] theorem instrAt_45 : instrAt 45 = .ADDI .x29 .x0 483 := rfl
@[simp] theorem instrAt_46 : instrAt 46 = .MUL .x29 .x16 .x29 := rfl
@[simp] theorem instrAt_47 : instrAt 47 = .ADDI .x22 .x0 0 := rfl
@[simp] theorem instrAt_48 : instrAt 48 = .BEQ .x22 .x27 160 := rfl
@[simp] theorem instrAt_49 : instrAt 49 = .BGEU .x22 .x29 88 := rfl
@[simp] theorem instrAt_50 : instrAt 50 = .ADDI .x24 .x0 483 := rfl
@[simp] theorem instrAt_51 : instrAt 51 = .DIVU .x25 .x22 .x24 := rfl
@[simp] theorem instrAt_52 : instrAt 52 = .MUL .x26 .x25 .x24 := rfl
@[simp] theorem instrAt_53 : instrAt 53 = .SUB .x26 .x22 .x26 := rfl
@[simp] theorem instrAt_54 : instrAt 54 = .ADDI .x24 .x0 498 := rfl
@[simp] theorem instrAt_55 : instrAt 55 = .MUL .x25 .x25 .x24 := rfl
@[simp] theorem instrAt_56 : instrAt 56 = .ADDI .x24 .x0 48 := rfl
@[simp] theorem instrAt_57 : instrAt 57 = .BLTU .x26 .x24 48 := rfl
@[simp] theorem instrAt_58 : instrAt 58 = .SUB .x26 .x26 .x24 := rfl
@[simp] theorem instrAt_59 : instrAt 59 = .ADDI .x24 .x0 29 := rfl
@[simp] theorem instrAt_60 : instrAt 60 = .DIVU .x28 .x26 .x24 := rfl
@[simp] theorem instrAt_61 : instrAt 61 = .MUL .x30 .x28 .x24 := rfl
@[simp] theorem instrAt_62 : instrAt 62 = .SUB .x26 .x26 .x30 := rfl
@[simp] theorem instrAt_63 : instrAt 63 = .ADDI .x24 .x0 30 := rfl
@[simp] theorem instrAt_64 : instrAt 64 = .MUL .x28 .x28 .x24 := rfl
@[simp] theorem instrAt_65 : instrAt 65 = .ADD .x25 .x25 .x28 := rfl
@[simp] theorem instrAt_66 : instrAt 66 = .ADDI .x25 .x25 48 := rfl
@[simp] theorem instrAt_67 : instrAt 67 = .ADD .x25 .x25 .x26 := rfl
@[simp] theorem instrAt_68 : instrAt 68 = .JAL .x0 56 := rfl
@[simp] theorem instrAt_69 : instrAt 69 = .ADD .x25 .x25 .x26 := rfl
@[simp] theorem instrAt_70 : instrAt 70 = .JAL .x0 48 := rfl
@[simp] theorem instrAt_71 : instrAt 71 = .SUB .x26 .x22 .x29 := rfl
@[simp] theorem instrAt_72 : instrAt 72 = .ADDI .x24 .x0 29 := rfl
@[simp] theorem instrAt_73 : instrAt 73 = .DIVU .x28 .x26 .x24 := rfl
@[simp] theorem instrAt_74 : instrAt 74 = .MUL .x30 .x28 .x24 := rfl
@[simp] theorem instrAt_75 : instrAt 75 = .SUB .x26 .x26 .x30 := rfl
@[simp] theorem instrAt_76 : instrAt 76 = .ADDI .x24 .x0 30 := rfl
@[simp] theorem instrAt_77 : instrAt 77 = .MUL .x28 .x28 .x24 := rfl
@[simp] theorem instrAt_78 : instrAt 78 = .ADDI .x24 .x0 498 := rfl
@[simp] theorem instrAt_79 : instrAt 79 = .MUL .x25 .x16 .x24 := rfl
@[simp] theorem instrAt_80 : instrAt 80 = .ADD .x25 .x25 .x28 := rfl
@[simp] theorem instrAt_81 : instrAt 81 = .ADD .x25 .x25 .x26 := rfl
@[simp] theorem instrAt_82 : instrAt 82 = .ADD .x25 .x25 .x20 := rfl
@[simp] theorem instrAt_83 : instrAt 83 = .LBU .x23 .x25 0 := rfl
@[simp] theorem instrAt_84 : instrAt 84 = .ADD .x24 .x22 .x20 := rfl
@[simp] theorem instrAt_85 : instrAt 85 = .SB .x24 .x23 0 := rfl
@[simp] theorem instrAt_86 : instrAt 86 = .ADDI .x22 .x22 1 := rfl
@[simp] theorem instrAt_87 : instrAt 87 = .JAL .x0 2096996 := rfl
@[simp] theorem instrAt_88 : instrAt 88 = .ADDI .x22 .x0 0 := rfl
@[simp] theorem instrAt_89 : instrAt 89 = .ADD .x26 .x27 .x20 := rfl
@[simp] theorem instrAt_90 : instrAt 90 = .BEQ .x22 .x19 80 := rfl
@[simp] theorem instrAt_91 : instrAt 91 = .ADD .x25 .x18 .x22 := rfl
@[simp] theorem instrAt_92 : instrAt 92 = .LBU .x23 .x25 0 := rfl
@[simp] theorem instrAt_93 : instrAt 93 = .LBU .x24 .x25 1 := rfl
@[simp] theorem instrAt_94 : instrAt 94 = .SLLI .x24 .x24 6 := rfl
@[simp] theorem instrAt_95 : instrAt 95 = .OR .x23 .x23 .x24 := rfl
@[simp] theorem instrAt_96 : instrAt 96 = .LBU .x24 .x25 2 := rfl
@[simp] theorem instrAt_97 : instrAt 97 = .SLLI .x24 .x24 12 := rfl
@[simp] theorem instrAt_98 : instrAt 98 = .OR .x23 .x23 .x24 := rfl
@[simp] theorem instrAt_99 : instrAt 99 = .LBU .x24 .x25 3 := rfl
@[simp] theorem instrAt_100 : instrAt 100 = .SLLI .x24 .x24 18 := rfl
@[simp] theorem instrAt_101 : instrAt 101 = .OR .x23 .x23 .x24 := rfl
@[simp] theorem instrAt_102 : instrAt 102 = .SB .x26 .x23 0 := rfl
@[simp] theorem instrAt_103 : instrAt 103 = .SRLI .x23 .x23 8 := rfl
@[simp] theorem instrAt_104 : instrAt 104 = .SB .x26 .x23 1 := rfl
@[simp] theorem instrAt_105 : instrAt 105 = .SRLI .x23 .x23 8 := rfl
@[simp] theorem instrAt_106 : instrAt 106 = .SB .x26 .x23 2 := rfl
@[simp] theorem instrAt_107 : instrAt 107 = .ADDI .x26 .x26 3 := rfl
@[simp] theorem instrAt_108 : instrAt 108 = .ADDI .x22 .x22 4 := rfl
@[simp] theorem instrAt_109 : instrAt 109 = .JAL .x0 2097076 := rfl
@[simp] theorem instrAt_110 : instrAt 110 = .SRLI .x24 .x19 2 := rfl
@[simp] theorem instrAt_111 : instrAt 111 = .ADD .x23 .x24 .x24 := rfl
@[simp] theorem instrAt_112 : instrAt 112 = .ADD .x24 .x23 .x24 := rfl
@[simp] theorem instrAt_113 : instrAt 113 = .ADD .x11 .x27 .x24 := rfl
@[simp] theorem instrAt_114 : instrAt 114 = .ECALL := rfl

def cost (t : Nat) : Nat := instructionCycles (.base (instrAt t))

theorem runs_step (s : MachineState) (t : Nat) (ht : t < 115) (pc : s.pc = pcOf t)
    (ord : ordinaryInstr (instrAt t) = true) (valid : memoryArgumentsValid s (instrAt t) = true) :
    Runs s (execInstrBr s (instrAt t)) 1 (cost t) := by
  intro fuel coins
  rw [Nat.add_comm 1 fuel]
  exact execute_ordinary_step _ _ _ _ _ _ (fetch_pack s t ht pc) (ordinary_step_eq s _ ord valid)

/-- Run packer words `ts` in order. -/
def run (s : MachineState) (ts : List Nat) : MachineState :=
  ts.foldl (fun state t => execInstrBr state (instrAt t)) s

def PathOK : MachineState → List Nat → Prop
  | _, [] => True
  | s, t :: ts => t < 115 ∧ s.pc = pcOf t ∧ ordinaryInstr (instrAt t) = true ∧
      memoryArgumentsValid s (instrAt t) = true ∧ PathOK (execInstrBr s (instrAt t)) ts

def pathCycles (ts : List Nat) : Nat := (ts.map cost).sum

theorem runs_path : ∀ (ts : List Nat) (s : MachineState), PathOK s ts →
    Runs s (run s ts) ts.length (pathCycles ts)
  | [], s, _ => by simpa [run, pathCycles] using Runs.refl s
  | t :: ts, s, ⟨ht, pc, ord, valid, rest⟩ => by
    have tail := runs_path ts _ rest
    have both := (runs_step s t ht pc ord valid).trans tail
    simpa [run, pathCycles, Nat.add_comm] using both

/-! Word arithmetic in `toNat` form. -/

theorem divu_toNat (a b : Word) :
    (rv64_divu a b).toNat = if b.toNat = 0 then 2^64 - 1 else a.toNat / b.toNat := by
  unfold rv64_divu
  by_cases h : b = 0#64
  · subst h; simp
  · have : b.toNat ≠ 0 := by
      intro z; apply h; exact BitVec.eq_of_toNat_eq (by simpa using z)
    simp [h, this, BitVec.toNat_udiv]

@[simp] theorem se12_0 : signExtend12 0#12 = 0#64 := by decide
@[simp] theorem se12_1 : signExtend12 1#12 = 1#64 := by decide
@[simp] theorem se12_2 : signExtend12 2#12 = 2#64 := by decide
@[simp] theorem se12_3 : signExtend12 3#12 = 3#64 := by decide
@[simp] theorem se12_4 : signExtend12 4#12 = 4#64 := by decide
@[simp] theorem se12_15 : signExtend12 15#12 = 15#64 := by decide
@[simp] theorem se12_29 : signExtend12 29#12 = 29#64 := by decide
@[simp] theorem se12_30 : signExtend12 30#12 = 30#64 := by decide
@[simp] theorem se12_48 : signExtend12 48#12 = 48#64 := by decide
@[simp] theorem se12_63 : signExtend12 63#12 = 63#64 := by decide
@[simp] theorem se12_483 : signExtend12 483#12 = 483#64 := by decide
@[simp] theorem se12_498 : signExtend12 498#12 = 498#64 := by decide


/-! Program counter arithmetic. -/

@[simp] theorem pcOf_succ (t : Nat) : pcOf t + 4#64 = pcOf (t + 1) := by
  unfold pcOf
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  simp
  omega

@[simp] theorem br_14 : pcOf 14 + signExtend13 112#13 = pcOf 42 := by decide
@[simp] theorem br_16 : pcOf 16 + signExtend13 88#13 = pcOf 38 := by decide
@[simp] theorem br_17 : pcOf 17 + signExtend13 48#13 = pcOf 29 := by decide
@[simp] theorem jal_28 : pcOf 28 + signExtend21 28#21 = pcOf 35 := by decide
@[simp] theorem jal_41 : pcOf 41 + signExtend21 2097044#21 = pcOf 14 := by decide
@[simp] theorem br_48 : pcOf 48 + signExtend13 160#13 = pcOf 88 := by decide
@[simp] theorem br_49 : pcOf 49 + signExtend13 88#13 = pcOf 71 := by decide
@[simp] theorem br_57 : pcOf 57 + signExtend13 48#13 = pcOf 69 := by decide
@[simp] theorem jal_68 : pcOf 68 + signExtend21 56#21 = pcOf 82 := by decide
@[simp] theorem jal_70 : pcOf 70 + signExtend21 48#21 = pcOf 82 := by decide
@[simp] theorem jal_87 : pcOf 87 + signExtend21 2096996#21 = pcOf 48 := by decide
@[simp] theorem br_90 : pcOf 90 + signExtend13 80#13 = pcOf 110 := by decide
@[simp] theorem jal_109 : pcOf 109 + signExtend21 2097076#21 = pcOf 90 := by decide

/-! Machine-state bookkeeping. -/

@[simp] theorem getReg_x0 (s : MachineState) : s.getReg .x0 = 0 := rfl
/-- Not an `rfl` lemma on purpose: a definitional use would make the kernel compare
symbolic program counters. -/
@[simp] theorem getByte_setPC (s : MachineState) (p a : Word) : (s.setPC p).getByte a = s.getByte a := by
  cases s; exact Eq.refl _
@[simp] theorem getByte_setReg (s : MachineState) (r : Reg) (v a : Word) :
    (s.setReg r v).getByte a = s.getByte a := by cases r <;> rfl
@[simp] theorem pc_setPC' (s : MachineState) (p : Word) : (s.setPC p).pc = p := rfl

attribute [local simp] Opening.getReg_setReg set_byte_read

@[simp] theorem getReg_setByte (s : MachineState) (a : Word) (v : Byte) (r : Reg) :
    (s.setByte a v).getReg r = s.getReg r := by
  simp [MachineState.setByte, Opening.getReg_setMem]

theorem truncate_w (v : Nat) : (BitVec.ofNat 64 v).setWidth 8 = BitVec.ofNat 8 v := by
  apply BitVec.eq_of_toNat_eq; simp

theorem run_append (s : MachineState) (a b : List Nat) : run s (a ++ b) = run (run s a) b := by
  simp [run, List.foldl_append]

theorem path_append (s : MachineState) : ∀ (a b : List Nat),
    PathOK s (a ++ b) ↔ PathOK s a ∧ PathOK (run s a) b
  | [], b => by simp [PathOK, run]
  | t :: a, b => by
    simp only [List.cons_append, PathOK]
    rw [path_append _ a b]
    simp [run, and_assoc]

/-! Registers and memory a path does not touch. -/

theorem exec_keeps (s : MachineState) (i : Instr) (r : Reg) (h : writesReg (.base i) r = false) :
    (execInstrBr s i).getReg r = s.getReg r := by
  cases i <;> simp only [writesReg, beq_eq_false_iff_ne, ne_eq, Bool.false_eq_true] at h <;>
    simp only [execInstrBr] <;> (try split) <;>
    simp [Opening.getReg_setReg, Opening.getReg_setMem, h, MachineState.setByte, MachineState.setHalfword,
      MachineState.setWord32]

def writesAny (ts : List Nat) (r : Reg) : Bool := ts.any fun t => writesReg (.base (instrAt t)) r

theorem run_keeps (r : Reg) : ∀ (ts : List Nat) (s : MachineState), writesAny ts r = false →
    (run s ts).getReg r = s.getReg r
  | [], s, _ => rfl
  | t :: ts, s, h => by
    simp only [writesAny, List.any_cons, Bool.or_eq_false_iff] at h
    simp only [run, List.foldl_cons]
    exact (run_keeps r ts _ h.2).trans (exec_keeps s _ r h.1)

/-- No store. -/
def loadsOnly : Instr → Bool
  | .SD .. | .SW .. | .SH .. | .SB .. | .CSRS .. => false
  | _ => true

theorem mem_setReg' (s : MachineState) (r : Reg) (v : Word) : (s.setReg r v).mem = s.mem := by
  cases r <;> rfl

theorem exec_mem (s : MachineState) (i : Instr) (h : loadsOnly i = true) :
    (execInstrBr s i).mem = s.mem := by
  cases i <;> simp only [loadsOnly] at h <;> simp only [execInstrBr] <;> (try split) <;>
    simp [mem_setReg', MachineState.setPC] at *

theorem run_mem : ∀ (ts : List Nat) (s : MachineState), (ts.all fun t => loadsOnly (instrAt t)) = true →
    (run s ts).mem = s.mem
  | [], s, _ => rfl
  | t :: ts, s, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [run, List.foldl_cons]
    exact (run_mem ts _ h.2).trans (exec_mem s _ h.1)

theorem getByte_of_mem {s t : MachineState} (h : s.mem = t.mem) (a : Word) : s.getByte a = t.getByte a := by
  simp only [MachineState.getByte, MachineState.getMem, h]

/-! Word arithmetic on `BitVec.ofNat` values. -/

theorem accessValid_of (a : Word) (h : a.toNat + 1 ≤ 68719476736) : accessValid a 1 = true := by
  simp [accessValid, rangeValid, MEMORY_BYTES, Nat.mod_one]
  omega

theorem w_add (a c : Nat) : BitVec.ofNat 64 a + BitVec.ofNat 64 c = BitVec.ofNat 64 (a + c) := by
  apply BitVec.eq_of_toNat_eq; simp
theorem w_mul (a c : Nat) : BitVec.ofNat 64 a * BitVec.ofNat 64 c = BitVec.ofNat 64 (a * c) := by
  apply BitVec.eq_of_toNat_eq; simp [Nat.mul_mod]
theorem w_sub (a c : Nat) (h : c ≤ a) (ha : a < 2^64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 c = BitVec.ofNat 64 (a - c) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub]; omega
theorem w_divu (a c : Nat) (hc : 0 < c) (ha : a < 2^64) (hc' : c < 2^64) :
    rv64_divu (BitVec.ofNat 64 a) (BitVec.ofNat 64 c) = BitVec.ofNat 64 (a / c) := by
  apply BitVec.eq_of_toNat_eq
  rw [divu_toNat]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hc']
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
    Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self a c) ha)]
theorem w_shl (a c : Nat) : BitVec.ofNat 64 a <<< c = BitVec.ofNat 64 (a * 2^c) := by
  apply BitVec.eq_of_toNat_eq; simp [Nat.shiftLeft_eq, Nat.mul_mod]
theorem w_shr (a c : Nat) (ha : a < 2^64) : BitVec.ofNat 64 a >>> c = BitVec.ofNat 64 (a / 2^c) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : a % 18446744073709551616 = a := Nat.mod_eq_of_lt ha
  have h2 : a / 2 ^ c % 18446744073709551616 = a / 2 ^ c :=
    Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) ha)
  simp [Nat.shiftRight_eq_div_pow, h1, h2]
theorem toNat_w (a : Nat) (ha : a < 2^64) : (BitVec.ofNat 64 a).toNat = a := by
  simp; omega
theorem w_inj (a c : Nat) (ha : a < 2^64) (hc : c < 2^64) :
    BitVec.ofNat 64 a = BitVec.ofNat 64 c ↔ a = c := by
  constructor
  · intro e; have := congrArg BitVec.toNat e; rwa [toNat_w a ha, toNat_w c hc] at this
  · intro e; rw [e]

theorem beq_ofNat (a c : Nat) (ha : a < 2^64) (hc : c < 2^64) :
    (BitVec.ofNat 64 a == BitVec.ofNat 64 c) = decide (a = c) := by
  by_cases h : a = c
  · subst h; simp
  · have : BitVec.ofNat 64 a ≠ BitVec.ofNat 64 c := fun e => h ((w_inj a c ha hc).1 e)
    simp [h, this]

theorem ult_ofNat (a c : Nat) (ha : a < 2^64) (hc : c < 2^64) :
    BitVec.ult (BitVec.ofNat 64 a) (BitVec.ofNat 64 c) = decide (a < c) := by
  rw [BitVec.ult_eq_decide]
  simp
  omega

/-! Extending a written byte region by one byte. -/

theorem extend_region (s' s : MachineState) (lo i : Nat) (f : Nat → Byte) (old : Word → Byte)
    (v : Byte) (fit : lo + i < 2^64)
    (hs : ∀ a, s.getByte a = if lo ≤ a.toNat ∧ a.toNat < lo + i then f (a.toNat - lo) else old a)
    (hs' : ∀ a, s'.getByte a = if a = BitVec.ofNat 64 (lo + i) then v else s.getByte a)
    (hv : v = f i) :
    ∀ a, s'.getByte a = if lo ≤ a.toNat ∧ a.toNat < lo + (i + 1) then f (a.toNat - lo) else old a := by
  intro a
  rw [hs', hs]
  by_cases e : a = BitVec.ofNat 64 (lo + i)
  · have : a.toNat = lo + i := by rw [e, toNat_w _ fit]
    rw [if_pos e, if_pos (by omega), hv, show a.toNat - lo = i by omega]
  · have : a.toNat ≠ lo + i := by
      intro h; apply e; apply BitVec.eq_of_toNat_eq; rw [h, toNat_w _ fit]
    rw [if_neg e]
    by_cases r : lo ≤ a.toNat ∧ a.toNat < lo + i
    · rw [if_pos r, if_pos (by omega)]
    · rw [if_neg r, if_neg (by omega)]

/-! The proof buffer and the scratch area. -/

def scratch (base : Nat) : Nat := base + 8589934592
/-- Unpacked proof capacity: 498 * 2^24 + 30 * 256. -/
def capacityBytes : Nat := 8355061248
def count (k b : Nat) : Nat := 15*k + b
def rounded (k b : Nat) : Nat := 4 * ((count k b + 3) / 4)

/-- Scratch byte `i` after the gather loop. -/
def gathered (P : List Byte) (k b i : Nat) : Byte :=
  if i < count k b then BitVec.ofNat 8 (ProofCodec.remainderBits P k i) else 0

/-- The unpacked proof bytes. -/
def Source (k b base : Nat) (P : List Byte) (s0 : MachineState) : Prop :=
  ∀ a : Word, base ≤ a.toNat → a.toNat < base + (498*k + 30*b) → s0.getByte a = P.getD (a.toNat - base) 0

structure Common (k base : Nat) (s : MachineState) : Prop where
  x5 : s.getReg .x5 = 1
  x10 : s.getReg .x10 = 0
  x16 : s.getReg .x16 = BitVec.ofNat 64 k
  x20 : s.getReg .x20 = BitVec.ofNat 64 base

structure GatherRegs (k b base : Nat) (s : MachineState) : Prop extends Common k base s where
  x7 : s.getReg .x7 = BitVec.ofNat 64 (48*k)
  x8 : s.getReg .x8 = BitVec.ofNat 64 (count k b)
  x9 : s.getReg .x9 = BitVec.ofNat 64 (15*k)
  x18 : s.getReg .x18 = BitVec.ofNat 64 (scratch base)
  x19 : s.getReg .x19 = BitVec.ofNat 64 (rounded k b)

theorem GatherRegs.keep {k b base : Nat} {s : MachineState} (regs : GatherRegs k b base s)
    (ts : List Nat) (h : ([.x5, .x10, .x16, .x20, .x7, .x8, .x9, .x18, .x19] : List Reg).all
      (fun r => !writesAny ts r) = true) : GatherRegs k b base (run s ts) := by
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨h5, h10, h16, h20, h7, h8, h9, h18, h19⟩ := h
  exact ⟨⟨(run_keeps _ ts s h5).trans regs.x5, (run_keeps _ ts s h10).trans regs.x10,
    (run_keeps _ ts s h16).trans regs.x16, (run_keeps _ ts s h20).trans regs.x20⟩,
    (run_keeps _ ts s h7).trans regs.x7, (run_keeps _ ts s h8).trans regs.x8,
    (run_keeps _ ts s h9).trans regs.x9, (run_keeps _ ts s h18).trans regs.x18,
    (run_keeps _ ts s h19).trans regs.x19⟩

structure Gather (k b base : Nat) (P : List Byte) (s0 : MachineState) (j : Nat) (s : MachineState) : Prop where
  regs : GatherRegs k b base s
  pc : s.pc = pcOf 14
  x22 : s.getReg .x22 = BitVec.ofNat 64 j
  bound : j ≤ rounded k b
  mem : ∀ a : Word, s.getByte a =
    if scratch base ≤ a.toNat ∧ a.toNat < scratch base + j then gathered P k b (a.toNat - scratch base)
    else s0.getByte a

/-! ### Gather loop: the six stored bits of each digest go to the scratch area. -/


set_option maxHeartbeats 400000 in
theorem gather_store (k b base : Nat) (P : List Byte) (s0 u : MachineState) (j v : Nat)
    (regs : GatherRegs k b base u) (pc : u.pc = pcOf 38) (x22 : u.getReg .x22 = BitVec.ofNat 64 j)
    (x23 : u.getReg .x23 = BitVec.ofNat 64 v) (hj : j < rounded k b)
    (fits : 498*k + 30*b ≤ capacityBytes) (room : base + 2^34 ≤ 2^36)
    (mem : ∀ a : Word, u.getByte a =
      if scratch base ≤ a.toNat ∧ a.toNat < scratch base + j then gathered P k b (a.toNat - scratch base)
      else s0.getByte a)
    (hv : gathered P k b j = BitVec.ofNat 8 v) :
    PathOK u [38, 39, 40, 41] ∧ Gather k b base P s0 (j + 1) (run u [38, 39, 40, 41]) := by
  have hj' := hj
  simp only [rounded, count, capacityBytes] at hj' fits
  have addr : u.getReg .x18 + u.getReg .x22 = BitVec.ofNat 64 (scratch base + j) := by
    rw [regs.x18, x22, w_add]
  have fit : scratch base + j < 2^64 := by unfold scratch; omega
  constructor
  · simp [PathOK, execInstrBr, pc, ordinaryInstr, memoryArgumentsValid, memAccess, addr]
    apply accessValid_of
    rw [toNat_w _ fit]
    unfold scratch; omega
  · refine ⟨regs.keep _ (by decide), ?_, ?_, by omega, ?_⟩
    · simp [run, execInstrBr, pc]
    · simp [run, execInstrBr, x22, w_add]
    · apply extend_region _ u _ _ _ _ (BitVec.ofNat 8 v) fit mem _ hv.symm
      intro a
      simp [run, execInstrBr, addr, x23, truncate_w]

theorem byte_and63 (x : Byte) : x.setWidth 64 &&& 63#64 = BitVec.ofNat 64 (x.toNat % 64) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_and]
  have := x.isLt
  have h : (63 : Nat) = 2^6 - 1 := rfl
  rw [h, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem Gather.read {k b base : Nat} {P : List Byte} {s0 s : MachineState} {j : Nat}
    (inv : Gather k b base P s0 j s) (src : Source k b base P s0)
    (fits : 498*k + 30*b ≤ capacityBytes) (a : Word) (lo : base ≤ a.toNat)
    (hi : a.toNat < base + (498*k + 30*b)) : s.getByte a = P.getD (a.toNat - base) 0 := by
  rw [inv.mem, if_neg (by unfold scratch capacityBytes at *; omega), src a lo hi]

def pathA : List Nat := [14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,35,36,37]

set_option maxHeartbeats 800000 in
theorem gather_digest (k b base : Nat) (P : List Byte) (s0 s : MachineState) (j : Nat)
    (inv : Gather k b base P s0 j s) (src : Source k b base P s0) (hj : j < rounded k b) (hd : j < 15*k)
    (fits : 498*k + 30*b ≤ capacityBytes) (room : base + 2^34 ≤ 2^36) :
    PathOK s pathA ∧ (run s pathA).pc = pcOf 38 ∧
      (run s pathA).getReg .x23 = BitVec.ofNat 64 (ProofCodec.remainderBits P k j) := by
  have hj' := hj
  have fits' := fits
  simp only [rounded, count, capacityBytes] at hj' fits'
  have c1 := beq_ofNat j (rounded k b) (by omega) (by unfold rounded count; omega)
  have c2 := ult_ofNat j (count k b) (by omega) (by unfold count; omega)
  have c3 := ult_ofNat j (15*k) (by omega) (by omega)
  have regs := inv.regs
  have ne1 : BitVec.ofNat 64 j ≠ BitVec.ofNat 64 (rounded k b) := by
    rw [Ne, w_inj _ _ (by omega) (by unfold rounded count; omega)]; omega
  refine ⟨?_, ?_, ?_⟩
  · simp (disch := omega) [PathOK, pathA, execInstrBr, inv.pc, inv.x22, regs.x19, regs.x8, regs.x9,
      regs.x20, c1, c2, c3, ne1, ordinaryInstr, memoryArgumentsValid, memAccess,
      show j ≠ rounded k b by omega, show j < count k b by unfold count; omega, hd, w_add, w_mul, w_sub, w_divu]
    apply accessValid_of
    rw [toNat_w _ (by omega)]
    omega
  · simp [run, pathA, execInstrBr, inv.pc, inv.x22, regs.x19, regs.x8, regs.x9, c1, c2, c3, ne1,
      show j ≠ rounded k b by omega, show j < count k b by unfold count; omega, hd]
  · simp (disch := omega) [run, pathA, execInstrBr, inv.pc, inv.x22, regs.x19, regs.x8, regs.x9,
      regs.x20, c1, c2, c3, ne1, show j ≠ rounded k b by omega, show j < count k b by unfold count; omega, hd,
      w_add, w_mul, w_sub, w_divu]
    have q1 : j / 15 < k := by omega
    have q2 : j - j / 15 * 15 < 15 := by omega
    have e1 : (j / 15 * 498 + 48 + (j - j / 15 * 15) * 30 + base + 29) < 2^64 := by omega
    rw [inv.read src fits _ (by rw [toNat_w _ e1]; omega) (by rw [toNat_w _ e1]; omega), byte_and63,
      toNat_w _ e1]
    unfold ProofCodec.remainderBits ProofCodec.unpackedDigest
    rw [if_pos hd, show j / 15 * 498 + 48 + (j - j / 15 * 15) * 30 + base + 29 - base =
      498 * (j / 15) + 48 + 30 * (j % 15) + 29 by omega]

def pathB : List Nat := [14,15,16,17,29,30,31,32,33,34,35,36,37]

set_option maxHeartbeats 800000 in
theorem gather_footer (k b base : Nat) (P : List Byte) (s0 s : MachineState) (j : Nat)
    (inv : Gather k b base P s0 j s) (src : Source k b base P s0) (hj : j < count k b) (hd : 15*k ≤ j)
    (fits : 498*k + 30*b ≤ capacityBytes) (room : base + 2^34 ≤ 2^36) :
    PathOK s pathB ∧ (run s pathB).pc = pcOf 38 ∧
      (run s pathB).getReg .x23 = BitVec.ofNat 64 (ProofCodec.remainderBits P k j) := by
  have hj' := hj
  have fits' := fits
  simp only [count, capacityBytes] at hj' fits'
  have c2 := ult_ofNat j (count k b) (by omega) (by unfold count; omega)
  have c3 := ult_ofNat j (15*k) (by omega) (by omega)
  have regs := inv.regs
  have ne1 : BitVec.ofNat 64 j ≠ BitVec.ofNat 64 (rounded k b) := by
    rw [Ne, w_inj _ _ (by omega) (by unfold rounded count; omega)]; unfold rounded count; omega
  have nlt : ¬ j < 15 * k := by omega
  refine ⟨?_, ?_, ?_⟩
  · simp (disch := omega) [PathOK, pathB, execInstrBr, inv.pc, inv.x22, regs.x19, regs.x8, regs.x9,
      regs.x20, regs.x16, c2, c3, ne1, ordinaryInstr, memoryArgumentsValid, memAccess,
      show j < count k b by unfold count; omega, nlt, w_add, w_mul, w_sub, w_divu]
    apply accessValid_of
    rw [toNat_w _ (by omega)]
    omega
  · simp [run, pathB, execInstrBr, inv.pc, inv.x22, regs.x19, regs.x8, regs.x9, c2, c3, ne1, nlt, hj]
  · simp (disch := omega) [run, pathB, execInstrBr, inv.pc, inv.x22, regs.x19, regs.x8, regs.x9,
      regs.x20, regs.x16, c2, c3, ne1, nlt, hj, w_add, w_mul, w_sub, w_divu]
    have e1 : k * 498 + (j - 15 * k) * 30 + base + 29 < 2^64 := by omega
    rw [inv.read src fits _ (by rw [toNat_w _ e1]; omega) (by rw [toNat_w _ e1]; omega), byte_and63,
      toNat_w _ e1]
    unfold ProofCodec.remainderBits ProofCodec.unpackedDigest
    rw [if_neg nlt, show k * 498 + (j - 15 * k) * 30 + base + 29 - base = 498 * k + 30 * (j - 15 * k) + 29 by omega]

def pathC : List Nat := [14,15,16]

set_option maxHeartbeats 800000 in
theorem gather_pad (k b base : Nat) (P : List Byte) (s0 s : MachineState) (j : Nat)
    (inv : Gather k b base P s0 j s) (hj : j < rounded k b) (hd : count k b ≤ j)
    (fits : 498*k + 30*b ≤ capacityBytes) :
    PathOK s pathC ∧ (run s pathC).pc = pcOf 38 ∧ (run s pathC).getReg .x23 = BitVec.ofNat 64 0 := by
  have hj' := hj
  have fits' := fits
  simp only [rounded, count, capacityBytes] at hj' fits' hd
  have c2 := ult_ofNat j (count k b) (by omega) (by unfold count; omega)
  have regs := inv.regs
  have ne1 : BitVec.ofNat 64 j ≠ BitVec.ofNat 64 (rounded k b) := by
    rw [Ne, w_inj _ _ (by omega) (by unfold rounded count; omega)]; unfold rounded count; omega
  have nlt : ¬ j < count k b := by unfold count; omega
  refine ⟨?_, ?_, ?_⟩
  · simp [PathOK, pathC, execInstrBr, inv.pc, inv.x22, regs.x19, regs.x8, c2, ne1, nlt, ordinaryInstr,
      memoryArgumentsValid, memAccess]
  · simp [run, pathC, execInstrBr, inv.pc, inv.x22, regs.x19, regs.x8, c2, ne1, nlt]
  · simp [run, pathC, execInstrBr, inv.pc, inv.x22, regs.x19, regs.x8, c2, ne1, nlt]


theorem runs_loop (Inv : Nat → MachineState → Prop) (N : Nat) (st cy : Nat → Nat)
    (body : ∀ j < N, ∀ s, Inv j s → ∃ s', Inv (j + 1) s' ∧ Runs s s' (st j) (cy j)) (d : Nat) :
    ∀ j s, j + d = N → Inv j s →
      ∃ s', Inv N s' ∧ Runs s s' (∑ i ∈ Finset.Ico j N, st i) (∑ i ∈ Finset.Ico j N, cy i) := by
  induction d with
  | zero =>
    intro j s h inv
    subst h
    exact ⟨s, inv, by simpa using Runs.refl s⟩
  | succ d ih =>
    intro j s h inv
    obtain ⟨s1, inv1, run1⟩ := body j (by omega) s inv
    obtain ⟨s2, inv2, run2⟩ := ih (j + 1) s1 (by omega) inv1
    refine ⟨s2, inv2, ?_⟩
    have hlt : j < N := by omega
    rw [Finset.sum_eq_sum_Ico_succ_bot hlt st, Finset.sum_eq_sum_Ico_succ_bot hlt cy]
    exact run1.trans run2

def gatherSteps (k b j : Nat) : Nat := if j < 15*k then 22 else if j < count k b then 17 else 7
def gatherCycles (k b j : Nat) : Nat := if j < 15*k then 34 else if j < count k b then 23 else 7

theorem gather_iter (k b base : Nat) (P : List Byte) (s0 s : MachineState) (j : Nat)
    (inv : Gather k b base P s0 j s) (src : Source k b base P s0) (hj : j < rounded k b)
    (fits : 498*k + 30*b ≤ capacityBytes) (room : base + 2^34 ≤ 2^36) :
    ∃ s', Gather k b base P s0 (j + 1) s' ∧ Runs s s' (gatherSteps k b j) (gatherCycles k b j) := by
  have mem0 (ts : List Nat) (h : (ts.all fun t => loadsOnly (instrAt t)) = true) (a : Word) :
      (run s ts).getByte a = _ := (getByte_of_mem (run_mem ts s h) a).trans (inv.mem a)
  have finish (head : List Nat) (v : Nat) (hh : (head.all fun t => loadsOnly (instrAt t)) = true)
      (keep : ([.x5, .x10, .x16, .x20, .x7, .x8, .x9, .x18, .x19] : List Reg).all
        (fun r => !writesAny head r) = true) (k22 : writesAny head .x22 = false)
      (ok : PathOK s head) (pc : (run s head).pc = pcOf 38)
      (x23 : (run s head).getReg .x23 = BitVec.ofNat 64 v) (hv : gathered P k b j = BitVec.ofNat 8 v) :
      PathOK s (head ++ [38, 39, 40, 41]) ∧
        Gather k b base P s0 (j + 1) (run s (head ++ [38, 39, 40, 41])) := by
    have st := gather_store k b base P s0 (run s head) j v (inv.regs.keep head keep) pc
      ((run_keeps _ head s k22).trans inv.x22) x23 hj fits room (mem0 head hh) hv
    rw [path_append, run_append]
    exact ⟨⟨ok, st.1⟩, st.2⟩
  by_cases hd : j < 15*k
  · obtain ⟨ok, pc, x23⟩ := gather_digest k b base P s0 s j inv src hj hd fits room
    have := finish pathA _ (by decide) (by decide) (by decide) ok pc x23
      (by rw [gathered, if_pos (by unfold count; omega)])
    refine ⟨_, this.2, (runs_path _ s this.1).cast ?_ ?_⟩
    · simp only [gatherSteps, if_pos hd]; rfl
    · simp only [gatherCycles, if_pos hd]; decide
  by_cases hn : j < count k b
  · obtain ⟨ok, pc, x23⟩ := gather_footer k b base P s0 s j inv src hn (by omega) fits room
    have := finish pathB _ (by decide) (by decide) (by decide) ok pc x23
      (by rw [gathered, if_pos hn])
    refine ⟨_, this.2, (runs_path _ s this.1).cast ?_ ?_⟩
    · simp only [gatherSteps, if_neg hd, if_pos hn]; rfl
    · simp only [gatherCycles, if_neg hd, if_pos hn]; decide
  · obtain ⟨ok, pc, x23⟩ := gather_pad k b base P s0 s j inv hj (by omega) fits
    have := finish pathC _ (by decide) (by decide) (by decide) ok pc x23
      (by rw [gathered, if_neg hn]; rfl)
    refine ⟨_, this.2, (runs_path _ s this.1).cast ?_ ?_⟩
    · simp only [gatherSteps, if_neg hd, if_neg hn]; rfl
    · simp only [gatherCycles, if_neg hd, if_neg hn]; decide

theorem gather_steps_sum (k b N : Nat) : ∑ i ∈ Finset.range N, gatherSteps k b i =
    22 * min N (15*k) + 17 * (min N (count k b) - min N (15*k)) + 7 * (N - min N (count k b)) := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; unfold gatherSteps count; split_ifs <;> omega

theorem gather_cycles_sum (k b N : Nat) : ∑ i ∈ Finset.range N, gatherCycles k b i =
    34 * min N (15*k) + 23 * (min N (count k b) - min N (15*k)) + 7 * (N - min N (count k b)) := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; unfold gatherCycles count; split_ifs <;> omega

theorem gather_loop (k b base : Nat) (P : List Byte) (s0 s : MachineState)
    (inv : Gather k b base P s0 0 s) (src : Source k b base P s0)
    (fits : 498*k + 30*b ≤ capacityBytes) (room : base + 2^34 ≤ 2^36) :
    ∃ s', Gather k b base P s0 (rounded k b) s' ∧
      Runs s s' (330*k + 17*b + 7*(rounded k b - count k b)) (510*k + 23*b + 7*(rounded k b - count k b)) := by
  obtain ⟨s', inv', run⟩ := runs_loop (fun j s => Gather k b base P s0 j s) (rounded k b)
    (gatherSteps k b) (gatherCycles k b)
    (fun j hj s inv => gather_iter k b base P s0 s j inv src hj fits room) (rounded k b) 0 s (by omega) inv
  refine ⟨s', inv', run.cast ?_ ?_⟩
  · rw [← Finset.range_eq_Ico, gather_steps_sum]; unfold rounded count; omega
  · rw [← Finset.range_eq_Ico, gather_cycles_sum]; unfold rounded count; omega


/-! ### Pack loop: body bytes move forward in place. -/

def bodyLen (k b : Nat) : Nat := 48*k + 29*count k b

theorem packed_source_bounds (k b i : Nat) (hi : i < bodyLen k b) :
    i ≤ ProofCodec.packedSource k i ∧ ProofCodec.packedSource k i < 498*k + 30*b := by
  unfold bodyLen count at hi
  unfold ProofCodec.packedSource
  split_ifs with h1 h2
  · omega
  · omega
  · omega

/-- What the body loop reads: the unpacked proof bytes, still in place. -/
def Unpacked (k b base : Nat) (P : List Byte) (s1 : MachineState) : Prop :=
  ∀ a : Word, base ≤ a.toNat → a.toNat < base + (498*k + 30*b) → s1.getByte a = P.getD (a.toNat - base) 0

structure PackRegs (k b base : Nat) (s : MachineState) : Prop extends Common k base s where
  x18 : s.getReg .x18 = BitVec.ofNat 64 (scratch base)
  x19 : s.getReg .x19 = BitVec.ofNat 64 (rounded k b)
  x27 : s.getReg .x27 = BitVec.ofNat 64 (bodyLen k b)

theorem PackRegs.keep {k b base : Nat} {s : MachineState} (regs : PackRegs k b base s)
    (ts : List Nat) (h : ([.x5, .x10, .x16, .x20, .x18, .x19, .x27] : List Reg).all
      (fun r => !writesAny ts r) = true) : PackRegs k b base (run s ts) := by
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨h5, h10, h16, h20, h18, h19, h27⟩ := h
  exact ⟨⟨(run_keeps _ ts s h5).trans regs.x5, (run_keeps _ ts s h10).trans regs.x10,
    (run_keeps _ ts s h16).trans regs.x16, (run_keeps _ ts s h20).trans regs.x20⟩,
    (run_keeps _ ts s h18).trans regs.x18, (run_keeps _ ts s h19).trans regs.x19,
    (run_keeps _ ts s h27).trans regs.x27⟩

structure PackBody (k b base : Nat) (P : List Byte) (s1 : MachineState) (i : Nat) (s : MachineState) : Prop where
  regs : PackRegs k b base s
  x29 : s.getReg .x29 = BitVec.ofNat 64 (483*k)
  pc : s.pc = pcOf 48
  x22 : s.getReg .x22 = BitVec.ofNat 64 i
  bound : i ≤ bodyLen k b
  mem : ∀ a : Word, s.getByte a =
    if base ≤ a.toNat ∧ a.toNat < base + i then P.getD (ProofCodec.packedSource k (a.toNat - base)) 0
    else s1.getByte a

def packTail : List Nat := [82, 83, 84, 85, 86, 87]

set_option maxHeartbeats 800000 in
theorem pack_store (k b base : Nat) (P : List Byte) (s1 u : MachineState) (i : Nat)
    (regs : PackRegs k b base u) (x29 : u.getReg .x29 = BitVec.ofNat 64 (483*k)) (pc : u.pc = pcOf 82)
    (x22 : u.getReg .x22 = BitVec.ofNat 64 i)
    (x25 : u.getReg .x25 = BitVec.ofNat 64 (ProofCodec.packedSource k i)) (hi : i < bodyLen k b)
    (fits : 498*k + 30*b ≤ capacityBytes) (room : base + 2^34 ≤ 2^36) (src : Unpacked k b base P s1)
    (mem : ∀ a : Word, u.getByte a =
      if base ≤ a.toNat ∧ a.toNat < base + i then P.getD (ProofCodec.packedSource k (a.toNat - base)) 0
      else s1.getByte a) :
    PathOK u packTail ∧ PackBody k b base P s1 (i + 1) (run u packTail) := by
  have ⟨lo, hi'⟩ := packed_source_bounds k b i hi
  have hi2 := hi
  have fits' := fits
  unfold bodyLen count at hi2
  unfold capacityBytes at fits'
  have e1 : ProofCodec.packedSource k i + base < 2^64 := by omega
  have e2 : i + base < 2^64 := by omega
  have rd : u.getByte (BitVec.ofNat 64 (ProofCodec.packedSource k i + base)) =
      P.getD (ProofCodec.packedSource k i) 0 := by
    rw [mem, toNat_w _ e1, if_neg (by omega), src _ (by rw [toNat_w _ e1]; omega)
      (by rw [toNat_w _ e1]; omega), toNat_w _ e1, Nat.add_sub_cancel]
  constructor
  · simp [PathOK, packTail, execInstrBr, pc, ordinaryInstr, memoryArgumentsValid, memAccess, x25,
      x22, regs.x20, w_add]
    constructor <;> apply accessValid_of <;> rw [toNat_w _ (by omega)] <;> omega
  · refine ⟨regs.keep _ (by decide), (run_keeps _ _ u (by decide)).trans x29, ?_, ?_, by omega, ?_⟩
    · simp [run, packTail, execInstrBr, pc]
    · simp [run, packTail, execInstrBr, x22, w_add]
    · intro a
      have st := extend_region (run u packTail) u base i (fun p => P.getD (ProofCodec.packedSource k p) 0)
        s1.getByte (P.getD (ProofCodec.packedSource k i) 0) (by omega) mem
      rw [st]
      · intro a
        simp [run, packTail, execInstrBr, x25, x22, regs.x20, w_add, rd, Nat.add_comm i base]
      · rfl

def pathH : List Nat := [48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 69, 70]
def pathD : List Nat := [48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68]
def pathF : List Nat := [48, 49, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81]

set_option maxHeartbeats 800000 in
theorem pack_head (k b base : Nat) (P : List Byte) (s1 s : MachineState) (i : Nat)
    (inv : PackBody k b base P s1 i s) (hi : i < bodyLen k b) (hr : i < 483*k) (ho : i % 483 < 48)
    (fits : 498*k + 30*b ≤ capacityBytes) :
    PathOK s pathH ∧ (run s pathH).pc = pcOf 82 ∧
      (run s pathH).getReg .x25 = BitVec.ofNat 64 (ProofCodec.packedSource k i) := by
  have hi2 := hi
  have fits' := fits
  unfold bodyLen count at hi2
  unfold capacityBytes at fits'
  have regs := inv.regs
  have ne1 : BitVec.ofNat 64 i ≠ BitVec.ofNat 64 (bodyLen k b) := by
    rw [Ne, w_inj _ _ (by omega) (by unfold bodyLen count; omega)]; omega
  have ho' : i - i / 483 * 483 < 48 := by omega
  refine ⟨?_, ?_, ?_⟩
  · simp (disch := omega) [PathOK, pathH, execInstrBr, inv.pc, inv.x22, regs.x27, inv.x29, ne1,
      ordinaryInstr, memoryArgumentsValid, memAccess, w_add, w_mul, w_sub, w_divu, ult_ofNat, hr, ho']
  · simp (disch := omega) [run, pathH, execInstrBr, inv.pc, inv.x22, regs.x27, inv.x29, ne1,
      w_add, w_mul, w_sub, w_divu, ult_ofNat, hr, ho']
  · simp (disch := omega) [run, pathH, execInstrBr, inv.pc, inv.x22, regs.x27, inv.x29, ne1,
      w_add, w_mul, w_sub, w_divu, ult_ofNat, hr, ho']
    unfold ProofCodec.packedSource
    rw [if_pos hr, if_pos ho]
    congr 1; omega

set_option maxHeartbeats 800000 in
theorem pack_digest (k b base : Nat) (P : List Byte) (s1 s : MachineState) (i : Nat)
    (inv : PackBody k b base P s1 i s) (hi : i < bodyLen k b) (hr : i < 483*k) (ho : ¬ i % 483 < 48)
    (fits : 498*k + 30*b ≤ capacityBytes) :
    PathOK s pathD ∧ (run s pathD).pc = pcOf 82 ∧
      (run s pathD).getReg .x25 = BitVec.ofNat 64 (ProofCodec.packedSource k i) := by
  have hi2 := hi
  have fits' := fits
  unfold bodyLen count at hi2
  unfold capacityBytes at fits'
  have regs := inv.regs
  have ne1 : BitVec.ofNat 64 i ≠ BitVec.ofNat 64 (bodyLen k b) := by
    rw [Ne, w_inj _ _ (by omega) (by unfold bodyLen count; omega)]; omega
  have ho' : ¬ i - i / 483 * 483 < 48 := by omega
  refine ⟨?_, ?_, ?_⟩
  · simp (disch := omega) [PathOK, pathD, execInstrBr, inv.pc, inv.x22, regs.x27, inv.x29, ne1,
      ordinaryInstr, memoryArgumentsValid, memAccess, w_add, w_mul, w_sub, w_divu, ult_ofNat, hr, ho']
  · simp (disch := omega) [run, pathD, execInstrBr, inv.pc, inv.x22, regs.x27, inv.x29, ne1,
      w_add, w_mul, w_sub, w_divu, ult_ofNat, hr, ho']
  · simp (disch := omega) [run, pathD, execInstrBr, inv.pc, inv.x22, regs.x27, inv.x29, ne1,
      w_add, w_mul, w_sub, w_divu, ult_ofNat, hr, ho']
    unfold ProofCodec.packedSource
    rw [if_pos hr, if_neg ho]
    congr 1; omega

set_option maxHeartbeats 800000 in
theorem pack_footer (k b base : Nat) (P : List Byte) (s1 s : MachineState) (i : Nat)
    (inv : PackBody k b base P s1 i s) (hi : i < bodyLen k b) (hr : ¬ i < 483*k)
    (fits : 498*k + 30*b ≤ capacityBytes) :
    PathOK s pathF ∧ (run s pathF).pc = pcOf 82 ∧
      (run s pathF).getReg .x25 = BitVec.ofNat 64 (ProofCodec.packedSource k i) := by
  have hi2 := hi
  have fits' := fits
  unfold bodyLen count at hi2
  unfold capacityBytes at fits'
  have regs := inv.regs
  have ne1 : BitVec.ofNat 64 i ≠ BitVec.ofNat 64 (bodyLen k b) := by
    rw [Ne, w_inj _ _ (by omega) (by unfold bodyLen count; omega)]; omega
  refine ⟨?_, ?_, ?_⟩
  · simp (disch := omega) [PathOK, pathF, execInstrBr, inv.pc, inv.x22, regs.x27, inv.x29, ne1,
      regs.x16, ordinaryInstr, memoryArgumentsValid, memAccess, w_add, w_mul, w_sub, w_divu, ult_ofNat, hr]
  · simp (disch := omega) [run, pathF, execInstrBr, inv.pc, inv.x22, regs.x27, inv.x29, ne1,
      regs.x16, w_add, w_mul, w_sub, w_divu, ult_ofNat, hr]
  · simp (disch := omega) [run, pathF, execInstrBr, inv.pc, inv.x22, regs.x27, inv.x29, ne1,
      regs.x16, w_add, w_mul, w_sub, w_divu, ult_ofNat, hr]
    unfold ProofCodec.packedSource
    rw [if_neg hr]
    congr 1; omega

def packSteps (k i : Nat) : Nat := if i < 483*k then (if i % 483 < 48 then 18 else 27) else 19
def packCycles (k i : Nat) : Nat := if i < 483*k then (if i % 483 < 48 then 27 else 45) else 31

theorem pack_iter (k b base : Nat) (P : List Byte) (s1 s : MachineState) (i : Nat)
    (inv : PackBody k b base P s1 i s) (src : Unpacked k b base P s1) (hi : i < bodyLen k b)
    (fits : 498*k + 30*b ≤ capacityBytes) (room : base + 2^34 ≤ 2^36) :
    ∃ s', PackBody k b base P s1 (i + 1) s' ∧ Runs s s' (packSteps k i) (packCycles k i) := by
  have finish (head : List Nat) (hh : (head.all fun t => loadsOnly (instrAt t)) = true)
      (keep : ([.x5, .x10, .x16, .x20, .x18, .x19, .x27] : List Reg).all
        (fun r => !writesAny head r) = true) (k22 : writesAny head .x22 = false)
      (k29 : writesAny head .x29 = false)
      (ok : PathOK s head) (pc : (run s head).pc = pcOf 82)
      (x25 : (run s head).getReg .x25 = BitVec.ofNat 64 (ProofCodec.packedSource k i)) :
      PathOK s (head ++ packTail) ∧ PackBody k b base P s1 (i + 1) (run s (head ++ packTail)) := by
    have st := pack_store k b base P s1 (run s head) i (inv.regs.keep head keep)
      ((run_keeps _ head s k29).trans inv.x29) pc ((run_keeps _ head s k22).trans inv.x22) x25 hi fits room src
      (fun a => (getByte_of_mem (run_mem head s hh) a).trans (inv.mem a))
    rw [path_append, run_append]
    exact ⟨⟨ok, st.1⟩, st.2⟩
  by_cases hr : i < 483*k
  · by_cases ho : i % 483 < 48
    · obtain ⟨ok, pc, x25⟩ := pack_head k b base P s1 s i inv hi hr ho fits
      have := finish pathH (by decide) (by decide) (by decide) (by decide) ok pc x25
      refine ⟨_, this.2, (runs_path _ s this.1).cast ?_ ?_⟩
      · simp only [packSteps, if_pos hr, if_pos ho]; rfl
      · simp only [packCycles, if_pos hr, if_pos ho]; decide
    · obtain ⟨ok, pc, x25⟩ := pack_digest k b base P s1 s i inv hi hr ho fits
      have := finish pathD (by decide) (by decide) (by decide) (by decide) ok pc x25
      refine ⟨_, this.2, (runs_path _ s this.1).cast ?_ ?_⟩
      · simp only [packSteps, if_pos hr, if_neg ho]; rfl
      · simp only [packCycles, if_pos hr, if_neg ho]; decide
  · obtain ⟨ok, pc, x25⟩ := pack_footer k b base P s1 s i inv hi hr fits
    have := finish pathF (by decide) (by decide) (by decide) (by decide) ok pc x25
    refine ⟨_, this.2, (runs_path _ s this.1).cast ?_ ?_⟩
    · simp only [packSteps, if_neg hr]; rfl
    · simp only [packCycles, if_neg hr]; decide

theorem pack_steps_sum (k N : Nat) : ∑ i ∈ Finset.range N, packSteps k i =
    18 * (48 * (min N (483*k) / 483) + min (min N (483*k) % 483) 48) +
    27 * (min N (483*k) - (48 * (min N (483*k) / 483) + min (min N (483*k) % 483) 48)) +
    19 * (N - min N (483*k)) := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; unfold packSteps; split_ifs <;> omega

theorem pack_cycles_sum (k N : Nat) : ∑ i ∈ Finset.range N, packCycles k i =
    27 * (48 * (min N (483*k) / 483) + min (min N (483*k) % 483) 48) +
    45 * (min N (483*k) - (48 * (min N (483*k) / 483) + min (min N (483*k) % 483) 48)) +
    31 * (N - min N (483*k)) := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; unfold packCycles; split_ifs <;> omega

theorem pack_loop (k b base : Nat) (P : List Byte) (s1 s : MachineState)
    (inv : PackBody k b base P s1 0 s) (src : Unpacked k b base P s1)
    (fits : 498*k + 30*b ≤ capacityBytes) (room : base + 2^34 ≤ 2^36) :
    ∃ s', PackBody k b base P s1 (bodyLen k b) s' ∧
      Runs s s' (12609*k + 551*b) (20871*k + 899*b) := by
  obtain ⟨s', inv', run⟩ := runs_loop (fun i s => PackBody k b base P s1 i s) (bodyLen k b)
    (packSteps k) (packCycles k)
    (fun i hi s inv => pack_iter k b base P s1 s i inv src hi fits room) (bodyLen k b) 0 s (by omega) inv
  refine ⟨s', inv', run.cast ?_ ?_⟩
  · rw [← Finset.range_eq_Ico, pack_steps_sum]; unfold bodyLen count; omega
  · rw [← Finset.range_eq_Ico, pack_cycles_sum]; unfold bodyLen count; omega


/-! ### Remainder loop: four six-bit remainders become three bytes. -/

theorem extend_fn (F G : Word → Byte) (lo i : Nat) (f : Nat → Byte) (old : Word → Byte)
    (v : Byte) (fit : lo + i < 2^64)
    (hs : ∀ a, G a = if lo ≤ a.toNat ∧ a.toNat < lo + i then f (a.toNat - lo) else old a)
    (hs' : ∀ a, F a = if a = BitVec.ofNat 64 (lo + i) then v else G a)
    (hv : v = f i) :
    ∀ a, F a = if lo ≤ a.toNat ∧ a.toNat < lo + (i + 1) then f (a.toNat - lo) else old a := by
  intro a
  rw [hs', hs]
  by_cases e : a = BitVec.ofNat 64 (lo + i)
  · have : a.toNat = lo + i := by rw [e, toNat_w _ fit]
    rw [if_pos e, if_pos (by omega), hv, show a.toNat - lo = i by omega]
  · have : a.toNat ≠ lo + i := by
      intro h; apply e; apply BitVec.eq_of_toNat_eq; rw [h, toNat_w _ fit]
    rw [if_neg e]
    by_cases r : lo ≤ a.toNat ∧ a.toNat < lo + i
    · rw [if_pos r, if_pos (by omega)]
    · rw [if_neg r, if_neg (by omega)]

def gbits (P : List Byte) (k b j : Nat) : Nat :=
  if j < count k b then ProofCodec.remainderBits P k j else 0

theorem gbits_lt (P : List Byte) (k b j : Nat) : gbits P k b j < 64 := by
  unfold gbits ProofCodec.remainderBits; split_ifs <;> omega

theorem gathered_setWidth (P : List Byte) (k b j : Nat) :
    (gathered P k b j).setWidth 64 = BitVec.ofNat 64 (gbits P k b j) := by
  apply BitVec.eq_of_toNat_eq
  have := gbits_lt P k b j
  unfold gathered gbits at *
  split_ifs at * <;> simp <;> omega

theorem w_or_mul (a c p : Nat) (s : Nat) (hp : p = 2^s) (ha : a < p) (h1 : a < 2^64) (h2 : c * p < 2^64)
    (h3 : a + c * p < 2^64) :
    BitVec.ofNat 64 a ||| BitVec.ofNat 64 (c * p) = BitVec.ofNat 64 (a + c * p) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_or, toNat_w _ h1, toNat_w _ h2, toNat_w _ h3]
  subst hp
  rw [Nat.add_comm, Nat.mul_comm, Nat.two_pow_add_eq_or_of_lt ha, Nat.or_comm]

theorem w_or6 (a c : Nat) (ha : a < 64) (h2 : c < 2^58) :
    BitVec.ofNat 64 a ||| BitVec.ofNat 64 (c * 64) = BitVec.ofNat 64 (a + c * 64) :=
  w_or_mul a c 64 6 rfl ha (by omega) (by omega) (by omega)
theorem w_or12 (a c : Nat) (ha : a < 4096) (h2 : c < 2^52) :
    BitVec.ofNat 64 a ||| BitVec.ofNat 64 (c * 4096) = BitVec.ofNat 64 (a + c * 4096) :=
  w_or_mul a c 4096 12 rfl ha (by omega) (by omega) (by omega)
theorem w_or18 (a c : Nat) (ha : a < 262144) (h2 : c < 2^46) :
    BitVec.ofNat 64 a ||| BitVec.ofNat 64 (c * 262144) = BitVec.ofNat 64 (a + c * 262144) :=
  w_or_mul a c 262144 18 rfl ha (by omega) (by omega) (by omega)

theorem gathered_lt (P : List Byte) (k b j : Nat) : (gathered P k b j).toNat < 64 := by
  unfold gathered ProofCodec.remainderBits
  split_ifs
  · simp; omega
  · simp

structure Remainder (k b base : Nat) (P : List Byte) (s1 : MachineState) (g : Nat) (s : MachineState) : Prop where
  regs : PackRegs k b base s
  pc : s.pc = pcOf 90
  x22 : s.getReg .x22 = BitVec.ofNat 64 (4*g)
  x26 : s.getReg .x26 = BitVec.ofNat 64 (base + (bodyLen k b + 3*g))
  bound : 4*g ≤ rounded k b
  mem : ∀ a : Word, s.getByte a =
    if base ≤ a.toNat ∧ a.toNat < base + (bodyLen k b + 3*g) then
      ProofCodec.packedByte P k (count k b) (a.toNat - base)
    else s1.getByte a

def remA : List Nat := [90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101]

set_option maxHeartbeats 800000 in
theorem rem_word (k b base : Nat) (P : List Byte) (s1 s : MachineState) (g : Nat)
    (inv : Remainder k b base P s1 g s)
    (scr : ∀ j < rounded k b, s1.getByte (BitVec.ofNat 64 (scratch base + j)) = gathered P k b j)
    (hg : 4*g < rounded k b)
    (fits : 498*k + 30*b ≤ capacityBytes) (room : base + 2^34 ≤ 2^36) :
    PathOK s remA ∧ (run s remA).pc = pcOf 102 ∧
      (run s remA).getReg .x23 = BitVec.ofNat 64 (ProofCodec.remainderWord P k (count k b) g) := by
  have hg' := hg
  have fits' := fits
  unfold rounded count at hg'
  unfold capacityBytes at fits'
  have regs := inv.regs
  have ne1 : BitVec.ofNat 64 (4*g) ≠ BitVec.ofNat 64 (rounded k b) := by
    rw [Ne, w_inj _ _ (by omega) (by unfold rounded count; omega)]; omega
  have rd (m : Nat) (hm : m < 4) : s.getByte (BitVec.ofNat 64 (scratch base + 4*g + m)) =
      gathered P k b (4*g + m) := by
    have e : scratch base + 4*g + m < 2^64 := by unfold scratch; omega
    rw [inv.mem, toNat_w _ e, if_neg (by unfold bodyLen scratch count; omega), Nat.add_assoc, scr _ (by unfold rounded count; omega)]
  have rd0 := rd 0 (by omega)
  have rd1 := rd 1 (by omega)
  have rd2 := rd 2 (by omega)
  have rd3 := rd 3 (by omega)
  simp only [Nat.add_zero] at rd0
  refine ⟨?_, ?_, ?_⟩
  · simp (disch := omega) [PathOK, remA, execInstrBr, inv.pc, inv.x22, regs.x19, regs.x18, ne1,
      ordinaryInstr, memoryArgumentsValid, memAccess, w_add]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> apply accessValid_of <;> rw [toNat_w _ (by unfold scratch; omega)] <;>
      unfold scratch <;> omega
  · simp [run, remA, execInstrBr, inv.pc, inv.x22, regs.x19, ne1]
  · simp (disch := omega) [run, remA, execInstrBr, inv.pc, inv.x22, regs.x19, regs.x18, ne1, w_add,
      rd0, rd1, rd2, rd3, gathered_setWidth, w_shl]
    have h0 := gbits_lt P k b (4*g)
    have h1 := gbits_lt P k b (4*g+1)
    have h2 := gbits_lt P k b (4*g+2)
    have h3 := gbits_lt P k b (4*g+3)
    rw [w_or6 _ _ h0 (by omega), w_or12 _ _ (by omega) (by omega), w_or18 _ _ (by omega) (by omega)]
    congr 1
    simp only [ProofCodec.remainderWord, Finset.sum_range_succ, Finset.sum_range_zero, gbits, Nat.add_zero]
    split_ifs <;> simp <;> omega

theorem packed_rem_byte (P : List Byte) (k b g m : Nat) (hm : m < 3) :
    ProofCodec.packedByte P k (count k b) (bodyLen k b + 3*g + m) =
      BitVec.ofNat 8 (ProofCodec.remainderWord P k (count k b) g / 256^m) := by
  unfold ProofCodec.packedByte
  have e : bodyLen k b = ProofCodec.bodyLength k (count k b) := rfl
  rw [← e, if_neg (by omega), show (bodyLen k b + 3*g + m - bodyLen k b) / 3 = g by omega,
    show (bodyLen k b + 3*g + m - bodyLen k b) % 3 = m by omega]

def remB : List Nat := [102, 103, 104, 105, 106, 107, 108, 109]

set_option maxHeartbeats 800000 in
theorem rem_store (k b base : Nat) (P : List Byte) (s1 u : MachineState) (g W : Nat)
    (regs : PackRegs k b base u) (pc : u.pc = pcOf 102)
    (x22 : u.getReg .x22 = BitVec.ofNat 64 (4*g))
    (x26 : u.getReg .x26 = BitVec.ofNat 64 (base + (bodyLen k b + 3*g)))
    (x23 : u.getReg .x23 = BitVec.ofNat 64 W) (hW : W = ProofCodec.remainderWord P k (count k b) g)
    (hg : 4*g < rounded k b)
    (fits : 498*k + 30*b ≤ capacityBytes) (room : base + 2^34 ≤ 2^36)
    (mem : ∀ a : Word, u.getByte a =
      if base ≤ a.toNat ∧ a.toNat < base + (bodyLen k b + 3*g) then
        ProofCodec.packedByte P k (count k b) (a.toNat - base)
      else s1.getByte a) :
    PathOK u remB ∧ Remainder k b base P s1 (g + 1) (run u remB) := by
  have hg' := hg
  have fits' := fits
  unfold rounded count at hg'
  unfold capacityBytes at fits'
  have hB : bodyLen k b = 48*k + 29*(15*k+b) := rfl
  have hW' : W < 2^24 := by
    rw [hW]
    exact (ProofCodec.remainderWord_digits P k (count k b) g 0 (by omega) (by unfold count; omega)).1
  have fit : base + (bodyLen k b + 3*g) + 3 < 2^64 := by omega
  constructor
  · simp [PathOK, remB, execInstrBr, pc, ordinaryInstr, memoryArgumentsValid, memAccess, x26, w_add]
    refine ⟨?_, ?_, ?_⟩ <;> apply accessValid_of <;> rw [toNat_w _ (by omega)] <;> omega
  · refine ⟨regs.keep _ (by decide), ?_, ?_, ?_, by unfold rounded count; omega, ?_⟩
    · simp [run, remB, execInstrBr, pc]
    · simp [run, remB, execInstrBr, x22, w_add]; exact congrArg _ (by ring)
    · simp [run, remB, execInstrBr, x26, w_add]; exact congrArg _ (by ring)
    · let F0 : Word → Byte := fun a => if a = BitVec.ofNat 64 (base + (bodyLen k b + 3*g)) then
          BitVec.ofNat 8 W else u.getByte a
      let F1 : Word → Byte := fun a => if a = BitVec.ofNat 64 (base + (bodyLen k b + 3*g + 1)) then
          BitVec.ofNat 8 (W / 256) else F0 a
      let F2 : Word → Byte := fun a => if a = BitVec.ofNat 64 (base + (bodyLen k b + 3*g + 2)) then
          BitVec.ofNat 8 (W / 256 / 256) else F1 a
      have m0 := extend_fn F0 u.getByte base (bodyLen k b + 3*g)
        (fun p => ProofCodec.packedByte P k (count k b) p) s1.getByte (BitVec.ofNat 8 W) (by omega) mem
        (fun a => rfl) (by
          rw [show bodyLen k b + 3*g = bodyLen k b + 3*g + 0 from rfl, packed_rem_byte P k b g 0 (by omega), hW]
          simp)
      have m1 := extend_fn F1 F0 base (bodyLen k b + 3*g + 1)
        (fun p => ProofCodec.packedByte P k (count k b) p) s1.getByte (BitVec.ofNat 8 (W / 256)) (by omega) m0
        (fun a => rfl) (by
          rw [packed_rem_byte P k b g 1 (by omega), hW]
          simp)
      have m2 := extend_fn F2 F1 base (bodyLen k b + 3*g + 2)
        (fun p => ProofCodec.packedByte P k (count k b) p) s1.getByte (BitVec.ofNat 8 (W / 256 / 256)) (by omega) m1
        (fun a => rfl) (by
          rw [packed_rem_byte P k b g 2 (by omega), hW, Nat.div_div_eq_div_mul]
          simp)
      intro a
      rw [show bodyLen k b + 3 * (g + 1) = bodyLen k b + 3*g + 2 + 1 by omega, ← m2 a]
      simp (disch := omega) [run, remB, execInstrBr, x26, x23, w_add, w_shr, truncate_w, F2, F1, F0,
        Nat.add_assoc, Nat.div_div_eq_div_mul]

theorem rem_iter (k b base : Nat) (P : List Byte) (s1 s : MachineState) (g : Nat)
    (inv : Remainder k b base P s1 g s)
    (scr : ∀ j < rounded k b, s1.getByte (BitVec.ofNat 64 (scratch base + j)) = gathered P k b j)
    (hg : 4*g < rounded k b)
    (fits : 498*k + 30*b ≤ capacityBytes) (room : base + 2^34 ≤ 2^36) :
    ∃ s', Remainder k b base P s1 (g + 1) s' ∧ Runs s s' 20 20 := by
  obtain ⟨ok, pc, x23⟩ := rem_word k b base P s1 s g inv scr hg fits room
  have st := rem_store k b base P s1 (run s remA) g _ (inv.regs.keep remA (by decide)) pc
    ((run_keeps _ remA s (by decide)).trans inv.x22) ((run_keeps _ remA s (by decide)).trans inv.x26)
    x23 rfl hg fits room (fun a => (getByte_of_mem (run_mem remA s (by decide)) a).trans (inv.mem a))
  rw [← run_append] at st
  have okAll : PathOK s (remA ++ remB) := (path_append _ _ _).2 ⟨ok, st.1⟩
  exact ⟨_, st.2, (runs_path _ s okAll).cast rfl (by decide)⟩

theorem rem_loop (k b base : Nat) (P : List Byte) (s1 s : MachineState)
    (inv : Remainder k b base P s1 0 s)
    (scr : ∀ j < rounded k b, s1.getByte (BitVec.ofNat 64 (scratch base + j)) = gathered P k b j)
    (fits : 498*k + 30*b ≤ capacityBytes) (room : base + 2^34 ≤ 2^36) :
    ∃ s', Remainder k b base P s1 (rounded k b / 4) s' ∧
      Runs s s' (20 * (rounded k b / 4)) (20 * (rounded k b / 4)) := by
  obtain ⟨s', inv', run⟩ := runs_loop (fun g s => Remainder k b base P s1 g s) (rounded k b / 4)
    (fun _ => 20) (fun _ => 20)
    (fun g hg s inv => rem_iter k b base P s1 s g inv scr (by unfold rounded at *; omega) fits room)
    (rounded k b / 4) 0 s (by omega) inv
  refine ⟨s', inv', run.cast ?_ ?_⟩ <;> simp [Nat.mul_comm]

/-! ### Entry: the common exit block jumps to the packer. -/

theorem runs_word (s : MachineState) (idx : Nat) (i : Instr) (hidx : idx < 1550)
    (pc : s.pc = BitVec.ofNat 64 (4096 + 4 * idx))
    (dec : (openingImage.code[idx]?).bind decodeInstruction = some (.base i))
    (ord : ordinaryInstr i = true) (valid : memoryArgumentsValid s i = true) :
    Runs s (execInstrBr s i) 1 (instructionCycles (.base i)) := by
  intro fuel coins
  rw [Nat.add_comm 1 fuel]
  exact execute_ordinary_step _ _ _ _ _ _ (packed_fetch_raw s idx i hidx pc dec) (ordinary_step_eq s _ ord valid)

def exitWords : List Instr := [.SUB .x11 .x21 .x20, .ADDI .x5 .x0 1, .ADDI .x10 .x0 0, .JAL .x0 3076]

def enterPack (s : MachineState) : MachineState := exitWords.foldl execInstrBr s

theorem runs_enter (s : MachineState) (pc : s.pc = 0x1a5c) : Runs s (enterPack s) 4 4 := by
  have p1 : (execInstrBr s (.SUB .x11 .x21 .x20)).pc = BitVec.ofNat 64 (4096 + 4 * 664) := by
    simp [execInstrBr, pc]
  have p2 : (execInstrBr (execInstrBr s (.SUB .x11 .x21 .x20)) (.ADDI .x5 .x0 1)).pc =
      BitVec.ofNat 64 (4096 + 4 * 665) := by
    simp [execInstrBr, pc]
  have p3 : (execInstrBr (execInstrBr (execInstrBr s (.SUB .x11 .x21 .x20)) (.ADDI .x5 .x0 1))
      (.ADDI .x10 .x0 0)).pc = BitVec.ofNat 64 (4096 + 4 * 666) := by
    simp [execInstrBr, pc]
  have r := (((runs_word s 663 (.SUB .x11 .x21 .x20) (by decide) (by rw [pc]; decide) rfl rfl rfl).trans
    (runs_word _ 664 (.ADDI .x5 .x0 1) (by decide) p1 rfl rfl rfl)).trans
    (runs_word _ 665 (.ADDI .x10 .x0 0) (by decide) p2 rfl rfl rfl)).trans
    (runs_word _ 666 (.JAL .x0 3076) (by decide) p3 rfl rfl rfl)
  exact r

theorem enter_facts (s : MachineState) (pc : s.pc = 0x1a5c) :
    (enterPack s).pc = pcOf 0 ∧ (enterPack s).getReg .x5 = 1 ∧ (enterPack s).getReg .x10 = 0 ∧
    (enterPack s).getReg .x11 = s.getReg .x21 - s.getReg .x20 ∧
    (∀ r, r ≠ .x11 → r ≠ .x5 → r ≠ .x10 → (enterPack s).getReg r = s.getReg r) ∧
    (enterPack s).mem = s.mem := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [enterPack, exitWords, execInstrBr, pc]
    decide
  · simp [enterPack, exitWords, execInstrBr]
  · simp [enterPack, exitWords, execInstrBr]
  · simp [enterPack, exitWords, execInstrBr]
  · intro r h1 h2 h3
    simp [enterPack, exitWords, execInstrBr, Ne.symm h1, Ne.symm h2, Ne.symm h3]
  · simp [enterPack, exitWords, execInstrBr, mem_setReg', MachineState.setPC]

def prelude : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

set_option maxHeartbeats 800000 in
theorem prelude_run (k b base : Nat) (P : List Byte) (s0 e : MachineState)
    (pc : e.pc = pcOf 0) (x5 : e.getReg .x5 = 1) (x10 : e.getReg .x10 = 0)
    (x16 : e.getReg .x16 = BitVec.ofNat 64 k) (x20 : e.getReg .x20 = BitVec.ofNat 64 base)
    (x11 : e.getReg .x11 = BitVec.ofNat 64 (498*k + 30*b)) (mem : e.mem = s0.mem)
    (fits : 498*k + 30*b ≤ capacityBytes) (room : base + 2^34 ≤ 2^36) :
    PathOK e prelude ∧ Gather k b base P s0 0 (run e prelude) := by
  have fits' := fits
  unfold capacityBytes at fits'
  constructor
  · simp [PathOK, prelude, execInstrBr, pc, ordinaryInstr, memoryArgumentsValid, memAccess]
  · refine ⟨⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, by omega, ?_⟩
    · simp [run, prelude, execInstrBr, x5]
    · simp [run, prelude, execInstrBr, x10]
    · simp [run, prelude, execInstrBr, x16]
    · simp [run, prelude, execInstrBr, x20]
    · simp [run, prelude, execInstrBr, x16, w_mul]; exact congrArg _ (by ring)
    · simp (disch := omega) [run, prelude, execInstrBr, x16, x11, w_mul, w_sub, w_divu]
      exact congrArg _ (by unfold count; omega)
    · simp [run, prelude, execInstrBr, x16, w_mul]; exact congrArg _ (by ring)
    · simp (disch := omega) [run, prelude, execInstrBr, x20, w_add, w_shl]
      exact congrArg _ (by unfold scratch; omega)
    · simp (disch := omega) [run, prelude, execInstrBr, x16, x11, w_mul, w_sub, w_divu, w_add, w_shl, w_shr]
      exact congrArg _ (by unfold rounded count; omega)
    · simp [run, prelude, execInstrBr, pc]
    · simp [run, prelude, execInstrBr]
    · intro a
      rw [getByte_of_mem ((run_mem prelude e (by decide)).trans mem), if_neg (by omega)]

def gatherExit : List Nat := [14, 42, 43, 44, 45, 46, 47]

set_option maxHeartbeats 800000 in
theorem gather_exit (k b base : Nat) (P : List Byte) (s0 s : MachineState)
    (inv : Gather k b base P s0 (rounded k b) s) :
    PathOK s gatherExit ∧ PackBody k b base P s 0 (run s gatherExit) := by
  have regs := inv.regs
  constructor
  · simp [PathOK, gatherExit, execInstrBr, inv.pc, inv.x22, regs.x19, ordinaryInstr, memoryArgumentsValid,
      memAccess]
  · have keep : ∀ r ∈ ([.x5, .x10, .x16, .x20, .x18, .x19] : List Reg),
        (run s gatherExit).getReg r = s.getReg r := by
      intro r hr; apply run_keeps; revert r; decide
    refine ⟨⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_, ?_, by omega, ?_⟩
    · rw [keep _ (by simp)]; exact regs.x5
    · rw [keep _ (by simp)]; exact regs.x10
    · rw [keep _ (by simp)]; exact regs.x16
    · rw [keep _ (by simp)]; exact regs.x20
    · rw [keep _ (by simp)]; exact regs.x18
    · rw [keep _ (by simp)]; exact regs.x19
    · simp [run, gatherExit, execInstrBr, regs.x8, regs.x7, inv.x22, regs.x19, w_mul, w_add]
      exact congrArg _ (by unfold bodyLen; ring)
    · simp [run, gatherExit, execInstrBr, regs.x16, inv.x22, regs.x19, w_mul]
      exact congrArg _ (by ring)
    · simp [run, gatherExit, execInstrBr, inv.pc, inv.x22, regs.x19]
    · simp [run, gatherExit, execInstrBr, inv.x22, regs.x19]
    · intro a
      rw [getByte_of_mem (run_mem gatherExit s (by decide)), if_neg (by omega)]

def packExit : List Nat := [48, 88, 89]

set_option maxHeartbeats 800000 in
theorem pack_exit (k b base : Nat) (P : List Byte) (s1 s : MachineState)
    (inv : PackBody k b base P s1 (bodyLen k b) s) :
    PathOK s packExit ∧ Remainder k b base P s1 0 (run s packExit) := by
  have regs := inv.regs
  constructor
  · simp [PathOK, packExit, execInstrBr, inv.pc, inv.x22, regs.x27, ordinaryInstr, memoryArgumentsValid,
      memAccess]
  · refine ⟨regs.keep _ (by decide), ?_, ?_, ?_, by omega, ?_⟩
    · simp [run, packExit, execInstrBr, inv.pc, inv.x22, regs.x27]
    · simp [run, packExit, execInstrBr]
    · simp [run, packExit, execInstrBr, inv.x22, regs.x27, regs.x20, w_add]
      exact congrArg _ (Nat.add_comm _ _)
    · intro a
      rw [getByte_of_mem (run_mem packExit s (by decide)), inv.mem]
      by_cases h : base ≤ a.toNat ∧ a.toNat < base + bodyLen k b
      · have h' : a.toNat - base < ProofCodec.bodyLength k (count k b) := by
          unfold bodyLen at h; unfold ProofCodec.bodyLength; omega
        rw [if_pos h, if_pos (by omega), ProofCodec.packedByte, if_pos h']
      · rw [if_neg h, if_neg (by omega)]

def remExit : List Nat := [90, 110, 111, 112, 113]

set_option maxHeartbeats 800000 in
theorem rem_exit (k b base : Nat) (P : List Byte) (s1 s : MachineState)
    (inv : Remainder k b base P s1 (rounded k b / 4) s) (fits : 498*k + 30*b ≤ capacityBytes) :
    PathOK s remExit ∧ (run s remExit).pc = pcOf 114 ∧
      (run s remExit).getReg .x11 = BitVec.ofNat 64 (ProofCodec.packedLength k (count k b)) ∧
      (run s remExit).getReg .x5 = 1 ∧ (run s remExit).getReg .x10 = 0 ∧
      (run s remExit).mem = s.mem := by
  have regs := inv.regs
  have fits' := fits
  unfold capacityBytes at fits'
  have e : 4 * (rounded k b / 4) = rounded k b := by unfold rounded; omega
  have hr : rounded k b < 2^64 := by unfold rounded count; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, run_mem _ _ (by decide)⟩
  · simp [PathOK, remExit, execInstrBr, inv.pc, inv.x22, regs.x19, e, ordinaryInstr, memoryArgumentsValid,
      memAccess]
  · simp [run, remExit, execInstrBr, inv.pc, inv.x22, regs.x19, e]
  · simp (disch := omega) [run, remExit, execInstrBr, inv.x22, regs.x19, regs.x27, e, w_add, w_shr]
    congr 1
    unfold ProofCodec.packedLength ProofCodec.bodyLength bodyLen rounded count; omega
  · simp [run, remExit, execInstrBr, inv.x22, regs.x19, e, regs.x5]
  · simp [run, remExit, execInstrBr, inv.x22, regs.x19, e, regs.x10]

theorem halt_run (f : MachineState) (pc : f.pc = pcOf 114) (x5 : f.getReg .x5 = 1)
    (x10 : f.getReg .x10 = 0) (fuel : Nat) (coins : Bool) :
    execute openingImage (1 + fuel) f coins = pure ⟨.success, f, 1, 0⟩ := by
  have fetched := fetch_pack f 114 (by decide) pc
  rw [show packCode.getD 114 .NOP = .ECALL from rfl] at fetched
  rw [Nat.add_comm]
  simp [execute, fetched, x5, x10]

/-! ### The whole postpass. -/

/-- Fuel from the exit block at `0x1a5c` through the packer's final `ECALL`. -/
def exitSteps (k b : Nat) : Nat :=
  34 + 12939*k + 568*b + 7*(rounded k b - count k b) + 5*rounded k b

/-- Cycles from the exit block at `0x1a5c` through the packer's final `ECALL`. -/
def exitCycles (k b : Nat) : Nat :=
  49 + 21381*k + 922*b + 7*(rounded k b - count k b) + 5*rounded k b

theorem execute_pack (k b base : Nat) (P : List Byte) (s : MachineState) (pc : s.pc = 0x1a5c)
    (x16 : s.getReg .x16 = BitVec.ofNat 64 k) (x20 : s.getReg .x20 = BitVec.ofNat 64 base)
    (len : s.getReg .x21 - s.getReg .x20 = BitVec.ofNat 64 (498*k + 30*b))
    (fits : 498*k + 30*b ≤ capacityBytes) (room : base + 2^34 ≤ 2^36)
    (src : Source k b base P s) :
    ∃ final : MachineState,
      (∀ fuel coins, execute openingImage (exitSteps k b + fuel) s coins =
        pure ⟨.success, final, exitCycles k b, 0⟩) ∧
      final.getReg .x11 = BitVec.ofNat 64 (ProofCodec.packedLength k (count k b)) ∧
      ∀ a : Word, final.getByte a =
        if base ≤ a.toNat ∧ a.toNat < base + ProofCodec.packedLength k (count k b) then
          ProofCodec.packedByte P k (count k b) (a.toNat - base)
        else if scratch base ≤ a.toNat ∧ a.toNat < scratch base + rounded k b then
          gathered P k b (a.toNat - scratch base)
        else s.getByte a := by
  -- exit block
  have r0 := runs_enter s pc
  obtain ⟨epc, e5, e10, e11, ekeep, emem⟩ := enter_facts s pc
  let e := enterPack s
  -- prelude
  have pre := prelude_run k b base P s e epc e5 e10
    ((ekeep .x16 (by decide) (by decide) (by decide)).trans x16)
    ((ekeep .x20 (by decide) (by decide) (by decide)).trans x20) (e11.trans len) emem fits room
  have r1 := (runs_path _ e pre.1).cast (s2 := 14) (c2 := 23) rfl (by decide)
  -- gather loop
  obtain ⟨s1, g1, r2⟩ := gather_loop k b base P s (run e prelude) pre.2 src fits room
  have ge := gather_exit k b base P s s1 g1
  have r3 := (runs_path _ s1 ge.1).cast (s2 := 7) (c2 := 13) rfl (by decide)
  have unpacked : Unpacked k b base P s1 := fun a lo hi => g1.read src fits a lo hi
  -- pack loop
  obtain ⟨s2, p2, r4⟩ := pack_loop k b base P s1 _ ge.2 unpacked fits room
  have pe := pack_exit k b base P s1 s2 p2
  have r5 := (runs_path _ s2 pe.1).cast (s2 := 3) (c2 := 3) rfl (by decide)
  -- remainder loop
  have scr : ∀ j < rounded k b, s1.getByte (BitVec.ofNat 64 (scratch base + j)) = gathered P k b j := by
    intro j hj
    have fit : scratch base + j < 2^64 := by
      unfold scratch rounded count capacityBytes at *; omega
    rw [g1.mem, toNat_w _ fit, if_pos (by omega), Nat.add_sub_cancel_left]
  obtain ⟨s3, p3, r6⟩ := rem_loop k b base P s1 _ pe.2 scr fits room
  obtain ⟨ok, fpc, f11, f5, f10, fmem⟩ := rem_exit k b base P s1 s3 p3 fits
  have r7 := (runs_path _ s3 ok).cast (s2 := 5) (c2 := 5) rfl (by decide)
  have all := (((((((r0.trans r1).trans r2).trans r3).trans r4).trans r5).trans r6).trans r7)
  refine ⟨run s3 remExit, ?_, f11, ?_⟩
  · intro fuel coins
    have h := all (1 + fuel) coins
    rw [halt_run _ fpc f5 f10] at h
    rw [show exitSteps k b + fuel = 4 + 14 + (330*k + 17*b + 7*(rounded k b - count k b)) + 7 +
      (12609*k + 551*b) + 3 + 20 * (rounded k b / 4) + 5 + (1 + fuel) by
        unfold exitSteps rounded; omega, h]
    simp only [pure_bind, Execution.charge]
    congr 2
    unfold exitCycles rounded; omega
  · intro a
    rw [getByte_of_mem fmem, p3.mem, g1.mem]
    have e1 : bodyLen k b + 3 * (rounded k b / 4) = ProofCodec.packedLength k (count k b) := by
      unfold bodyLen ProofCodec.packedLength ProofCodec.bodyLength rounded; omega
    rw [e1]

theorem exit_cycles_le (k b : Nat) (hk : k ≤ 128) (hb : b ≤ 128) : exitCycles k b ≤ 2865073 := by
  unfold exitCycles rounded count
  generalize hm : (15*k + b + 3) / 4 = m
  have h1 : 4*m ≤ 15*k + b + 3 := by omega
  have h2 : 15*k + b ≤ 4*m := by omega
  have h3 : m ≤ 512 := by omega
  omega

theorem exit_cycles_max : exitCycles 128 128 = 2865073 := by decide

theorem exit_steps_le (k b : Nat) (hk : k ≤ 128) (hb : b ≤ 128) : exitSteps k b ≤ 1739170 := by
  unfold exitSteps rounded count
  generalize hm : (15*k + b + 3) / 4 = m
  have h1 : 4*m ≤ 15*k + b + 3 := by omega
  have h2 : 15*k + b ≤ 4*m := by omega
  have h3 : m ≤ 512 := by omega
  omega

theorem exit_steps_le_cardinality (k b : Nat) (hk : k ≤ 16777216) (hb : b ≤ 128) :
    exitSteps k b ≤ 218338762402 := by
  unfold exitSteps rounded count
  generalize hm : (15*k + b + 3) / 4 = m
  have h1 : 4*m ≤ 15*k + b + 3 := by omega
  have h2 : 15*k + b ≤ 4*m := by omega
  have h3 : m ≤ 62914592 := by omega
  omega

theorem exit_steps_le_cycles (k b : Nat) : exitSteps k b ≤ exitCycles k b := by
  unfold exitSteps exitCycles; omega

/-- `execute_pack` in terms of `ProofCodec.pack`, for a proof list of the unpacked length. -/
theorem packed_bytes (k b : Nat) (P : List Byte) (hlen : P.length = 498*k + 30*b) (p : Nat)
    (hp : p < ProofCodec.packedLength k (count k b)) :
    ProofCodec.packedByte P k (count k b) p = (ProofCodec.pack k P).getD p 0 := by
  have hc : ProofCodec.unpackedCount k P.length = count k b := by
    rw [hlen, ProofCodec.unpackedCount, count]; omega
  rw [ProofCodec.getD_pack k P p (by rw [hc]; exact hp), hc]
end TwoPermutationPrototype.PackedOpening.Pack
