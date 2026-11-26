import CommitGolfCandidate.TwoPermutationPackedCheckerSteps
import CommitGolfCandidate.WriteMemory
import CommitGolfCandidate.TwoPermutationOpeningBlocks

/-! Symbolic execution helpers for the checker's proof-unpacking wrapper (words 377-505).
Registers are tracked as natural numbers; straight-line ALU blocks, single memory
instructions, branches and jumps each get one lemma. -/
namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp

/-- Fetch anywhere in the 506-word image. -/
theorem fetch_any (s : MachineState) (index : Nat) (instruction : Instr)
    (bounded : index < 506) (pc : s.pc = BitVec.ofNat 64 (4096+4*index))
    (decoded : (packedImage.code[index]?).bind decodeInstruction = some (.base instruction)) :
    fetch packedImage s = some (.base instruction) :=
  cap_image_fetch packedImage s index instruction (by omega) pc decoded

theorem hop_one (s : MachineState) (index : Nat) (i : Instr) (bounded : index < 506)
    (pc : s.pc = BitVec.ofNat 64 (4096+4*index))
    (decoded : (packedImage.code[index]?).bind decodeInstruction = some (.base i))
    (ord : ordinaryStep s (.base i) = some (execInstrBr s i)) :
    Hop s (execInstrBr s i) 1 (instructionCycles (.base i)) := by
  intro fuel
  rw [Nat.add_comm 1 fuel]
  exact execute_ordinary_step _ _ _ _ _ _ (fetch_any s index i bounded pc decoded) ord

theorem Hop.refl (s : MachineState) : Hop s s 0 0 := by
  intro fuel
  simp [Execution.charge]

theorem Hop.cast {s t : MachineState} {a b c d : Nat} (h : Hop s t a b) (ha : a = c) (hb : b = d) :
    Hop s t c d := ha ▸ hb ▸ h

/-! ### Registers as naturals -/

def View (s : MachineState) (v : Reg → Nat) : Prop := ∀ r, (s.getReg r).toNat = v r

def setV (v : Reg → Nat) (rd : Reg) (x : Nat) : Reg → Nat :=
  fun r => if r = rd ∧ rd ≠ .x0 then x else v r

def isAlu : Instr → Bool
  | .ADD .. | .SUB .. | .ADDI .. | .ANDI .. | .SLLI .. | .SRLI .. | .SRL .. | .OR ..
  | .MUL .. | .DIVU .. => true
  | _ => false

def aluDest : Instr → Reg
  | .ADD rd _ _ | .SUB rd _ _ | .ADDI rd _ _ | .ANDI rd _ _ | .SLLI rd _ _ | .SRLI rd _ _
  | .SRL rd _ _ | .OR rd _ _ | .MUL rd _ _ | .DIVU rd _ _ => rd
  | _ => .x0

def aluVal (v : Reg → Nat) : Instr → Nat
  | .ADD _ a b => (v a + v b) % 2^64
  | .SUB _ a b => (2^64 - v b + v a) % 2^64
  | .ADDI _ a imm => (v a + (signExtend12 imm).toNat) % 2^64
  | .ANDI _ a imm => v a &&& (signExtend12 imm).toNat
  | .SLLI _ a sh => (v a <<< sh.toNat) % 2^64
  | .SRLI _ a sh => v a >>> sh.toNat
  | .SRL _ a b => v a >>> (v b % 64)
  | .OR _ a b => v a ||| v b
  | .MUL _ a b => (v a * v b) % 2^64
  | .DIVU _ a b => if v b = 0 then 2^64-1 else v a / v b
  | _ => 0

def stepV (v : Reg → Nat) (i : Instr) : Reg → Nat := setV v (aluDest i) (aluVal v i)

theorem view_set (s : MachineState) (v : Reg → Nat) (rd : Reg) (w : Word) (x : Nat)
    (hv : View s v) (hx : w.toNat = x) : View (s.setReg rd w) (setV v rd x) := by
  intro r
  rw [TwoPermutationPrototype.Opening.getReg_setReg]
  unfold setV
  by_cases h : rd = r ∧ rd ≠ .x0
  · rw [if_pos h, if_pos ⟨h.1.symm, h.2⟩, hx]
  · rw [if_neg h, if_neg (fun h' => h ⟨h'.1.symm, h'.2⟩), hv]

theorem alu_exec (s : MachineState) (i : Instr) (alu : isAlu i = true) :
    execInstrBr s i = (s.setReg (aluDest i) (match i with
      | .ADD _ a b => s.getReg a + s.getReg b
      | .SUB _ a b => s.getReg a - s.getReg b
      | .ADDI _ a imm => s.getReg a + signExtend12 imm
      | .ANDI _ a imm => s.getReg a &&& signExtend12 imm
      | .SLLI _ a sh => s.getReg a <<< sh.toNat
      | .SRLI _ a sh => s.getReg a >>> sh.toNat
      | .SRL _ a b => s.getReg a >>> ((s.getReg b).toNat % 64)
      | .OR _ a b => s.getReg a ||| s.getReg b
      | .MUL _ a b => s.getReg a * s.getReg b
      | .DIVU _ a b => rv64_divu (s.getReg a) (s.getReg b)
      | _ => 0)).setPC (s.pc + 4) := by
  cases i <;> simp only [isAlu, Bool.false_eq_true] at alu <;> rfl

theorem view_alu (s : MachineState) (v : Reg → Nat) (i : Instr) (alu : isAlu i = true)
    (hv : View s v) : View (execInstrBr s i) (stepV v i) := by
  rw [alu_exec s i alu]
  intro r
  rw [MachineState.getReg_setPC]
  revert r
  apply view_set s v _ _ _ hv
  have hv' : ∀ r, (s.getReg r).toNat = v r := hv
  cases i <;> simp only [isAlu, Bool.false_eq_true] at alu <;>
    simp only [aluVal, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_and, BitVec.toNat_or,
      BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_mul, hv']
  rename_i a b _
  unfold rv64_divu
  by_cases z : s.getReg b = 0#64
  · have : v b = 0 := by rw [← hv, z]; rfl
    simp [z, this]
  · have : v b ≠ 0 := by
      rw [← hv]; intro h; exact z (BitVec.eq_of_toNat_eq h)
    simp only [beq_iff_eq, z, ite_false, this, BitVec.toNat_udiv, hv']

theorem alu_pc (s : MachineState) (i : Instr) (alu : isAlu i = true) :
    (execInstrBr s i).pc = s.pc + 4 := by
  rw [alu_exec s i alu]; rfl

theorem alu_mem (s : MachineState) (i : Instr) (alu : isAlu i = true) :
    (execInstrBr s i).mem = s.mem := by
  rw [alu_exec s i alu]
  simp only [MachineState.setPC]
  cases h : aluDest i <;> rfl

theorem alu_ordinary (s : MachineState) (i : Instr) (alu : isAlu i = true) :
    ordinaryStep s (.base i) = some (execInstrBr s i) := by
  cases i <;> simp_all [isAlu, ordinaryStep, memoryArgumentsValid, memAccess]

def blockCycles (is : List Instr) : Nat := (is.map fun i => instructionCycles (.base i)).sum

theorem pc_next (index : Nat) :
    BitVec.ofNat 64 (4096+4*index) + 4 = BitVec.ofNat 64 (4096+4*(index+1)) := by
  rw [show (4 : Word) = BitVec.ofNat 64 4 from rfl, ← BitVec.ofNat_add]
  congr 1

/-- A straight-line ALU block. -/
theorem block_run (s : MachineState) (index : Nat) (is : List Instr) (v : Reg → Nat) (hv : View s v)
    (bounded : index + is.length ≤ 506) (pc : s.pc = BitVec.ofNat 64 (4096+4*index))
    (code : ∀ j < is.length, (packedImage.code[index+j]?).bind decodeInstruction = some (.base (is.getD j .NOP)))
    (alu : is.all isAlu = true) :
    Hop s (is.foldl execInstrBr s) is.length (blockCycles is) ∧
      View (is.foldl execInstrBr s) (is.foldl stepV v) ∧
      (is.foldl execInstrBr s).pc = BitVec.ofNat 64 (4096+4*(index+is.length)) ∧
      (is.foldl execInstrBr s).mem = s.mem := by
  induction is generalizing s index v with
  | nil => exact ⟨Hop.refl s, hv, by simpa using pc, rfl⟩
  | cons i is ih =>
    simp only [List.all_cons, Bool.and_eq_true] at alu
    have first := hop_one s index i (by simp at bounded; omega) pc
      (by simpa using code 0 (by simp)) (alu_ordinary s i alu.1)
    have pc' : (execInstrBr s i).pc = BitVec.ofNat 64 (4096+4*(index+1)) := by
      rw [alu_pc s i alu.1, pc, pc_next]
    obtain ⟨hop, view, pc'', mem⟩ := ih (execInstrBr s i) (index+1) (stepV v i)
      (view_alu s v i alu.1 hv) (by simp at bounded; omega) pc'
      (by intro j hj; simpa [Nat.add_assoc, Nat.add_comm 1 j] using code (j+1) (by simp; omega)) alu.2
    refine ⟨?_, view, ?_, ?_⟩
    · have h := first.thenDo hop
      refine h.cast (by simp; omega) ?_
      simp [blockCycles]
    · rw [List.foldl_cons, pc'']; simp only [List.length_cons]; congr 2; omega
    · rw [List.foldl_cons, mem, alu_mem s i alu.1]

/-! ### Branches and jumps -/

theorem view_pc_only (s : MachineState) (v : Reg → Nat) (p : Word) (hv : View s v) :
    View (s.setPC p) v := by
  intro r; rw [MachineState.getReg_setPC]; exact hv r

theorem beq_exec (s : MachineState) (v : Reg → Nat) (hv : View s v) (a b : Reg) (off : BitVec 13) :
    execInstrBr s (.BEQ a b off) = s.setPC (if v a = v b then s.pc + signExtend13 off else s.pc + 4) := by
  have e : (s.getReg a == s.getReg b) = decide (v a = v b) := by
    rw [← hv a, ← hv b]
    by_cases h : s.getReg a = s.getReg b
    · simp [h]
    · simp [h, BitVec.toNat_inj]
  by_cases h : v a = v b <;> simp [execInstrBr, e, h]

theorem bne_exec (s : MachineState) (v : Reg → Nat) (hv : View s v) (a b : Reg) (off : BitVec 13) :
    execInstrBr s (.BNE a b off) = s.setPC (if v a = v b then s.pc + 4 else s.pc + signExtend13 off) := by
  have e : (s.getReg a != s.getReg b) = !decide (v a = v b) := by
    rw [← hv a, ← hv b]
    by_cases h : s.getReg a = s.getReg b
    · simp [h]
    · simp [h, BitVec.toNat_inj]
  by_cases h : v a = v b <;> simp [execInstrBr, e, h]

theorem bltu_exec (s : MachineState) (v : Reg → Nat) (hv : View s v) (a b : Reg) (off : BitVec 13) :
    execInstrBr s (.BLTU a b off) = s.setPC (if v a < v b then s.pc + signExtend13 off else s.pc + 4) := by
  have e : BitVec.ult (s.getReg a) (s.getReg b) = decide (v a < v b) := by
    rw [← hv a, ← hv b, BitVec.ult]
  by_cases h : v a < v b <;> simp [execInstrBr, e, h]

theorem bgeu_exec (s : MachineState) (v : Reg → Nat) (hv : View s v) (a b : Reg) (off : BitVec 13) :
    execInstrBr s (.BGEU a b off) = s.setPC (if v a < v b then s.pc + 4 else s.pc + signExtend13 off) := by
  have e : BitVec.ult (s.getReg a) (s.getReg b) = decide (v a < v b) := by
    rw [← hv a, ← hv b, BitVec.ult]
  by_cases h : v a < v b <;> simp [execInstrBr, e, h]

theorem jal0_exec (s : MachineState) (off : BitVec 21) :
    execInstrBr s (.JAL .x0 off) = s.setPC (s.pc + signExtend21 off) := rfl

theorem branch_ordinary (s : MachineState) (i : Instr)
    (h : (match i with | .BEQ .. | .BNE .. | .BLTU .. | .BGEU .. | .JAL .. => true | _ => false) = true) :
    ordinaryStep s (.base i) = some (execInstrBr s i) := by
  cases i <;> simp_all [ordinaryStep, memoryArgumentsValid, memAccess]

/-! ### Byte memory -/

theorem lbu_exec (s : MachineState) (rd rs : Reg) (off : BitVec 12) :
    execInstrBr s (.LBU rd rs off) =
      (s.setReg rd ((s.getByte (s.getReg rs + signExtend12 off)).zeroExtend 64)).setPC (s.pc + 4) := rfl

theorem sb_exec (s : MachineState) (rs1 rs2 : Reg) (off : BitVec 12) :
    execInstrBr s (.SB rs1 rs2 off) =
      (s.setByte (s.getReg rs1 + signExtend12 off) ((s.getReg rs2).truncate 8)).setPC (s.pc + 4) := rfl

theorem lbu_ordinary (s : MachineState) (rd rs : Reg) (off : BitVec 12)
    (room : (s.getReg rs + signExtend12 off).toNat + 1 ≤ MEMORY_BYTES) :
    ordinaryStep s (.base (.LBU rd rs off)) = some (execInstrBr s (.LBU rd rs off)) := by
  rw [BitVec.toNat_add] at room
  simp only [MEMORY_BYTES] at room
  simp [ordinaryStep, memoryArgumentsValid, memAccess, accessValid, rangeValid, MEMORY_BYTES]
  omega

theorem sb_ordinary (s : MachineState) (rs1 rs2 : Reg) (off : BitVec 12)
    (room : (s.getReg rs1 + signExtend12 off).toNat + 1 ≤ MEMORY_BYTES) :
    ordinaryStep s (.base (.SB rs1 rs2 off)) = some (execInstrBr s (.SB rs1 rs2 off)) := by
  rw [BitVec.toNat_add] at room
  simp only [MEMORY_BYTES] at room
  simp [ordinaryStep, memoryArgumentsValid, memAccess, accessValid, rangeValid, MEMORY_BYTES]
  omega

theorem view_lbu (s : MachineState) (v : Reg → Nat) (hv : View s v) (rd rs : Reg) (off : BitVec 12) :
    View (execInstrBr s (.LBU rd rs off))
      (setV v rd (s.getByte (s.getReg rs + signExtend12 off)).toNat) := by
  rw [lbu_exec]
  apply view_pc_only
  apply view_set s v _ _ _ hv
  have := (s.getByte (s.getReg rs + signExtend12 off)).isLt
  simp only [BitVec.toNat_setWidth]
  omega

theorem setByte_getReg (s : MachineState) (a : Word) (b : BitVec 8) (r : Reg) :
    (s.setByte a b).getReg r = s.getReg r := by
  cases r <;> rfl

theorem view_sb (s : MachineState) (v : Reg → Nat) (hv : View s v) (rs1 rs2 : Reg) (off : BitVec 12) :
    View (execInstrBr s (.SB rs1 rs2 off)) v := by
  rw [sb_exec]
  intro r
  rw [MachineState.getReg_setPC, setByte_getReg, hv]

theorem sb_byte (s : MachineState) (rs1 rs2 : Reg) (off : BitVec 12) (q : Word) :
    (execInstrBr s (.SB rs1 rs2 off)).getByte q =
      if q = s.getReg rs1 + signExtend12 off then (s.getReg rs2).truncate 8 else s.getByte q := by
  rw [sb_exec]
  exact set_byte_read _ _ _ _

theorem setPC_getByte (s : MachineState) (p q : Word) : (s.setPC p).getByte q = s.getByte q := rfl

theorem lbu_mem (s : MachineState) (rd rs : Reg) (off : BitVec 12) :
    (execInstrBr s (.LBU rd rs off)).mem = s.mem := by
  rw [lbu_exec]; simp only [MachineState.setPC]; cases rd <;> rfl

end TwoPermutationPrototype.Packed.Checker
