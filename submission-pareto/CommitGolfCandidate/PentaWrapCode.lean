import CommitGolfCandidate.Execution
import CommitGolfCandidate.TwoPermutationMemoryBridge

/-! The level-7 cap checker wrapper (check-image words 460-774) as a symbolic program, and
straight-line execution facts for any image that carries these words.

Wrapper offsets (absolute word = 460 + offset):
- 0-9: empty test, exact length `912k + 8704`, table source and destination, 55 groups;
- 10-93: one table group: 20 doublewords copied to the doubled group (`+0` and `+160`) and
  cleared at the source, then the pointers advance and the group counter loops;
- 94-105: constants `x8 = 5^7`, `x9 = 5`, `x18 = 320`, `x19-x22` = the four level bases + 32;
- 106-114: pointers to the last record (`x24` compressed, `x25` expanded, `x26` index word);
- 115-121: one record's 114-doubleword prefix, copied from the top down;
- 122-123: the record's index and `x6 = index / 5^7`;
- 124-283: four level fills of 40 words each (`levelFill`);
- 284-287: pointers to the previous record, loop;
- 288-308: `a7 = 1424k`, every temporary zeroed, jump to word 1;
- 309-311: empty case; 312-314: reject.

Register use: `x5 x6 x7 x28-x31` scratch, `x27` copy offset. The doubled table lives at
`TABLE = 2^28`, in scratch memory below the commitment.

Record order. Record `r` of a cap proof is expanded with index word `r` of the loader, which holds
the `r`-th position in ascending order (the loader serializes positions sorted,
`PentaWrapLoader.index_word`); the honest cap proof lists its records in the same ascending order
(`capTranscriptBuilder`). The round trip (`PentaCapRoundtrip.expand_cap_proof`) depends on both.
The top four blocks of record `r` are written by `PentaWrapRecord.level_fill`, one level at a time,
from the doubled table; `expandByte` is the byte-level statement of the whole expansion. -/

namespace TwoPermutationPrototype.PentaWrap
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 100000

def TABLE : Nat := 268435456

def guardCode : List Instr :=
  [.BEQ .x16 .x0 1236, .ADDI .x30 .x0 912, .MUL .x30 .x16 .x30, .LUI .x31 2, .ADDI .x31 .x31 2784,
   .ADD .x31 .x30 .x31, .BNE .x17 .x31 1224, .ADD .x6 .x15 .x30, .LUI .x7 65536, .ADDI .x28 .x0 43]

/-- One table group: doubleword `m` goes to `+8m` and `+160+8m` of the doubled group, and the
source doubleword is cleared (for `k ≤ 17` the expansion is shorter than the cap proof). -/
def tableGroupCode : List Instr :=
  (List.range 20).flatMap fun m =>
    [.LD .x5 .x6 (BitVec.ofNat 12 (8*m)), .SD .x7 .x5 (BitVec.ofNat 12 (8*m)),
     .SD .x7 .x5 (BitVec.ofNat 12 (160+8*m)), .SD .x6 .x0 (BitVec.ofNat 12 (8*m))]

def tableLatchCode : List Instr := [.ADDI .x6 .x6 160, .ADDI .x7 .x7 320, .ADDI .x28 .x28 4095, .BNE .x28 .x0 7860]

def constantCode : List Instr :=
  [.LUI .x8 19, .ADDI .x8 .x8 301, .ADDI .x9 .x0 5, .ADDI .x18 .x0 320,
   .LUI .x19 65536, .ADDI .x19 .x19 32, .LUI .x20 65539, .ADDI .x20 .x20 1504,
   .LUI .x21 65540, .ADDI .x21 .x21 288, .LUI .x22 65540, .ADDI .x22 .x22 928]

def pointerCode : List Instr :=
  [.ADDI .x31 .x16 4095, .ADDI .x30 .x0 912, .MUL .x24 .x31 .x30, .ADD .x24 .x15 .x24,
   .ADDI .x30 .x0 1424, .MUL .x25 .x31 .x30, .ADD .x25 .x15 .x25, .SLLI .x26 .x31 3, .ADD .x26 .x13 .x26]

def copyCode : List Instr :=
  [.ADDI .x27 .x0 904, .ADD .x5 .x24 .x27, .LD .x5 .x5 0, .ADD .x6 .x25 .x27, .SD .x6 .x5 0,
   .ADDI .x27 .x27 4088, .BGE .x27 .x0 8172, .LD .x5 .x26 0, .DIVU .x6 .x5 .x8]

/-- Level `7 + lvl`: group and rotation from `x6 = index / 5^(7+lvl)`, base register `x(19+lvl)`,
16 doublewords to `912 + 128 lvl` of the expanded record, then `x6 = index / 5^(8+lvl)`. -/
def levelBase (lvl : Nat) : Reg := match lvl with | 0 => .x19 | 1 => .x20 | 2 => .x21 | _ => .x22

def levelFill (lvl : Nat) : List Instr :=
  [.DIVU .x7 .x6 .x9, .MUL .x28 .x7 .x9, .SUB .x28 .x6 .x28, .MUL .x29 .x7 .x18, .SLLI .x28 .x28 5,
   .ADD .x29 .x29 .x28, .ADD .x29 .x29 (levelBase lvl)] ++
  ((List.range 16).flatMap fun m =>
    [.LD .x31 .x29 (BitVec.ofNat 12 (8*m)), .SD .x25 .x31 (BitVec.ofNat 12 (912+128*lvl+8*m))]) ++
  [.ADDI .x6 .x7 0]

def latchCode : List Instr := [.ADDI .x24 .x24 3184, .ADDI .x25 .x25 2672, .ADDI .x26 .x26 4088, .BGEU .x26 .x13 7504]

def zeroedRegs : List Reg := [.x5, .x7, .x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27,
  .x28, .x29, .x30, .x31]

def restoreCode : List Instr :=
  [.ADDI .x6 .x0 1424, .MUL .x17 .x16 .x6] ++ zeroedRegs.map (fun r => .ADDI r .x0 0) ++ [.JAL .x0 2094084]

def emptyCode : List Instr := [.BNE .x17 .x0 12, .ADDI .x6 .x0 1424, .JAL .x0 2094072]

def rejectCode : List Instr := [.ADDI .x5 .x0 1, .ADDI .x10 .x0 1, .ECALL]

/-! ### The level 8-10 hash phase (wrapper offsets 315-3469)

The proof carries only the level-7 table (43 groups). After the table loop, offset 94 jumps to the
hash phase, which recomputes every node of levels 8, 9 and 10 into the doubled table: node `i` of the
54 is the penta hash of doubled group `i` (40 zero bytes, then the group's five slots, copied to the
scratch buffer `HB`), and its 32-byte digest goes to both copies of its slot. The scratch buffers are
cleared, `a0-a3` restored, `a7` raised by the 1,824 omitted bytes, and the displaced constants run
before the record loop. -/

def HB : Nat := 536870912

def hi20 (v : Nat) : BitVec 20 := BitVec.ofNat 20 ((v+2048)/4096)
def lo12 (v : Nat) : BitVec 12 := BitVec.ofNat 12 (v % 4096)

/-- Doubled group read by hash `i`. -/
def hashSrc (i : Nat) : Nat := TABLE + 320*i

/-- Slot (in doubled-table slot order) written by hash `i`: level 8, 9 or 10. -/
def hashSlot (i : Nat) : Nat := if i < 43 then 215 + i else if i < 52 then 260 + (i-43) else 270 + (i-52)

def hashDst (i : Nat) : Nat := TABLE + 320*(hashSlot i / 5) + 32*(hashSlot i % 5)

def hashSetup : List Instr :=
  [.ADDI .x18 .x10 0, .ADDI .x19 .x11 0, .ADDI .x20 .x12 0, .ADDI .x21 .x13 0, .LUI .x10 131072,
   .ADDI .x11 .x0 200, .LUI .x12 131072, .ADDI .x12 .x12 256, .ADDI .x13 .x0 1, .ADDI .x5 .x0 0,
   .ADDI .x22 .x6 0]

def hashBlock (i : Nat) : List Instr :=
  [.LUI .x6 (hi20 (hashSrc i)), .ADDI .x6 .x6 (lo12 (hashSrc i))] ++
  (List.range 20).flatMap (fun m =>
    [.LD .x31 .x6 (BitVec.ofNat 12 (8*m)), .SD .x10 .x31 (BitVec.ofNat 12 (8*(5+m)))]) ++
  [.ECALL, .LUI .x7 (hi20 (hashDst i)), .ADDI .x7 .x7 (lo12 (hashDst i))] ++
  (List.range 4).flatMap (fun m =>
    [.LD .x31 .x12 (BitVec.ofNat 12 (8*m)), .SD .x7 .x31 (BitVec.ofNat 12 (8*m)),
     .SD .x7 .x31 (BitVec.ofNat 12 (8*(20+m)))])

def hashClear : List Instr :=
  (List.range 20).map (fun m => .SD .x10 .x0 (BitVec.ofNat 12 (8*(5+m)))) ++
  (List.range 25).map (fun m => .SD .x12 .x0 (BitVec.ofNat 12 (8*m)))

def hashRestore : List Instr :=
  [.ADDI .x10 .x18 0, .ADDI .x11 .x19 0, .ADDI .x12 .x20 0, .ADDI .x13 .x21 0, .ADDI .x17 .x17 1824,
   .ADDI .x6 .x22 1920, .LUI .x7 (hi20 (TABLE+17600)), .ADDI .x7 .x7 (lo12 (TABLE+17600))]

def hashCode : List Instr :=
  hashSetup ++ (List.range 54).flatMap hashBlock ++ hashClear ++ hashRestore ++ constantCode ++
    [.JAL .x0 2083700]

/-- Words 460-3929 of the check image. -/
def wrapCode : List Instr :=
  guardCode ++ tableGroupCode ++ tableLatchCode ++ (.JAL .x0 884 :: constantCode.tail) ++ pointerCode ++
    copyCode ++ (List.range 4).flatMap levelFill ++ latchCode ++ restoreCode ++ emptyCode ++ rejectCode ++
    hashCode

theorem wrap_code_length : wrapCode.length = 3470 := by decide

/-- The image carries the wrapper at words 460-774 and the entry jump at word 0. -/
structure WrapImage (img : Image) : Prop where
  entry : (img.code[0]?).bind decodeInstruction = some (.base (.JAL .x0 1840))
  words : ∀ i < 3470, (img.code[460+i]?).bind decodeInstruction = (wrapCode[i]?).map Instruction.base

/-- Absolute word `460+i` of the wrapper as a fetch fact. -/
theorem wrap_fetch {img : Image} (wrap : WrapImage img) (state : MachineState) (i : Nat)
    (instruction : Instr) (code : wrapCode[i]? = some instruction)
    (pc : state.pc = BitVec.ofNat 64 (4096+4*(460+i))) :
    fetch img state = some (.base instruction) := by
  have bounded : i < 3470 := by
    rw [← wrap_code_length]
    exact (List.getElem?_eq_some_iff.mp code).1
  have decoded := wrap.words i bounded
  rw [code] at decoded
  have numeric : state.pc.toNat = 4096+4*(460+i) := by
    rw [pc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    omega
  rw [fetch, numeric, ite_eq_left (by omega), show (4096+4*(460+i)-4096)/4 = 460+i by omega]
  cases entry : img.code[460+i]? with
  | none => simp [entry] at decoded
  | some word => simpa only [entry, Option.bind_some, Option.map_some] using decoded

theorem entry_fetch {img : Image} (wrap : WrapImage img) (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 4096) :
    fetch img state = some (.base (.JAL .x0 1840)) := by
  have numeric : state.pc.toNat = 4096 := by rw [pc]; rfl
  rw [fetch, numeric, ite_eq_left (by omega), show (4096-4096)/4 = 0 by rfl]
  have decoded := wrap.entry
  cases entry : img.code[0]? with
  | none => simp [entry] at decoded
  | some word => simpa only [entry, Option.bind_some] using decoded

/-! ### Steps on an arbitrary image -/

/-- `before` runs to `after` in `steps` machine steps charging `cycles` cycles (check: no coins). -/
def Hop (img : Image) (before after : MachineState) (steps cycles : Nat) : Prop :=
  ∀ fuel, execute img (steps+fuel) before false = do
    let result ← execute img fuel after false
    return result.charge cycles 0

theorem Hop.zero (img : Image) (state : MachineState) : Hop img state state 0 0 := by
  intro fuel
  simp only [Nat.zero_add]
  cases h : execute img fuel state false <;> simp [Execution.charge]

theorem Hop.trans {img : Image} {s t u : MachineState} {a b c d : Nat}
    (first : Hop img s t a c) (last : Hop img t u b d) : Hop img s u (a+b) (c+d) := by
  intro fuel
  rw [Nat.add_assoc, first, last]
  simp only [bind_assoc, pure_bind, Execution.charge, Nat.zero_add, ← Nat.add_assoc]

theorem Hop.cast {img : Image} {s t : MachineState} {a b a' b' : Nat} (hop : Hop img s t a b)
    (ha : a = a') (hb : b = b') : Hop img s t a' b' := by
  subst ha hb
  exact hop

/-- Pure wrapper instructions: no memory access, branch, jump or system call. -/
def wrapPure : Instr → Bool
  | .ADDI .. | .SLLI .. | .ADD .. | .SUB .. | .LUI .. | .MUL .. | .DIVU .. | .SLTU .. | .XORI .. => true
  | _ => false

def wrapCost (code : List Instr) : Nat := (code.map fun instruction => instructionCycles (.base instruction)).sum

/-- `code` sits in the wrapper from wrapper offset `start` (absolute word `460+start`). -/
def WrapAt (start : Nat) (code : List Instr) : Prop := ∀ i < code.length, wrapCode[start+i]? = code[i]?

instance (start : Nat) (code : List Instr) : Decidable (WrapAt start code) := by
  unfold WrapAt
  infer_instance

theorem pure_ordinary (state : MachineState) (instruction : Instr) (pure : wrapPure instruction = true) :
    ordinaryStep state (.base instruction) = some (execInstrBr state instruction) := by
  cases instruction <;> simp [wrapPure] at pure <;> rfl

theorem pure_pc_step (state : MachineState) (instruction : Instr) (pure : wrapPure instruction = true) :
    (execInstrBr state instruction).pc = state.pc + 4 := by
  cases instruction <;> simp [wrapPure] at pure <;> rfl

theorem set_reg_mem (state : MachineState) (reg : Reg) (value : Word) :
    (state.setReg reg value).mem = state.mem := by cases reg <;> rfl

theorem pure_mem_step (state : MachineState) (instruction : Instr) (pure : wrapPure instruction = true) :
    (execInstrBr state instruction).mem = state.mem := by
  cases instruction <;> simp [wrapPure] at pure <;> simp [execInstrBr, set_reg_mem, MachineState.setPC]

theorem pc_add (start i : Nat) :
    BitVec.ofNat 64 (4096+4*(460+start)) + BitVec.ofNat 64 (4*i) = BitVec.ofNat 64 (4096+4*(460+(start+i))) := by
  rw [← BitVec.ofNat_add]
  congr 1
  omega

theorem pc_succ (start : Nat) :
    BitVec.ofNat 64 (4096+4*(460+start)) + 4 = BitVec.ofNat 64 (4096+4*(460+(start+1))) := by
  rw [show (4 : Word) = BitVec.ofNat 64 4 from rfl, ← BitVec.ofNat_add]
  congr 1

/-- One ordinary wrapper instruction. -/
theorem wrap_one {img : Image} (wrap : WrapImage img) (state : MachineState) (instruction : Instr) (i : Nat)
    (code : wrapCode[i]? = some instruction) (pc : state.pc = BitVec.ofNat 64 (4096+4*(460+i)))
    (stepped : ordinaryStep state (.base instruction) = some (execInstrBr state instruction)) :
    Hop img state (execInstrBr state instruction) 1 (instructionCycles (.base instruction)) := by
  intro fuel
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ (wrap_fetch wrap state i instruction code pc) stepped]

theorem wrap_pure_run {img : Image} (wrap : WrapImage img) :
    ∀ (code : List Instr) (start : Nat) (state : MachineState), WrapAt start code →
      state.pc = BitVec.ofNat 64 (4096+4*(460+start)) → code.all wrapPure = true →
      Hop img state (code.foldl execInstrBr state) code.length (wrapCost code)
  | [], _, state, _, _, _ => Hop.zero img state
  | first :: rest, start, state, at_, pc, pure => by
    have lines : wrapPure first = true ∧ rest.all wrapPure = true := by simpa using pure
    have head := wrap_one wrap state first start (by simpa using at_ 0 (by simp)) pc
      (pure_ordinary state first lines.1)
    have tail := wrap_pure_run wrap rest (start+1) (execInstrBr state first)
      (fun i h => by
        have := at_ (i+1) (by simp; omega)
        simpa [Nat.add_assoc, Nat.add_comm 1 i] using this)
      ((pure_pc_step state first lines.1).trans (by rw [pc, pc_succ])) lines.2
    exact (head.trans tail).cast (by simp [Nat.add_comm]) (by simp [wrapCost])

theorem wrap_pure_pc : ∀ (code : List Instr) (state : MachineState), code.all wrapPure = true →
    (code.foldl execInstrBr state).pc = state.pc + BitVec.ofNat 64 (4*code.length)
  | [], state, _ => by simp
  | first :: rest, state, pure => by
    have lines : wrapPure first = true ∧ rest.all wrapPure = true := by simpa using pure
    rw [List.foldl_cons, wrap_pure_pc rest _ lines.2, pure_pc_step state first lines.1, BitVec.add_assoc]
    congr 1
    rw [show (4 : Word) = BitVec.ofNat 64 4 from rfl, ← BitVec.ofNat_add]
    congr 1
    simp
    omega

theorem wrap_pure_mem : ∀ (code : List Instr) (state : MachineState), code.all wrapPure = true →
    (code.foldl execInstrBr state).mem = state.mem
  | [], _, _ => rfl
  | first :: rest, state, pure => by
    have lines : wrapPure first = true ∧ rest.all wrapPure = true := by simpa using pure
    rw [List.foldl_cons, wrap_pure_mem rest _ lines.2, pure_mem_step state first lines.1]

theorem get_reg_set_reg (state : MachineState) (rd rs : Reg) (value : Word) :
    (state.setReg rd value).getReg rs = if rd = rs ∧ rd ≠ .x0 then value else state.getReg rs := by
  by_cases same : rd = rs
  · subst rs
    by_cases zero : rd = .x0
    · subst rd
      rfl
    · simp [zero, MachineState.getReg_setReg_eq]
  · simp [same, MachineState.getReg_setReg_ne]

theorem get_reg_set_mem (state : MachineState) (address value : Word) (reg : Reg) :
    (state.setMem address value).getReg reg = state.getReg reg := by cases reg <;> rfl

/-- A branch or jump of the wrapper: one step, one cycle, registers and memory unchanged. -/
theorem wrap_control {img : Image} (wrap : WrapImage img) (state : MachineState) (instruction : Instr) (i : Nat)
    (code : wrapCode[i]? = some instruction) (pc : state.pc = BitVec.ofNat 64 (4096+4*(460+i)))
    (stepped : ordinaryStep state (.base instruction) = some (execInstrBr state instruction))
    (single : instructionCycles (.base instruction) = 1) :
    Hop img state (execInstrBr state instruction) 1 1 := by
  have h := wrap_one wrap state instruction i code pc stepped
  rwa [single] at h

/-- A doubleword load of the wrapper at an aligned in-range address. -/
theorem wrap_load {img : Image} (wrap : WrapImage img) (state : MachineState) (rd rs : Reg) (offset : BitVec 12)
    (i : Nat) (code : wrapCode[i]? = some (.LD rd rs offset)) (pc : state.pc = BitVec.ofNat 64 (4096+4*(460+i)))
    (address : Nat) (at_ : state.getReg rs + signExtend12 offset = BitVec.ofNat 64 address)
    (aligned : address % 8 = 0) (bounded : address + 8 ≤ MEMORY_BYTES) :
    Hop img state (execInstrBr state (.LD rd rs offset)) 1 1 ∧
      (execInstrBr state (.LD rd rs offset)).pc = BitVec.ofNat 64 (4096+4*(460+(i+1))) ∧
      (execInstrBr state (.LD rd rs offset)).mem = state.mem ∧
      (execInstrBr state (.LD rd rs offset)).getReg rd =
        (if rd = .x0 then 0 else state.getMem (BitVec.ofNat 64 address)) ∧
      ∀ r, r ≠ rd → (execInstrBr state (.LD rd rs offset)).getReg r = state.getReg r := by
  have valid : memoryArgumentsValid state (.LD rd rs offset) = true := by
    simp only [memoryArgumentsValid, memAccess, at_]
    unfold accessValid rangeValid
    have small : address < 2^64 := by unfold MEMORY_BYTES at bounded; omega
    simp [BitVec.toNat_ofNat, aligned]
    omega
  have stepped : ordinaryStep state (.base (.LD rd rs offset)) = some (execInstrBr state (.LD rd rs offset)) := by
    simp [ordinaryStep, valid]
  refine ⟨wrap_control wrap state _ i code pc stepped rfl, ?_, ?_, ?_, ?_⟩
  · simp only [execInstrBr]
    show state.pc + 4 = _
    rw [pc, pc_succ]
  · simp only [execInstrBr]
    exact set_reg_mem _ _ _
  · simp only [execInstrBr, MachineState.getReg_setPC, get_reg_set_reg, at_]
    by_cases zero : rd = .x0
    · subst zero
      rfl
    · simp [zero]
  · intro r other
    simp only [execInstrBr, MachineState.getReg_setPC, get_reg_set_reg]
    simp [Ne.symm other]

/-- A doubleword store of the wrapper at an aligned in-range address. -/
theorem wrap_store {img : Image} (wrap : WrapImage img) (state : MachineState) (base value : Reg) (offset : BitVec 12)
    (i : Nat) (code : wrapCode[i]? = some (.SD base value offset)) (pc : state.pc = BitVec.ofNat 64 (4096+4*(460+i)))
    (word : Nat) (at_ : state.getReg base + signExtend12 offset = TwoPermutationPrototype.RV64.wordAddress word)
    (bounded : 8*word + 8 ≤ MEMORY_BYTES) :
    Hop img state (execInstrBr state (.SD base value offset)) 1 1 ∧
      (execInstrBr state (.SD base value offset)).pc = BitVec.ofNat 64 (4096+4*(460+(i+1))) ∧
      (∀ w < 2^61, TwoPermutationPrototype.RV64.memoryView (execInstrBr state (.SD base value offset)) w =
        if w = word then state.getReg value else TwoPermutationPrototype.RV64.memoryView state w) ∧
      ∀ r, (execInstrBr state (.SD base value offset)).getReg r = state.getReg r := by
  have small : 8*word < 2^64 := by unfold MEMORY_BYTES at bounded; omega
  have valid : memoryArgumentsValid state (.SD base value offset) = true := by
    simp only [memoryArgumentsValid, memAccess, at_]
    unfold accessValid rangeValid TwoPermutationPrototype.RV64.wordAddress
    simp [BitVec.toNat_ofNat]
    omega
  have stepped : ordinaryStep state (.base (.SD base value offset)) =
      some (execInstrBr state (.SD base value offset)) := by
    simp [ordinaryStep, valid]
  refine ⟨wrap_control wrap state _ i code pc stepped rfl, ?_, ?_, ?_⟩
  · simp only [execInstrBr]
    show state.pc + 4 = _
    rw [pc, pc_succ]
  · intro w hw
    have stored := TwoPermutationPrototype.RV64.memory_at_store (state := state) (value := state.getReg value)
      (address := word) (index := w) (by omega) hw
    simp only [execInstrBr, at_]
    have pcFree : ∀ (t : MachineState) (p : Word), TwoPermutationPrototype.RV64.memoryView (t.setPC p) =
        TwoPermutationPrototype.RV64.memoryView t := fun _ _ => rfl
    rw [pcFree, stored]
    rfl
  · intro r
    simp only [execInstrBr, MachineState.getReg_setPC]
    exact get_reg_set_mem _ _ _ _

end TwoPermutationPrototype.PentaWrap
