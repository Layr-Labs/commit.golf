import CommitGolfCandidate.NonceCompressedPrograms
import CommitGolfCandidate.Execution
import CommitGolfCandidate.NonceCompactHalfword

/-! Instruction fetches of the compaction (opening words 192..256) and the run relation used to
compose its blocks. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- The delivered opening image. -/
abbrev s6OpeningImage : Image := nonceCompressedProgram.image .opening

/-- Opening words 192..256. -/
def s6CompactWords : List (BitVec 32) := [
    822035, 494483, 494739, 527379, 34343523, 8392211, 79692015, 17533843,
    67112467, 67109103, 13635219, 88080623, 2853779, 4294872723, 4262370019, 4294708243,
    4228651747, 23824483, 58720495, 2853779, 4284477551, 1090291123, 1049235, 1299,
    115, 774915, 7114787, 2853779, 2919571, 4294839827, 4262336227, 32871,
    774915, 7114787, 2872067, 7115043, 4969219, 7115299, 7066371, 7115555,
    9163523, 7115811, 11260675, 7116067, 13357827, 7116323, 15454979, 7116579,
    17552131, 7116835, 19649283, 7117091, 21746435, 7117347, 23843587, 7117603,
    25940739, 7117859, 28037891, 7118115, 30135043, 7118371, 32213907, 32279699,
    32871]

/-- Decoded opening words 192..256. -/
def s6CompactInstrs : List Instr :=
  [.ADDI .x22 .x25 0, .ADDI .x23 .x15 0, .ADDI .x25 .x15 0, .ADDI .x24 .x16 0, .BEQ .x24 .x0 52,
   .ADDI .x28 .x0 8, .JAL .x1 76, .ADDI .x23 .x23 16, .ADDI .x28 .x0 64, .JAL .x1 64,
   .ADDI .x29 .x0 13, .JAL .x1 84, .ADDI .x23 .x23 2, .ADDI .x29 .x29 4095, .BNE .x29 .x0 8180,
   .ADDI .x24 .x24 4095, .BNE .x24 .x0 8148, .BEQ .x23 .x22 16, .JAL .x1 56, .ADDI .x23 .x23 2,
   .JAL .x0 2097140, .SUB .x11 .x25 .x15, .ADDI .x5 .x0 1, .ADDI .x10 .x0 0, .ECALL,
   .LHU .x6 .x23 0, .SH .x25 .x6 0, .ADDI .x23 .x23 2, .ADDI .x25 .x25 2, .ADDI .x28 .x28 4095,
   .BNE .x28 .x0 8172, .JALR .x0 .x1 0] ++
  ((List.range 15).flatMap fun j =>
    [.LHU .x6 .x23 (BitVec.ofNat 12 (2 * j)), .SH .x25 .x6 (BitVec.ofNat 12 (2 * j))]) ++
  [.ADDI .x23 .x23 30, .ADDI .x25 .x25 30, .JALR .x0 .x1 0]

theorem s6_opening_code_drop : s6OpeningImage.code.drop 192 = s6CompactWords := by
  decide

theorem s6_opening_code_length : s6OpeningImage.code.length = 257 := by
  decide

theorem s6_opening_word_jump : s6OpeningImage.code[110]? = some 343933039 := by
  decide

theorem s6_compact_decode (k : Nat) (inside : k < 65) :
    (s6CompactWords[k]?).bind decodeInstruction = some (.base (s6CompactInstrs.getD k .EBREAK)) := by
  interval_cases k <;> rfl

theorem s6_image_fetch (image : Image) (state : MachineState) (index : Nat) (word : BitVec 32)
    (bounded : index < 1024) (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * index))
    (entry : image.code[index]? = some word) :
    fetch image state = decodeInstruction word := by
  have numeric : state.pc.toNat = 4096 + 4 * index := by
    rw [pc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    omega
  rw [fetch, numeric, if_pos (by omega)]
  rw [show (4096 + 4 * index - 4096) / 4 = index by omega, entry]

theorem s6_compact_fetch (state : MachineState) (k : Nat) (inside : k < 65)
    (pc : state.pc = BitVec.ofNat 64 (4864 + 4 * k)) :
    fetch s6OpeningImage state = some (.base (s6CompactInstrs.getD k .EBREAK)) := by
  have entry : s6OpeningImage.code[192 + k]? = s6CompactWords[k]? := by
    rw [← s6_opening_code_drop, List.getElem?_drop]
  have decoded := s6_compact_decode k inside
  cases word : s6CompactWords[k]? with
  | none => rw [word] at decoded; contradiction
  | some value =>
    rw [word, Option.bind_some] at decoded
    rw [s6_image_fetch s6OpeningImage state (192 + k) value (by omega)
      (by rw [pc]; congr 1; omega) (entry.trans word), decoded]

/-- `state` runs `steps` one-cycle instructions to `next`. -/
def NonceRuns (image : Image) (steps : Nat) (state next : MachineState) : Prop :=
  ∀ fuel coins, execute image (steps + fuel) state coins =
    (do let result ← execute image fuel next coins
        return result.charge steps 0)

theorem nonce_runs_zero (image : Image) (state : MachineState) : NonceRuns image 0 state state := by
  intro fuel coins
  simp [Execution.charge]

theorem nonce_runs_trans {image : Image} {first second : Nat} {state middle next : MachineState}
    (left : NonceRuns image first state middle) (right : NonceRuns image second middle next) :
    NonceRuns image (first + second) state next := by
  intro fuel coins
  rw [show first + second + fuel = first + (second + fuel) by omega, left, right]
  simp only [bind_assoc, pure_bind]
  congr 1
  funext result
  simp only [Execution.charge, Nat.zero_add, Nat.add_assoc]

theorem nonce_runs_step {image : Image} {state next : MachineState} {instruction : Instr}
    (fetched : fetch image state = some (.base instruction))
    (stepped : ordinaryStep state (.base instruction) = some next)
    (cycles : instructionCycles (.base instruction) = 1) :
    NonceRuns image 1 state next := by
  intro fuel coins
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ fetched stepped, cycles]

/-- One compaction instruction that is not a memory access. -/
theorem s6_runs_plain (state : MachineState) (k : Nat) (inside : k < 65)
    (pc : state.pc = BitVec.ofNat 64 (4864 + 4 * k))
    (plain : memAccess state (s6CompactInstrs.getD k .EBREAK) = none)
    (ordinary : ∀ s, ordinaryStep s (.base (s6CompactInstrs.getD k .EBREAK)) =
      if memoryArgumentsValid s (s6CompactInstrs.getD k .EBREAK) then
        some (execInstrBr s (s6CompactInstrs.getD k .EBREAK)) else none)
    (cycles : instructionCycles (.base (s6CompactInstrs.getD k .EBREAK)) = 1) :
    NonceRuns s6OpeningImage 1 state (execInstrBr state (s6CompactInstrs.getD k .EBREAK)) := by
  apply nonce_runs_step (s6_compact_fetch state k inside pc) _ cycles
  rw [ordinary, memoryArgumentsValid, plain, if_pos rfl]

end CommitGolfCandidate
