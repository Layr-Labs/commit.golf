import CommitGolfCandidate.CapWordCopy
import CommitGolfCandidate.CapCheckLeafTail
import CommitGolfCandidate.S3CheckLeafSteps

/-! The checker leaf at words 257..439 of the cap check image: its exact
words, the decoded straight-line segments between the three permutation calls,
the four group-place blocks, and the fetch facts. Each fact decodes the image's
actual words. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- The 183 words of `s3LeafSubroutine`. -/
def s3LeafWords : List (BitVec 32) :=
  [0x10003303, 0x00603023, 0x10803303, 0x00603423, 0x11003303, 0x00603823,
   0x00043303, 0x00603c23, 0x00843303, 0x02603023, 0x01043303, 0x02603423,
   0x01843303, 0x02603823, 0x02043303, 0x02603c23, 0x02843303, 0x04603023,
   0x03043303, 0x04603423, 0x03843303, 0x04603823, 0x04043303, 0x04603c23,
   0x04843303, 0x06603023, 0x05043303, 0x06603423, 0x05843303, 0x06603823,
   0x06043303, 0x06603c23, 0x06843303, 0x08603023, 0x07043303, 0x08603423,
   0x07843303, 0x08603823, 0x08043303, 0x08603c23, 0x08843303, 0x0a603023,
   0x09043303, 0x0a603423, 0x09843303, 0x0a603823, 0x0a043303, 0x0a603c23,
   0x0a843303, 0x0c603023, 0x00000293, 0x00000513, 0x0c800593, 0x00000613,
   0x00100693, 0x00000073, 0x08803303, 0x02603c23, 0x09003303, 0x04603023,
   0x09803303, 0x04603423, 0x0a003303, 0x04603823, 0x0a803303, 0x04603c23,
   0x0b003303, 0x06603023, 0x0b803303, 0x06603423, 0x0c003303, 0x06603823,
   0x07843303, 0x06603c23, 0x08043303, 0x08603023, 0x08843303, 0x08603423,
   0x09043303, 0x08603823, 0x09843303, 0x08603c23, 0x0a043303, 0x0a603023,
   0x0a843303, 0x0a603423, 0x0b043303, 0x0a603823, 0x0b843303, 0x0a603c23,
   0x0c043303, 0x0c603023, 0x0c843303, 0x0c603423, 0x0d043303, 0x0c603823,
   0x0d843303, 0x0c603c23, 0x0e043303, 0x0e603023, 0x0e843303, 0x0e603423,
   0x0f043303, 0x0e603823, 0x0f843303, 0x0e603c23, 0x03800513, 0x00000073,
   0x003a7393, 0x00539393, 0x00003303, 0x0863b023, 0x00803303, 0x0863b423,
   0x01003303, 0x0863b823, 0x01803303, 0x0863bc23, 0x00000313, 0x02730463,
   0x000cb303, 0x08603023, 0x008cb303, 0x08603423, 0x010cb303, 0x08603823,
   0x018cb303, 0x08603c23, 0x020c8c93, 0x02000313, 0x02730463, 0x000cb303,
   0x0a603023, 0x008cb303, 0x0a603423, 0x010cb303, 0x0a603823, 0x018cb303,
   0x0a603c23, 0x020c8c93, 0x04000313, 0x02730463, 0x000cb303, 0x0c603023,
   0x008cb303, 0x0c603423, 0x010cb303, 0x0c603823, 0x018cb303, 0x0c603c23,
   0x020c8c93, 0x06000313, 0x02730463, 0x000cb303, 0x0e603023, 0x008cb303,
   0x0e603423, 0x010cb303, 0x0e603823, 0x018cb303, 0x0e603c23, 0x020c8c93,
   0x02003c23, 0x04003023, 0x04003423, 0x04003823, 0x04003c23, 0x06003023,
   0x06003423, 0x06003823, 0x06003c23, 0x00000073, 0x00003303, 0x10603023,
   0x00803303, 0x10603423, 0x01003303, 0x10603823, 0x01803303, 0x10603c23,
   0x002a5a13, 0x10040413, 0x00008067]

/-- Load a word through x6 and store it at an absolute address. -/
def s3Copy (base : Reg) (pairs : List (Nat × Nat)) : List Instr :=
  pairs.flatMap fun pair =>
    [.LD .x6 base (BitVec.ofNat 12 pair.1), .SD .x0 .x6 (BitVec.ofNat 12 pair.2)]

/-- Load a word through x6 and store it relative to a target register. -/
def s6CopyAt (base target : Reg) (pairs : List (Nat × Nat)) : List Instr :=
  pairs.flatMap fun pair =>
    [.LD .x6 base (BitVec.ofNat 12 pair.1), .SD target .x6 (BitVec.ofNat 12 pair.2)]

def s3SaltPairs : List (Nat × Nat) := (List.range 3).map fun word => (256 + 8 * word, 8 * word)
def s3HeadPairs : List (Nat × Nat) := (List.range 22).map fun word => (8 * word, 24 + 8 * word)
def s3RelayPairs : List (Nat × Nat) := (List.range 8).map fun word => (136 + 8 * word, 56 + 8 * word)
def s3TailPairs : List (Nat × Nat) :=
  (List.range 17).map fun word => (120 + 8 * word, 120 + 8 * word)
def s6OwnPairs : List (Nat × Nat) := (List.range 4).map fun word => (8 * word, 128 + 8 * word)
def s6PlacePairs (place : Nat) : List (Nat × Nat) :=
  (List.range 4).map fun word => (8 * word, 128 + 32 * place + 8 * word)
def s3OutputPairs : List (Nat × Nat) := (List.range 4).map fun word => (8 * word, 256 + 8 * word)

/-- Forward-permutation selectors with input and output at address 0. -/
def s3LeafSelect : List Instr :=
  [.ADDI .x5 .x0 0, .ADDI .x10 .x0 0, .ADDI .x11 .x0 200, .ADDI .x12 .x0 0, .ADDI .x13 .x0 1]

/-- Words 257..311, up to the first ECALL at word 312: the salt words (nonce
and tag) to 0..24, value words 0..21 to 24..200, then the selectors. -/
def s3LeafBuild : List Instr := s3Copy .x0 s3SaltPairs ++ s3Copy .x8 s3HeadPairs ++ s3LeafSelect

/-- Words 313..363, up to the second ECALL at word 364: reply bytes 136..200
to 56..120, value words 15..31 to 120..256, input address 56. -/
def s3LeafChain : List Instr :=
  s3Copy .x0 s3RelayPairs ++ s3Copy .x8 s3TailPairs ++ [.ADDI .x10 .x0 56]

/-- Words 365..366: x7 = 32 * (position mod 4), the offset of the leaf's place. -/
def s6LeafSlot : List Instr := [.ANDI .x7 .x20 3, .SLLI .x7 .x7 5]

/-- Words 367..374: the leaf digest to its place at 128 + x7. -/
def s6LeafOwn : List Instr := s6CopyAt .x0 .x7 s6OwnPairs

/-- First two words of place block `place` (word 375 + 11 * place): skip the
block when it is the leaf's own place. -/
def s6PlaceTest (place : Nat) : List Instr :=
  [.ADDI .x6 .x0 (BitVec.ofNat 12 (32 * place)), .BEQ .x6 .x7 40]

/-- The other nine words: the next record digest at x25 to place `place`. -/
def s6PlaceCopy (place : Nat) : List Instr :=
  s3Copy .x25 (s6PlacePairs place) ++ [.ADDI .x25 .x25 32]

/-- Words 419..427: 72 zero bytes at 56..128, up to the third ECALL at word 428. -/
def s6LeafClear : List Instr :=
  (List.range 9).map fun word => .SD .x0 .x0 (BitVec.ofNat 12 (56 + 8 * word))

/-- Words 429..438, up to the return at word 439: the group digest to scratch
256..288, the group index, and the value cursor. -/
def s3LeafFinish : List Instr :=
  s3Copy .x0 s3OutputPairs ++ [.SRLI .x20 .x20 2, .ADDI .x8 .x8 256]

theorem s3_leaf_build_length : s3LeafBuild.length = 55 := by decide
theorem s3_leaf_chain_length : s3LeafChain.length = 51 := by decide
theorem s6_leaf_slot_length : s6LeafSlot.length = 2 := by decide
theorem s6_leaf_own_length : s6LeafOwn.length = 8 := by decide
theorem s6_place_copy_length (place : Nat) : (s6PlaceCopy place).length = 9 := rfl
theorem s6_leaf_clear_length : s6LeafClear.length = 9 := by decide
theorem s3_leaf_finish_length : s3LeafFinish.length = 10 := by decide

theorem s3_leaf_words :
    (((capExperimental 24).image .check).code.drop 257).take 183 = s3LeafWords := by decide

theorem s3_leaf_word (i : Nat) (inside : i < 183) :
    ((capExperimental 24).image .check).code[257 + i]? = s3LeafWords[i]? := by
  rw [← s3_leaf_words, List.getElem?_take, if_pos inside, List.getElem?_drop]

theorem s3_leaf_build_decoded : ∀ i (inside : i < s3LeafBuild.length),
    (((capExperimental 24).image .check).code[257 + i]?).bind decodeInstruction =
      some (.base s3LeafBuild[i]) := by
  intro i inside
  have small : i < 55 := by simpa only [s3_leaf_build_length] using inside
  rw [s3_leaf_word i (by omega)]
  interval_cases i <;> rfl

theorem s3_leaf_chain_decoded : ∀ i (inside : i < s3LeafChain.length),
    (((capExperimental 24).image .check).code[313 + i]?).bind decodeInstruction =
      some (.base s3LeafChain[i]) := by
  intro i inside
  have small : i < 51 := by simpa only [s3_leaf_chain_length] using inside
  rw [show 313 + i = 257 + (56 + i) by omega, s3_leaf_word _ (by omega)]
  interval_cases i <;> rfl

theorem s6_leaf_slot_decoded : ∀ i (inside : i < s6LeafSlot.length),
    (((capExperimental 24).image .check).code[365 + i]?).bind decodeInstruction =
      some (.base s6LeafSlot[i]) := by
  intro i inside
  have small : i < 2 := by simpa only [s6_leaf_slot_length] using inside
  rw [show 365 + i = 257 + (108 + i) by omega, s3_leaf_word _ (by omega)]
  interval_cases i <;> rfl

theorem s6_leaf_own_decoded : ∀ i (inside : i < s6LeafOwn.length),
    (((capExperimental 24).image .check).code[367 + i]?).bind decodeInstruction =
      some (.base s6LeafOwn[i]) := by
  intro i inside
  have small : i < 8 := by simpa only [s6_leaf_own_length] using inside
  rw [show 367 + i = 257 + (110 + i) by omega, s3_leaf_word _ (by omega)]
  interval_cases i <;> rfl

theorem s6_place_addi_decoded (place : Nat) (small : place < 4) :
    (((capExperimental 24).image .check).code[375 + 11 * place]?).bind decodeInstruction =
      some (.base (.ADDI .x6 .x0 (BitVec.ofNat 12 (32 * place)))) := by
  rw [show 375 + 11 * place = 257 + (118 + 11 * place) by omega, s3_leaf_word _ (by omega)]
  interval_cases place <;> rfl

theorem s6_place_branch_decoded (place : Nat) (small : place < 4) :
    (((capExperimental 24).image .check).code[376 + 11 * place]?).bind decodeInstruction =
      some (.base (.BEQ .x6 .x7 40)) := by
  rw [show 376 + 11 * place = 257 + (119 + 11 * place) by omega, s3_leaf_word _ (by omega)]
  interval_cases place <;> rfl

theorem s6_place_copy_decoded (place : Nat) (small : place < 4) :
    ∀ i (inside : i < (s6PlaceCopy place).length),
    (((capExperimental 24).image .check).code[377 + 11 * place + i]?).bind decodeInstruction =
      some (.base (s6PlaceCopy place)[i]) := by
  intro i inside
  have few : i < 9 := by simpa only [s6_place_copy_length] using inside
  rw [show 377 + 11 * place + i = 257 + (120 + 11 * place + i) by omega,
    s3_leaf_word _ (by omega)]
  interval_cases place <;> interval_cases i <;> rfl

theorem s6_leaf_clear_decoded : ∀ i (inside : i < s6LeafClear.length),
    (((capExperimental 24).image .check).code[419 + i]?).bind decodeInstruction =
      some (.base s6LeafClear[i]) := by
  intro i inside
  have small : i < 9 := by simpa only [s6_leaf_clear_length] using inside
  rw [show 419 + i = 257 + (162 + i) by omega, s3_leaf_word _ (by omega)]
  interval_cases i <;> rfl

theorem s3_leaf_finish_decoded : ∀ i (inside : i < s3LeafFinish.length),
    (((capExperimental 24).image .check).code[429 + i]?).bind decodeInstruction =
      some (.base s3LeafFinish[i]) := by
  intro i inside
  have small : i < 10 := by simpa only [s3_leaf_finish_length] using inside
  rw [show 429 + i = 257 + (172 + i) by omega, s3_leaf_word _ (by omega)]
  interval_cases i <;> rfl

theorem s3_leaf_call_fetched (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * 312) ∨
      state.pc = BitVec.ofNat 64 (4096 + 4 * 364) ∨
      state.pc = BitVec.ofNat 64 (4096 + 4 * 428)) :
    fetch ((capExperimental 24).image .check) state = some (.base .ECALL) := by
  rcases pc with pc | pc | pc
  · apply cap_image_fetch _ state 312 _ (by decide) pc
    rw [show 312 = 257 + 55 by rfl, s3_leaf_word _ (by decide)]
    rfl
  · apply cap_image_fetch _ state 364 _ (by decide) pc
    rw [show 364 = 257 + 107 by rfl, s3_leaf_word _ (by decide)]
    rfl
  · apply cap_image_fetch _ state 428 _ (by decide) pc
    rw [show 428 = 257 + 171 by rfl, s3_leaf_word _ (by decide)]
    rfl

theorem s3_leaf_return_fetched (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * 439)) :
    fetch ((capExperimental 24).image .check) state = some (.base (.JALR .x0 .x1 0)) := by
  apply cap_image_fetch _ state 439 _ (by decide) pc
  rw [show 439 = 257 + 182 by rfl, s3_leaf_word _ (by decide)]
  rfl

theorem s3_leaf_build_checked : s3Checked .x8 32 true s3LeafBuild = true := by decide
theorem s3_leaf_chain_checked : s3Checked .x8 32 true s3LeafChain = true := by decide
theorem s6_leaf_slot_checked : s3Checked .x7 20 false s6LeafSlot = true := by decide
theorem s6_leaf_own_checked : s3Checked .x7 20 true s6LeafOwn = true := by decide
theorem s6_place_copy_checked (place : Nat) (small : place < 4) :
    s3Checked .x25 4 true (s6PlaceCopy place) = true := by
  interval_cases place <;> decide
theorem s6_leaf_clear_checked : s3Checked .x8 32 false s6LeafClear = true := by decide
theorem s3_leaf_finish_checked : s3Checked .x8 32 false s3LeafFinish = true := by decide

end CommitGolfCandidate
