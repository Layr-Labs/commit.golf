import CommitGolfCandidate.CapWordCopy
import CommitGolfCandidate.CapCheckLeafTail
import CommitGolfCandidate.S3CheckLeafSteps

/-! The stage-3 checker leaf at words 257..346 of the cap check image: its
exact words, the decoded straight-line segments between the two permutation
calls, and the fetch facts. Each fact decodes the image's actual words. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- The 90 words of `s3LeafSubroutine`. -/
def s3LeafWords : List (BitVec 32) :=
  [0x00000313, 0x00000313, 0x00000313, 0x00000313, 0x00000313, 0x00000313,
   0x00000313, 0x00000313, 0x00000313, 0x00000313, 0x00000313, 0x00000313,
   0x00000313, 0x00000313, 0x00000313, 0x00000313, 0x00000313, 0x00000313,
   0x00000313, 0x00000313, 0x00000313, 0x00000313, 0x00000293, 0x00040513,
   0x0c800593, 0x00000613, 0x00100693, 0x00000073, 0x07803303, 0x00603023,
   0x08003303, 0x00603423, 0x08803303, 0x00603823, 0x09003303, 0x00603c23,
   0x09803303, 0x02603023, 0x0a003303, 0x02603423, 0x0a803303, 0x02603823,
   0x10003303, 0x02603c23, 0x10803303, 0x04603023, 0x11003303, 0x04603423,
   0x08843303, 0x04603823, 0x09043303, 0x04603c23, 0x09843303, 0x06603023,
   0x0a043303, 0x06603423, 0x0a843303, 0x06603823, 0x0b043303, 0x06603c23,
   0x0b843303, 0x08603023, 0x0c043303, 0x08603423, 0x0c843303, 0x08603823,
   0x0d043303, 0x08603c23, 0x0d843303, 0x0a603023, 0x0e043303, 0x0a603423,
   0x0e843303, 0x0a603823, 0x0f043303, 0x0a603c23, 0x0f843303, 0x0c603023,
   0x00000513, 0x00000073, 0x00003303, 0x10603023, 0x00803303, 0x10603423,
   0x01003303, 0x10603823, 0x01803303, 0x10603c23, 0x10040413, 0x00008067]

/-- Load a word through x6 and store it at an absolute address. -/
def s3Copy (base : Reg) (pairs : List (Nat × Nat)) : List Instr :=
  pairs.flatMap fun pair =>
    [.LD .x6 base (BitVec.ofNat 12 pair.1), .SD .x0 .x6 (BitVec.ofNat 12 pair.2)]

def s3ChainPairs : List (Nat × Nat) := (List.range 7).map fun word => (120 + 8 * word, 8 * word)
def s3NoncePairs : List (Nat × Nat) := (List.range 3).map fun word => (256 + 8 * word, 56 + 8 * word)
def s3TailPairs : List (Nat × Nat) := (List.range 15).map fun word => (136 + 8 * word, 80 + 8 * word)
def s3OutputPairs : List (Nat × Nat) := (List.range 4).map fun word => (8 * word, 256 + 8 * word)

/-- Words 257..278: fillers that keep the routine at the record's 90 instructions. -/
def s3LeafPadding : List Instr := List.replicate 22 (.ADDI .x6 .x0 0)

/-- Words 279..283: forward-permutation selectors, input at the value (x8), output at 0. -/
def s3LeafSelectors : List Instr :=
  [.ADDI .x5 .x0 0, .ADDI .x10 .x8 0, .ADDI .x11 .x0 200, .ADDI .x12 .x0 0, .ADDI .x13 .x0 1]

/-- Words 257..283, up to the first ECALL at word 284. -/
def s3LeafBuild : List Instr := s3LeafPadding ++ s3LeafSelectors

/-- Words 285..298: reply words 15..21 (bytes 120..176) to addresses 0..48. -/
def s3LeafChainCopy : List Instr := s3Copy .x0 s3ChainPairs

/-- Words 299..304: the three nonce words from scratch 256..272 to 56..72. -/
def s3LeafNonce : List Instr := s3Copy .x0 s3NoncePairs

/-- Words 305..334: value words 17..31 to addresses 80..192. -/
def s3CheckLeafTail : List Instr := s3Copy .x8 s3TailPairs

/-- Words 285..335, up to the second ECALL at word 336. -/
def s3LeafChain : List Instr :=
  s3LeafChainCopy ++ s3LeafNonce ++ s3CheckLeafTail ++ [.ADDI .x10 .x0 0]

/-- Words 337..344: the four digest words from 0..24 to scratch 256..280. -/
def s3LeafOutput : List Instr := s3Copy .x0 s3OutputPairs

/-- Words 337..345, up to the return at word 346. -/
def s3LeafFinish : List Instr := s3LeafOutput ++ [.ADDI .x8 .x8 256]

theorem s3_leaf_build_length : s3LeafBuild.length = 27 := by decide
theorem s3_leaf_chain_length : s3LeafChain.length = 51 := by decide
theorem s3_leaf_finish_length : s3LeafFinish.length = 9 := by decide

theorem s3_leaf_words :
    ((capExperimental 24).image .check).code.drop 257 = s3LeafWords := by decide

theorem s3_leaf_word (i : Nat) :
    ((capExperimental 24).image .check).code[257 + i]? = s3LeafWords[i]? := by
  rw [← List.getElem?_drop, s3_leaf_words]

theorem s3_leaf_build_decoded : ∀ i (inside : i < s3LeafBuild.length),
    (((capExperimental 24).image .check).code[257 + i]?).bind decodeInstruction =
      some (.base s3LeafBuild[i]) := by
  intro i inside
  have small : i < 27 := by simpa only [s3_leaf_build_length] using inside
  rw [s3_leaf_word]
  interval_cases i <;> rfl

theorem s3_leaf_chain_decoded : ∀ i (inside : i < s3LeafChain.length),
    (((capExperimental 24).image .check).code[285 + i]?).bind decodeInstruction =
      some (.base s3LeafChain[i]) := by
  intro i inside
  have small : i < 51 := by simpa only [s3_leaf_chain_length] using inside
  rw [show 285 + i = 257 + (28 + i) by omega, s3_leaf_word]
  interval_cases i <;> rfl

theorem s3_leaf_finish_decoded : ∀ i (inside : i < s3LeafFinish.length),
    (((capExperimental 24).image .check).code[337 + i]?).bind decodeInstruction =
      some (.base s3LeafFinish[i]) := by
  intro i inside
  have small : i < 9 := by simpa only [s3_leaf_finish_length] using inside
  rw [show 337 + i = 257 + (80 + i) by omega, s3_leaf_word]
  interval_cases i <;> rfl

theorem s3_leaf_call_fetched (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * 284) ∨
      state.pc = BitVec.ofNat 64 (4096 + 4 * 336)) :
    fetch ((capExperimental 24).image .check) state = some (.base .ECALL) := by
  rcases pc with pc | pc
  · apply cap_image_fetch _ state 284 _ (by decide) pc
    rw [show 284 = 257 + 27 by rfl, s3_leaf_word]
    rfl
  · apply cap_image_fetch _ state 336 _ (by decide) pc
    rw [show 336 = 257 + 79 by rfl, s3_leaf_word]
    rfl

theorem s3_leaf_return_fetched (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * 346)) :
    fetch ((capExperimental 24).image .check) state = some (.base (.JALR .x0 .x1 0)) := by
  apply cap_image_fetch _ state 346 _ (by decide) pc
  rw [show 346 = 257 + 89 by rfl, s3_leaf_word]
  rfl

theorem s3_leaf_build_checked : s3Checked true s3LeafBuild = true := by decide
theorem s3_leaf_chain_checked : s3Checked true s3LeafChain = true := by decide
theorem s3_leaf_finish_checked : s3Checked false s3LeafFinish = true := by decide

end CommitGolfCandidate
