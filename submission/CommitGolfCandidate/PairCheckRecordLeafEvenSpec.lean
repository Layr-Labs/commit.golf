import CommitGolfCandidate.PairCheckRecordLeafCalls
import CommitGolfCandidate.PairCheckBinding

/-! # Pair-heads checker: the even leaf path (words 494–542), specification

The state machine of the even path and the facts the leaf block needs from it (`EvenPathFacts`). The parity branch
(words 44–45) jumps here with the same registers as the odd path; the path ends with `jal zero,58` at the quartet
block entry 0x10e8 with the leaf digest at 12288.

    494 lui t5,0x100            ; Y = 0x100000 (word 131072)
    495 addi a0,a0,96           ; first-call input = value bytes 56..256 (word src+12)
    496 addi a2,t5,-152         ; first-call reply at Y-152 (word 131053), so reply words 20..24 land at Y+8
    497 ecall                   ; P(v[56..256))
    498 addi a0,a0,-96
    499 addi t6,t3,-8           ; tag = M-48 = 4048+256·i (evenPositionTag)
    500 sd t6,0(t5)
    501..534  17 × (ld t6,40+8j(a0); sd t6,48+8j(t5))   ; value words 0..16 to Y+48..Y+184
    535..538  ld t6,0(tp); sd t6,184(t5); ld t6,8(tp); sd t6,192(t5)   ; salt words
    539 addi a0,t5,0
    540 addi a2,s7,0            ; digest at 12288
    541 ecall                   ; P(tag | R1[160..200) | v[0..136) | s)
    542 jal zero,-1936          ; to word 58
-/

namespace TwoPermutationPrototype.PairCk.Packed.RecordLeaf
open TwoPermutationPrototype.Packed
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp OracleSpec
open TwoPermutationPrototype.PairCk.Packed.Checker (pairImage)
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
set_option maxRecDepth 8192

/-- The even-path entry (word 494): the odd path's `LeafReady` registers at the even target. -/
structure EvenReady (state : MachineState) (src nonce : Nat) (index : Index) : Prop where
  pc : state.pc = BitVec.ofNat 64 (4096+4*494)
  source : state.getReg .x10 = wordAddress src
  proofPointer : state.getReg .x4 = wordAddress nonce
  destination : state.getReg .x23 = wordAddress 1536
  tag : state.getReg .x28 = firstTag index.val
  selector : state.getReg .x5 = 0
  size : state.getReg .x11 = 200
  primitive : state.getReg .x13 = 1
  nonceRange : nonce + 2 ≤ 1536
  srcHigh : 131097 ≤ src
  endBound : src + 37 ≤ 2^33

/-- Words 494–496. -/
def evenHeadCode : List Instr := [.LUI .x30 256, .ADDI .x10 .x10 96, .ADDI .x12 .x30 3944]

/-- Move `j` (words 501+2j, 502+2j): value word `j` (j < 17) or salt word `j-17` to word 131078+j. -/
def evenMoveCode (j : Nat) : List Instr :=
  if j < 17 then [.LD .x31 .x10 (BitVec.ofNat 12 (40+8*j)), .SD .x30 .x31 (BitVec.ofNat 12 (48+8*j))]
  else [.LD .x31 .x4 (BitVec.ofNat 12 (8*(j-17))), .SD .x30 .x31 (BitVec.ofNat 12 (48+8*j))]

/-- Words 498–540. -/
def evenMiddleCode : List Instr :=
  [.ADDI .x10 .x10 4000, .ADDI .x31 .x28 4088, .SD .x30 .x31 0] ++
    (List.range 19).flatMap evenMoveCode ++ [.ADDI .x10 .x30 0, .ADDI .x12 .x23 0]

/-- Word 542. -/
def evenJump : Instr := .JAL .x0 2095216

def evenHead (state : MachineState) : MachineState := evenHeadCode.foldl execInstrBr state
def evenMiddle (state : MachineState) : MachineState := evenMiddleCode.foldl execInstrBr state
def evenFirstState (state : MachineState) (first : Block) : MachineState :=
  writeBits (evenHead state) (wordAddress 131053) first
def evenFinal (state : MachineState) (first second : Block) : MachineState :=
  execInstrBr (writeBits (evenMiddle (evenFirstState state first)) (wordAddress 1536) second) evenJump

/-- The two permutation calls of the even path (cf. `leafQueries` for the odd path). -/
def evenQueries (state : MachineState) (src : Nat) (index : Index) : OracleComp World MachineState := do
  let message := window (memoryView state) (src+5)
  let first ← World.query (.inr (.inr (.inl (packBuffer (evenFirstInput message)))))
  let second ← World.query (.inr (.inr (.inl (packBuffer
    (evenSecondInput index (checkerNonce state) (replyWords first) message)))))
  return evenFinal state first second

/-- The decoded image agrees with the code lists above. -/
theorem even_head_decode (i : Nat) (inside : i < 3) :
    (pairImage.code[494+i]?).bind decodeInstruction = some (.base (evenHeadCode[i]?.getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem even_middle_decode (i : Nat) (inside : i < 43) :
    (pairImage.code[498+i]?).bind decodeInstruction = some (.base (evenMiddleCode[i]?.getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem even_calls_decode :
    (pairImage.code[497]?).bind decodeInstruction = some (.base .ECALL) ∧
    (pairImage.code[541]?).bind decodeInstruction = some (.base .ECALL) ∧
    (pairImage.code[542]?).bind decodeInstruction = some (.base evenJump) := ⟨rfl, rfl, rfl⟩

theorem even_middle_length : evenMiddleCode.length = 43 := rfl

/-- What the leaf block needs from the even path. Target: `theorem even_path_facts : EvenPathFacts`. -/
structure EvenPathFacts : Prop where
  run : ∀ {state : MachineState} {src nonce : Nat} {index : Index}, EvenReady state src nonce index →
    ∀ fuel, execute pairImage (49+fuel) state false =
      (do let intermediate ← evenQueries state src index
          let result ← execute pairImage fuel intermediate false
          return result.charge 63 2)
  pc : ∀ {state : MachineState} {src nonce : Nat} {index : Index}, EvenReady state src nonce index →
    ∀ first second : Block, (evenFinal state first second).pc = 0x10e8
  register : ∀ (state : MachineState) (first second : Block) (reg : Reg),
    reg ≠ .x10 → reg ≠ .x12 → reg ≠ .x30 → reg ≠ .x31 →
    (evenFinal state first second).getReg reg = state.getReg reg
  frame : ∀ {state : MachineState} {src nonce : Nat} {index : Index}, EvenReady state src nonce index →
    ∀ (first second : Block) (word : Nat), word < 2^33 →
      (word < 1536 ∨ 1561 ≤ word) → (word < 131053 ∨ 131097 ≤ word) →
      memoryView (evenFinal state first second) word = memoryView state word

end TwoPermutationPrototype.PairCk.Packed.RecordLeaf
