import CommitGolfCandidate.K3OpenChain
import CommitGolfCandidate.GroupOpenStep

/-! Layout 2 V2a opener, first pass (Inc 2 direct salts + Inc 3 direct inverse-quartet output): the rows of one
position in pass phase `ph < 4` (words `3079 + 80 ph ..`), checked against the image.

Per position `i` at ordinal `j` (`ph = j % 4`, block `B = destOf j` in `x29`):
```
ld x6,0(x14) ; srli x28,x6,2 ; slli x3,x6,4 ; and x30,x3,x1 ; add x30,x30,x2      -- index, quartet, entry
slli x7,x28,10 ; add x7,x7,x24 ; addi x12,x29,0 ; lh x10,4(x30) ; add x10,x10,x7  -- reply address, output B
lh x31,6(x30) ; add x31,x31,x7 ; addi x13,x0,2 ; ecall                             -- sibling node; inverse
addi x13,x0,1 ; addi x12,x0,1536 ; sd x31,16(x29) ; addi x10,x0,1024              -- pointer to B+16
[chain rows 3097+80ph .. 3138+80ph, K3OpenChain with phase ph]
ld x31,0(x28) ; sd x31,0(x29) ; ld x31,8(x28) ; sd x31,8(x29)                       -- salt to B+0..15
addi x29,x29,528|536 ; addi x14,x14,8 ; bne x14,x17,<next phase> ; [addi x25,x9,0 ; jal <4096>]
```
The inverse reply (200 bytes) lands at `B`; there is no reply cache (every position inverts). -/
namespace TwoPermutationPrototype.GroupedOpening.Layout2V2
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000

/-- Bytes the pass advances `x29` by after a phase-`ph` position. -/
def passStride (ph : Nat) : Nat := if ph=0 then 528 else 536
/-- The latch offset (bytes, 13-bit): to the next phase, or back from phase 3 to phase 0. -/
def latchImm (ph : Nat) : BitVec 13 := if ph=3 then 6968 else 56
/-- The exit jump of phase `ph` (word `3147 + 80 ph`) to the record pass at word 4096. -/
def exitImm (ph : Nat) : BitVec 21 := BitVec.ofNat 21 (3796-320*ph)

def headRows (ph : Nat) : List Row :=
  [(3079+80*ph,.LD .x6 .x14 0),(3080+80*ph,.SRLI .x28 .x6 2),(3081+80*ph,.SLLI .x3 .x6 4),
   (3082+80*ph,.AND .x30 .x3 .x1),(3083+80*ph,.ADD .x30 .x30 .x2),(3084+80*ph,.SLLI .x7 .x28 10),
   (3085+80*ph,.ADD .x7 .x7 .x24),(3086+80*ph,.ADDI .x12 .x29 0),(3087+80*ph,.LH .x10 .x30 4),
   (3088+80*ph,.ADD .x10 .x10 .x7),(3089+80*ph,.LH .x31 .x30 6),(3090+80*ph,.ADD .x31 .x31 .x7),
   (3091+80*ph,.ADDI .x13 .x0 2)]
def postRows (ph : Nat) : List Row :=
  [(3093+80*ph,.ADDI .x13 .x0 1),(3094+80*ph,.ADDI .x12 .x0 1536),(3095+80*ph,.SD .x29 .x31 16),
   (3096+80*ph,.ADDI .x10 .x0 1024)]
def saltRows (ph : Nat) : List Row :=
  [(3139+80*ph,.LD .x31 .x28 0),(3140+80*ph,.SD .x29 .x31 0),(3141+80*ph,.LD .x31 .x28 8),
   (3142+80*ph,.SD .x29 .x31 8),(3143+80*ph,.ADDI .x29 .x29 (BitVec.ofNat 12 (passStride ph)))]
def latchRows (ph : Nat) (last : Bool) : List Row :=
  [(3144+80*ph,.ADDI .x14 .x14 8),(3145+80*ph,.BNE .x14 .x17 (latchImm ph))] ++
  (if last then [(3146+80*ph,.ADDI .x25 .x9 0),(3147+80*ph,.JAL .x0 (exitImm ph))] else [])
/-- Word 3078: `addi x29,x21,0` (the pass's block cursor starts at the proof buffer). -/
def cursorRows : List Row := [(3078,.ADDI .x29 .x21 0)]

theorem head_fetch (ph : Nat) (hp : ph<4) : presentRows (headRows ph) := by
  interval_cases ph <;> (apply rows_present; decide +kernel)
theorem post_fetch (ph : Nat) (hp : ph<4) : presentRows (postRows ph) := by
  interval_cases ph <;> (apply rows_present; decide +kernel)
theorem salt_fetch (ph : Nat) (hp : ph<4) : presentRows (saltRows ph) := by
  interval_cases ph <;> (apply rows_present; decide +kernel)
theorem latch_fetch (ph : Nat) (hp : ph<4) (last : Bool) : presentRows (latchRows ph last) := by
  interval_cases ph <;> cases last <;> (apply rows_present; decide +kernel)
theorem cursor_fetch : presentRows cursorRows := by apply rows_present; decide +kernel

private theorem inverse_words : ∀ ph : Fin 4,
    (openingImage.code[3092+80*ph.val]?).bind Opening.decodeBase=some .ECALL := by decide +kernel

theorem inverse_fetch (s : MachineState) (ph : Nat) (hp : ph<4) (pc : s.pc=address (3092+80*ph)) :
    fetch openingImage s=some (.base .ECALL) :=
  packed_fetch_far _ (3092+80*ph) _ (by omega) pc (inverse_words ⟨ph,hp⟩)

theorem row_lengths (ph : Nat) : (headRows ph).length=13 ∧ price (headRows ph)=13 ∧ (postRows ph).length=4 ∧
    price (postRows ph)=4 ∧ (saltRows ph).length=5 ∧ price (saltRows ph)=5 :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem latch_lengths (ph : Nat) (last : Bool) :
    (latchRows ph last).length=2+2*(if last then 1 else 0) ∧ price (latchRows ph last)=2+2*(if last then 1 else 0) := by
  cases last <;> exact ⟨rfl,rfl⟩

/-- The latch targets: the next phase's first word, and the exit to the record pass. -/
theorem latch_target (ph : Nat) (hp : ph<4) :
    address (3145+80*ph)+signExtend13 (latchImm ph)=address (3079+80*((ph+1)%4)) := by
  interval_cases ph <;> decide

theorem exit_target (ph : Nat) (hp : ph<4) : address (3147+80*ph)+signExtend21 (exitImm ph)=address 4096 := by
  interval_cases ph <;> decide

end TwoPermutationPrototype.GroupedOpening.Layout2V2
