import CommitGolf.Riscv

/-! Layout 2 opener, shared phase interface (Opus ↔ Astra).

Pure, dependency-light definitions of what one phase writer (`phase_p_body` of the V1 opener, words
`bodyWord p ..< tailWord p`) reads and writes, and the guarantee `PhaseFacts` it provides:

- `sourceAddress l22 pos k`, `recordSource s l22 pos k`: the 560 source bytes of position `pos`'s record, read
  from the body-entry state `s` (16 salt bytes, 3 quartet mates of 32 bytes, then 14 sibling digests of 32 bytes,
  levels 0..13; level 0 through the quartet's pointer word `l22`), high digest bits included;
- `writerDwords p src c`, `writerByte`, `writerCarry`: the block the body stores at `s5` and the physical `a1`
  it leaves, computed with exactly the unmasked 64-bit operations of Neon's `generate.py`;
- `PhaseEntry`, `PhaseFacts image p`: from a body entry, `bodyLen p` unit-cost steps (no oracle call) reach the
  tail word with the block written, the carry in `a1`, `t1 = 512 + pos/2^15`, six clobbered registers, and byte
  and raw-word frames outside the block.

Base addresses are numerals: `heapBase = trapdoorBase`, `slotBase = groupSlots`, `saltBase = nonceBase`,
`recordBase0 = proofBase` of the opener modules. -/
namespace CommitGolfCandidate.Layout2Phase
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

/-! ### Geometry -/

def heapBase : Nat := 4294971424
def slotBase : Nat := 4831842336
def saltBase : Nat := 9126809632
def recordBase0 : Nat := 13824430176

/-- Bytes phase `p` stores at `s5` (488 field bytes and 5 or 6 stream dwords). -/
def stride (p : Nat) : Nat := if p=0 then 528 else 536
/-- Offset of phase `p` inside its 2136-byte block of four records. -/
def phaseBase (p : Nat) : Nat := if p=0 then 0 else if p=1 then 528 else if p=2 then 1064 else 1600
/-- Logical stream bits pending in `a1` at the entry of phase `p` (0 at phase 0: `a1` is then ignored). -/
def carryIn (p : Nat) : Nat := if p=0 then 0 else if p=1 then 48 else if p=2 then 32 else 16
/-- Unit-cost instructions of `phase_p_body`. -/
def bodyLen (p : Nat) : Nat := if p=0 then 228 else if p=3 then 231 else 232
/-- First word of `phase_p_body` in the opening image. -/
def bodyWord (p : Nat) : Nat := if p=0 then 4099 else if p=1 then 4342 else if p=2 then 4587 else 4832
/-- First word of `phase_p_tail` (`addi s5,s5,stride`). -/
def tailWord (p : Nat) : Nat := bodyWord p+bodyLen p
def wordAddress (i : Nat) : Word := BitVec.ofNat 64 (4096+4*i)

/-! ### Sources -/

/-- Address of source byte `k < 560` of position `pos`: salt (`k < 16`), the three quartet mates
(`16 ≤ k < 112`, mate `m = (k-16)/32` at reply slot `(32 (pos%4)) xor (32 (m+1))`), the level-0 sibling through
the quartet pointer word (`l22`), and the heap siblings of levels `1..13`. -/
def sourceAddress (l22 pos k : Nat) : Nat :=
  if k<16 then saltBase+16*pos+k
  else if k<112 then slotBase+584+1024*(pos/4)+((32*(pos%4)) ^^^ (32*((k-16)/32+1)))+(k-16)%32
  else if k<144 then l22+(k-112)
  else heapBase+32*(((4194304+pos/4) >>> ((k-112)/32)) ^^^ 1)+(k-112)%32

/-- Source byte `k` of position `pos`'s record, read from state `s`. -/
def recordSource (s : MachineState) (l22 pos k : Nat) : Byte :=
  s.getByte (BitVec.ofNat 64 (sourceAddress l22 pos k))

/-! ### The writer's output -/

/-- Little-endian dword of the sources at byte `k`. -/
def dwordOf (src : Nat → Byte) (k : Nat) : Word :=
  src (k+7) ++ src (k+6) ++ src (k+5) ++ src (k+4) ++ src (k+3) ++ src (k+2) ++ src (k+1) ++ src k

/-- The raw (unmasked) dword holding digest bits 192..255 of the band-A sibling `a < 4` (level `2+a`). -/
def tailA (src : Nat → Byte) (a : Nat) : Word := dwordOf src (176+32*a+24)
/-- The raw dword holding digest bits 192..255 of the band-B sibling `b < 8` (level `6+b`). -/
def tailB (src : Nat → Byte) (b : Nat) : Word := dwordOf src (304+32*b+24)

/-- The three band-A tail dwords at block bytes 272, 280 and 288. -/
def bandATails (src : Nat → Byte) : List Word :=
  [tailA src 0 ||| (tailA src 1 <<< 48),
   (tailA src 1 >>> 16) ||| (tailA src 2 <<< 32),
   (tailA src 2 >>> 32) ||| (tailA src 3 <<< 16)]

/-- One band-B tail into the stream: state `(a1, pending bits, emitted dwords)`, as `generate.py` emits it.
With no pending bits the tail dword replaces `a1`; at exactly 18 pending bits the emitted dword stays in `a1`. -/
def streamStep (st : Word × Nat × List Word) (t : Word) : Word × Nat × List Word :=
  if st.2.1=0 then (t, 46, st.2.2)
  else if st.2.1<18 then (st.1 ||| (t <<< st.2.1), st.2.1+46, st.2.2)
  else if st.2.1=18 then (st.1 ||| (t <<< 18), 0, st.2.2++[st.1 ||| (t <<< 18)])
  else (t >>> (64-st.2.1), st.2.1+46-64, st.2.2++[st.1 ||| (t <<< st.2.1)])

/-- The eight band-B tails of a record through the stream, from `a1 = c` with `carryIn p` pending bits. -/
def streamRun (p : Nat) (src : Nat → Byte) (c : Word) : Word × Nat × List Word :=
  ((List.range 8).map (tailB src)).foldl streamStep (c, carryIn p, [])

/-- The dwords phase `p` stores at `s5`, in address order: salt (2), mates (12), level-0 and level-1 siblings
(4 + 4), band-A first 24 bytes (12), band-A tails (3), band-B first 24 bytes (24), stream (5 or 6). -/
def writerDwords (p : Nat) (src : Nat → Byte) (c : Word) : List Word :=
  [dwordOf src 0, dwordOf src 8] ++
  (List.range 12).map (fun i => dwordOf src (16+8*i)) ++
  (List.range 4).map (fun i => dwordOf src (112+8*i)) ++
  (List.range 4).map (fun i => dwordOf src (144+8*i)) ++
  (List.range 12).map (fun i => dwordOf src (176+32*(i/3)+8*(i%3))) ++
  bandATails src ++
  (List.range 24).map (fun i => dwordOf src (304+32*(i/3)+8*(i%3))) ++
  (streamRun p src c).2.2

/-- Byte `j < stride p` of the block. -/
def writerByte (p : Nat) (src : Nat → Byte) (c : Word) (j : Nat) : Byte :=
  ((writerDwords p src c).getD (j/8) 0).extractLsb' (8*(j%8)) 8

/-- The physical `a1` the body leaves (for phase 3 the last emitted dword). -/
def writerCarry (p : Nat) (src : Nat → Byte) (c : Word) : Word := (streamRun p src c).1

/-! ### The guarantee -/

/-- `cycles` unit-cost steps from `before` to `after` with no oracle call (today's `RunsOpeningBlock`). -/
def RunsBlock (image : Image) (before after : MachineState) (cycles : Nat) : Prop :=
  ∀ fuel allowCoins, execute image (cycles+fuel) before allowCoins =
    (do let result ← execute image fuel after allowCoins
        return result.charge cycles 0)

/-- A body entry of phase `p` for position `pos`, block start `B`, quartet pointer value `l22`, physical carry
`c` (arbitrary: no width condition). -/
structure PhaseEntry (s : MachineState) (p pos B l22 : Nat) (c : Word) : Prop where
  phase : p<4
  pc : s.pc=wordAddress (bodyWord p)
  index : pos<16777216
  posReg : s.getReg .x6=BitVec.ofNat 64 pos
  salt : s.getReg .x7=BitVec.ofNat 64 (saltBase+16*pos)
  dest : s.getReg .x21=BitVec.ofNat 64 B
  aligned : B%8=0
  room : recordBase0 ≤ B ∧ B+stride p ≤ MEMORY_BYTES
  carry : s.getReg .x11=c
  heap : s.getReg .x9=BitVec.ofNat 64 heapBase
  slots : s.getReg .x18=BitVec.ofNat 64 (slotBase+584)
  leaves : s.getReg .x19=BitVec.ofNat 64 4194304
  pointer : s.getMem (BitVec.ofNat 64 (slotBase+1024*(pos/4)+712))=BitVec.ofNat 64 l22
  quad : l22%8=0 ∧ heapBase ≤ l22 ∧ l22+32 ≤ saltBase

/-- What the phase-`p` writer guarantees. -/
def PhaseFacts (image : Image) (p : Nat) : Prop :=
  ∀ (s : MachineState) (pos B l22 : Nat) (c : Word), PhaseEntry s p pos B l22 c →
    ∃ t, RunsBlock image s t (bodyLen p) ∧
      t.pc=wordAddress (tailWord p) ∧
      (∀ j<stride p, t.getByte (BitVec.ofNat 64 (B+j))=writerByte p (recordSource s l22 pos) c j) ∧
      t.getReg .x11=writerCarry p (recordSource s l22 pos) c ∧
      t.getReg .x6=BitVec.ofNat 64 (512+pos/32768) ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x10 → r ≠ .x11 → r ≠ .x28 → r ≠ .x31 → t.getReg r=s.getReg r) ∧
      (∀ a<2^64, a<B ∨ B+stride p ≤ a → t.getByte (BitVec.ofNat 64 a)=s.getByte (BitVec.ofNat 64 a)) ∧
      (∀ q : Word, q.toNat<B ∨ B+stride p ≤ q.toNat → t.getMem q=s.getMem q)

/-! ### Sanity checks -/

theorem writer_dwords_length (p : Nat) (src : Nat → Byte) (c : Word) (hp : p<4) :
    (writerDwords p src c).length*8=stride p := by
  have h : ∀ p<4, ∀ (c : Word) (src : Nat → Byte), ((streamRun p src c).2.2).length=(if p=0 then 5 else 6) := by
    intro p hp c src
    interval_cases p <;> simp [streamRun, streamStep, carryIn, List.range_succ]
  simp only [writerDwords, List.length_append, List.length_map, List.length_range, List.length_cons,
    List.length_nil, bandATails, h p hp c src]
  unfold stride
  split <;> omega

theorem tail_words : tailWord 0=4327 ∧ tailWord 1=4574 ∧ tailWord 2=4819 ∧ tailWord 3=5063 := by decide

end CommitGolfCandidate.Layout2Phase
