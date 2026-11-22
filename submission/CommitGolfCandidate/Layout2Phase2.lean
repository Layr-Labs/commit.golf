import CommitGolfCandidate.Layout2Phase

/-! Layout 2 V2a (Inc 2 direct salts + Inc 3 direct inverse-quartet output): shared phase interface
(Opus ↔ Astra), the V2 counterpart of `Layout2Phase`.

Image: `cg-team/astra/layout2/v2/programs.json` (SHA-256 `b0be540d…7f07`). Per phase `p` the record pass is

    hdr_p  (1 word)          ld t1,0(s0)                                        -- Opus (loop)
    body_p (bodyLen p words) words bodyWord p ..< tailWord p, straight line       -- Astra (writer)
    tail_p (7 words)         as V1: addi s5,s5,stride; srli; slli; add; sd s7; addi s0,s0,8; bne s0,a7
    exit_p                   as V1: flush 6/4/2/0 carry bytes, jal <1097>          -- Opus (loop)

At body entry the block `[B, B+stride p)` already holds what pass 1 put there (Opus proves this):

- bytes `0..15`: the salt; the body keeps them;
- bytes `16..23` (`pointerOffset`): the saved L22 pointer `l22`; the body loads it first, then L21 overwrites
  bytes `16..47`;
- bytes `72..199`: the four leaf-digest slots `slotOffset s = 72+32s` of the inverse quartet reply; the slot of the
  selector `q = pos % 4` is overwritten with the L22 sibling, the three mate slots `s ≠ q` are kept.

The body stores exactly the physical dwords `written q d`: `2..8` (L21, band-A0 head), the slot-`q` dwords
`9+4q ..< 13+4q` (L22), and `25 ..` (A1..A3 heads, band-A tails, band-B heads, stream). The written dword `d`
holds V1's `writerDwords` entry `v1Dword d`; from `d = 25` on that is V1's dword at the same index, so band A
tails, band B and the stream are V1's. Only V1 entries `≥ 14` are used, i.e. only the sources `k ≥ 112` (L22 through
`l22`, heap siblings of levels 1..13); the salt and mate entries of `recordSource` (V1 addresses) play no role. -/
namespace CommitGolfCandidate.Layout2Phase2
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CommitGolfCandidate.Layout2Phase

/-! ### Geometry of the V2a record pass -/

/-- Unit-cost instructions of the V2a `body_p`. -/
def bodyLen (p : Nat) : Nat := if p=0 then 193 else if p=3 then 196 else 197
/-- First word of the V2a `body_p`: the word after the header `ld t1,0(s0)` at `bodyWord p - 1`. -/
def bodyWord (p : Nat) : Nat := if p=0 then 4097 else if p=1 then 4303 else if p=2 then 4511 else 4719
/-- First word of `tail_p` (`addi s5,s5,stride p`). -/
def tailWord (p : Nat) : Nat := bodyWord p+bodyLen p

/-- Byte offset of the saved L22 pointer in the block. -/
def pointerOffset : Nat := 16
/-- Byte offset of reply slot `s < 4` (leaf digest `d_s` of the quartet). -/
def slotOffset (s : Nat) : Nat := 72+32*s

/-- Physical dword `d` of the block is stored by the body of a record with selector `q = pos % 4`. -/
def written (q d : Nat) : Bool := (2 ≤ d && d<9) || (9+4*q ≤ d && d<13+4*q) || 25 ≤ d

/-- The index into V1's `writerDwords` that a written physical dword `d` holds: L21 and the A0 head move from
V1 dwords `18..24` to `2..8`, slot `q` holds L22 (V1 dwords `14..17`), everything from dword `25` stays. -/
def v1Dword (d : Nat) : Nat := if d<9 then d+16 else if d<25 then 14+(d-9)%4 else d

/-- Byte `j` of a written dword of the block. -/
def writtenByte (p : Nat) (src : Nat → Byte) (c : Word) (j : Nat) : Byte :=
  ((writerDwords p src c).getD (v1Dword (j/8)) 0).extractLsb' (8*(j%8)) 8

/-- Block bytes the body keeps from its entry state: the salt and the three mate slots. -/
def retained (q j : Nat) : Prop := j<16 ∨ (72 ≤ j ∧ j<200 ∧ (j-72)/32 ≠ q)

/-! ### The guarantee -/

/-- A V2a body entry of phase `p` for position `pos`, block start `B`, saved pointer value `l22`, physical carry
`c` (arbitrary). Compared with V1: no salt-address (`x7`) or slot-base (`x18`) premise; the pointer is the raw
dword at `B+16` instead of the trapdoor pointer word. -/
structure PhaseEntry (s : MachineState) (p pos B l22 : Nat) (c : Word) : Prop where
  phase : p<4
  pc : s.pc=wordAddress (bodyWord p)
  index : pos<16777216
  posReg : s.getReg .x6=BitVec.ofNat 64 pos
  dest : s.getReg .x21=BitVec.ofNat 64 B
  aligned : B%8=0
  room : recordBase0 ≤ B ∧ B+stride p ≤ MEMORY_BYTES
  carry : s.getReg .x11=c
  heap : s.getReg .x9=BitVec.ofNat 64 heapBase
  leaves : s.getReg .x19=BitVec.ofNat 64 4194304
  pointer : s.getMem (BitVec.ofNat 64 (B+pointerOffset))=BitVec.ofNat 64 l22
  quad : l22%8=0 ∧ heapBase ≤ l22 ∧ l22+32 ≤ saltBase

/-- What the V2a phase-`p` writer guarantees: `bodyLen p` unit-cost steps (no oracle call) to `tailWord p`; the
written dwords as above; the retained bytes, every byte outside the block and every raw word outside the block
unchanged; carry, `x6` and the clobbered registers as in V1. -/
def PhaseFacts (image : Image) (p : Nat) : Prop :=
  ∀ (s : MachineState) (pos B l22 : Nat) (c : Word), PhaseEntry s p pos B l22 c →
    ∃ t, RunsBlock image s t (bodyLen p) ∧
      t.pc=wordAddress (tailWord p) ∧
      (∀ j<stride p, written (pos%4) (j/8) →
        t.getByte (BitVec.ofNat 64 (B+j))=writtenByte p (recordSource s l22 pos) c j) ∧
      t.getReg .x11=writerCarry p (recordSource s l22 pos) c ∧
      t.getReg .x6=BitVec.ofNat 64 (512+pos/32768) ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x10 → r ≠ .x11 → r ≠ .x28 → r ≠ .x31 → t.getReg r=s.getReg r) ∧
      (∀ a<2^64, ¬(B ≤ a ∧ a<B+stride p ∧ written (pos%4) ((a-B)/8)) →
        t.getByte (BitVec.ofNat 64 a)=s.getByte (BitVec.ofNat 64 a)) ∧
      (∀ w : Word, w.toNat<B ∨ B+stride p ≤ w.toNat → t.getMem w=s.getMem w)

/-! ### Sanity checks -/

theorem tail_words : tailWord 0=4290 ∧ tailWord 1=4500 ∧ tailWord 2=4708 ∧ tailWord 3=4915 := by decide

/-- Every V2a body is V1's body less 35 instructions (salt copy 4, mate copies and their address set-up 31). -/
theorem body_saving : ∀ p<4, bodyLen p+35=Layout2Phase.bodyLen p := by decide

/-- Inside the block, a byte is retained exactly when its dword is not written. -/
theorem retained_iff (p q j : Nat) (hq : q<4) (hj : j<stride p) :
    retained q j ↔ written q (j/8)=false := by
  have hs : stride p ≤ 536 := by unfold stride; split <;> omega
  unfold retained written
  simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not, Nat.not_le, Nat.not_lt]
  interval_cases q <;> omega

/-- Written dwords hold V1 entries from 14 on, so only the sources `k ≥ 112` matter. -/
theorem v1Dword_ge (d : Nat) : 14 ≤ v1Dword d ∧ (25 ≤ d → v1Dword d=d) := by
  unfold v1Dword; constructor <;> (try intro) <;> split_ifs <;> omega

/-- The written dwords of a phase-`p` block: 7 + 4 + `stride p/8 - 25`; so 48 or 49 dwords, plus 2 salt and
12 mate dwords retained. -/
theorem written_count : ∀ p<4, ∀ q<4,
    ((List.range (stride p/8)).filter (fun d => written q d)).length=stride p/8-14 := by decide

/-! ### Only the sources `k ≥ 112` matter (the V1 salt and mate addresses of `recordSource` are unused) -/
theorem dword_congr {src src' : Nat → Byte} (k : Nat) (h : ∀ i, k ≤ i → src i=src' i) :
    dwordOf src k=dwordOf src' k := by
  simp only [dwordOf, h k (by omega), h (k+1) (by omega), h (k+2) (by omega), h (k+3) (by omega),
    h (k+4) (by omega), h (k+5) (by omega), h (k+6) (by omega), h (k+7) (by omega)]

/-- V1's block from dword 14 on (L22, L21, band A, band B, stream). -/
def writerHigh (p : Nat) (src : Nat → Byte) (c : Word) : List Word :=
  (List.range 4).map (fun i => dwordOf src (112+8*i)) ++
  (List.range 4).map (fun i => dwordOf src (144+8*i)) ++
  (List.range 12).map (fun i => dwordOf src (176+32*(i/3)+8*(i%3))) ++
  bandATails src ++
  (List.range 24).map (fun i => dwordOf src (304+32*(i/3)+8*(i%3))) ++
  (streamRun p src c).2.2

theorem writer_split (p : Nat) (src : Nat → Byte) (c : Word) :
    writerDwords p src c=([dwordOf src 0, dwordOf src 8] ++ (List.range 12).map (fun i => dwordOf src (16+8*i))) ++
      writerHigh p src c := by
  simp only [writerDwords, writerHigh, List.append_assoc]

theorem stream_congr (p : Nat) {src src' : Nat → Byte} (c : Word) (h : ∀ i, 304 ≤ i → src i=src' i) :
    streamRun p src c=streamRun p src' c := by
  unfold streamRun
  congr 1
  apply List.map_congr_left
  intro b hb
  simp only [List.mem_range] at hb
  exact dword_congr _ (fun i hi => h i (by omega))

theorem high_congr (p : Nat) {src src' : Nat → Byte} (c : Word) (h : ∀ i, 112 ≤ i → src i=src' i) :
    writerHigh p src c=writerHigh p src' c := by
  have d : ∀ k, 112 ≤ k → dwordOf src k=dwordOf src' k := fun k hk => dword_congr k (fun i hi => h i (by omega))
  unfold writerHigh bandATails tailA
  rw [stream_congr p c (fun i hi => h i (by omega))]
  congr 1
  · congr 1
    · congr 1
      · congr 1
        · congr 1
          · apply List.map_congr_left; intro i hi; simp only [List.mem_range] at hi; exact d _ (by omega)
          · apply List.map_congr_left; intro i hi; simp only [List.mem_range] at hi; exact d _ (by omega)
        · apply List.map_congr_left; intro i hi; simp only [List.mem_range] at hi; exact d _ (by omega)
      · simp only [d 200 (by omega), d 232 (by omega), d 264 (by omega), d 296 (by omega)]
    · apply List.map_congr_left; intro i hi; simp only [List.mem_range] at hi; exact d _ (by omega)

/-- Only the sources `k ≥ 112` reach the written dwords. -/
theorem written_byte_congr (p : Nat) {src src' : Nat → Byte} (c : Word) (j : Nat)
    (h : ∀ i, 112 ≤ i → src i=src' i) : writtenByte p src c j=writtenByte p src' c j := by
  have ge := (v1Dword_ge (j/8)).1
  unfold writtenByte
  rw [writer_split, writer_split]
  have len : ∀ s : Nat → Byte, ([dwordOf s 0, dwordOf s 8] ++ (List.range 12).map (fun i => dwordOf s (16+8*i))).length=14 := by
    intro s; simp
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [len]; omega),
    List.getElem?_append_right (by rw [len]; omega), len, len, high_congr p c h]

/-- Only the band-B sources `k ≥ 304` reach the carry. -/
theorem writer_carry_congr (p : Nat) {src src' : Nat → Byte} (c : Word)
    (h : ∀ i, 304 ≤ i → src i=src' i) : writerCarry p src c=writerCarry p src' c := by
  unfold writerCarry; rw [stream_congr p c h]

end CommitGolfCandidate.Layout2Phase2
