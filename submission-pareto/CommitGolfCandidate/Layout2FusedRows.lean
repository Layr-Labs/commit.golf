import CommitGolfCandidate.K3OpenChain
import CommitGolfCandidate.GroupOpenStep
import CommitGolfCandidate.GroupOpenVirtual
import CommitGolfCandidate.Machine
import CommitGolfCandidate.K3OpenReply
import CommitGolfCandidate.Layout2Phase
import CommitGolfCandidate.Layout2Writer3Run
import CommitGolfCandidate.Layout2Records
import CommitGolfCandidate.Layout2Seen

/-! Fused opener (Layout 2 V2 Increment 4b): the rows of one position (phase `ph`, words `4097 + 272 ph ..`) and their
presence in the image; block geometry. The position proofs are `Layout2FusedHead` (head, inverse call, chain),
`Layout2FusedRec` (salt, writer, tail) and `Layout2FusedStep` (one position). Code of phase `ph`:
```
ld x6,0(x8) ; srli x28,x6,2 ; slli x3,x6,4 ; and x30,x3,x1 ; add x30,x30,x2        -- index, quartet, entry
slli x7,x28,10 ; add x7,x7,x24 ; addi x12,x21,0 ; lh x10,4(x30) ; add x10,x10,x7   -- reply address, output B
lh x18,6(x30) ; add x18,x18,x7 ; addi x13,x0,2 ; ecall                              -- L22 node in s2; inverse
addi x13,x0,1 ; addi x12,x0,1536 ; addi x10,x0,1024                                 -- generator input
[chain rows 4114+272ph .. 4155+272ph, K3OpenChain with phase ph]
ld x31,0(x28) ; sd x31,0(x21) ; ld x31,8(x28) ; sd x31,8(x21)                         -- salt to B+0..15
[the phase writer at 4160+272ph, Layout2Writer3; the tail with the byte mark and the latch, Layout2Steps]
```
The inverse reply (200 bytes) lands at `B = destOf j` (in `s5`); the writer then overwrites the written dwords. -/
namespace TwoPermutationPrototype.GroupedOpening.Layout2F
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open TwoPermutationPrototype.GroupedOpening TwoPermutationPrototype.GroupedOpening.Layout2
open CommitGolfCandidate.Layout2Phase (stride)
open CommitGolfCandidate.Permutation.CounterSalt (coord)
open TwoPermutationPrototype.Sampling (saltWords)
open TwoPermutationPrototype.GroupedOpening.Layout2V2 (linkedSalts)
set_option maxRecDepth 18000
set_option maxHeartbeats 1800000

attribute [local simp] Opening.getReg_setReg Opening.getReg_setMem MachineState.getReg_setPC
attribute [local simp] pc_of_set mem_of_set mem_of_reg open_zero
attribute [local simp] MachineState.getMem_setPC MachineState.getMem_setReg

theorem view_of_mem {a b : MachineState} (h : a.mem=b.mem) (w : Nat) : memoryView a w=memoryView b w := by
  unfold memoryView MachineState.getMem; rw [h]

/-! ### Rows -/

def headRows (ph : Nat) : List Row :=
  [(4097+272*ph,.LD .x6 .x8 0),(4098+272*ph,.SRLI .x28 .x6 2),(4099+272*ph,.SLLI .x3 .x6 4),
   (4100+272*ph,.AND .x30 .x3 .x1),(4101+272*ph,.ADD .x30 .x30 .x2),(4102+272*ph,.SLLI .x7 .x28 10),
   (4103+272*ph,.ADD .x7 .x7 .x24),(4104+272*ph,.ADDI .x12 .x21 0),(4105+272*ph,.LH .x10 .x30 4),
   (4106+272*ph,.ADD .x10 .x10 .x7),(4107+272*ph,.LH .x18 .x30 6),(4108+272*ph,.ADD .x18 .x18 .x7),
   (4109+272*ph,.ADDI .x13 .x0 2)]
def postRows (ph : Nat) : List Row :=
  [(4111+272*ph,.ADDI .x13 .x0 1),(4112+272*ph,.ADDI .x12 .x0 1536),(4113+272*ph,.ADDI .x10 .x0 1024)]
def saltRows (ph : Nat) : List Row :=
  [(4156+272*ph,.LD .x31 .x28 0),(4157+272*ph,.SD .x21 .x31 0),(4158+272*ph,.LD .x31 .x28 8),
   (4159+272*ph,.SD .x21 .x31 8)]
/-- The phase writer's rows (`Layout2Writer3.listing3`) at `fwriterWord ph = 4160 + 272 ph`. -/
def writerRowsF (ph : Nat) : List Row := Layout2Writer3.writerRows (fwriterWord ph) ph
/-- The deterministic rest of a position after the chain: salt rows, writer, tail with the latch. -/
def recRows (ph : Nat) (last : Bool) : List Row := saltRows ph ++ writerRowsF ph ++ ftailRows ph last
/-- Its length and price. -/
def recLen (ph : Nat) (last : Bool) : Nat := 4+(Layout2Writer3.writerLen ph+tailCost ph last)

theorem head_fetch (ph : Nat) (hp : ph<4) : presentRows (headRows ph) := by
  interval_cases ph <;> (apply rows_present; decide +kernel)
theorem post_fetch (ph : Nat) (hp : ph<4) : presentRows (postRows ph) := by
  interval_cases ph <;> (apply rows_present; decide +kernel)
theorem salt_fetch (ph : Nat) (hp : ph<4) : presentRows (saltRows ph) := by
  interval_cases ph <;> (apply rows_present; decide +kernel)
/-- Rows `rowsFrom w ops` are present when the image words `w ..< w + |ops|` decode to `ops` (one list check). -/
theorem rows_from_present (w : Nat) (ops : List Instr) (hw : w+ops.length ≤ 6144)
    (img : ((openingImage.code.drop w).take ops.length).map Opening.decodeBase=ops.map some) :
    presentRows (Layout2Writer3.rowsFrom w ops) := by
  induction ops generalizing w with
  | nil => intro q hq; simp [Layout2Writer3.rowsFrom] at hq
  | cons op ops ih =>
    intro q hq
    have e0 : (openingImage.code[w]?).bind Opening.decodeBase=some op ∧
        ((openingImage.code.drop (w+1)).take ops.length).map Opening.decodeBase=ops.map some := by
      have hl : w<openingImage.code.length := by
        by_contra h
        rw [List.drop_eq_nil_of_le (by omega)] at img; simp at img
      rw [List.drop_eq_getElem_cons hl] at img
      simp only [List.length_cons, List.take_succ_cons, List.map_cons, List.cons.injEq] at img
      refine ⟨?_, ?_⟩
      · rw [List.getElem?_eq_getElem hl]; simpa using img.1
      · rw [← List.drop_drop]; simpa [List.drop_one] using img.2
    simp only [Layout2Writer3.rowsFrom, List.mem_cons] at hq
    rcases hq with rfl|hq
    · exact fun st pc => packed_fetch_far st _ _ (by simp at hw; omega) pc e0.1
    · exact ih (w+1) (by simp at hw; omega) e0.2 q hq

private theorem writer_image : ∀ ph : Fin 4,
    ((openingImage.code.drop (fwriterWord ph.val)).take (Layout2Writer3.listing3 ph.val 0).length).map
      Opening.decodeBase=(Layout2Writer3.listing3 ph.val 0).map some := by decide +kernel

theorem writer_fetch (ph : Nat) (hp : ph<4) : presentRows (writerRowsF ph) := by
  have h := writer_image ⟨ph,hp⟩
  have len := Layout2Writer3.listing3_length ⟨ph,hp⟩
  apply rows_from_present _ _ _ h
  rw [len]; unfold fwriterWord Layout2Writer3.writerLen Layout2Phase2.bodyLen; split_ifs <;> omega

private theorem inverse_words : ∀ ph : Fin 4,
    (openingImage.code[4110+272*ph.val]?).bind Opening.decodeBase=some .ECALL := by decide +kernel

theorem inverse_fetch (s : MachineState) (ph : Nat) (hp : ph<4) (pc : s.pc=address (4110+272*ph)) :
    fetch openingImage s=some (.base .ECALL) :=
  packed_fetch_far _ (4110+272*ph) _ (by omega) pc (inverse_words ⟨ph,hp⟩)

theorem writer_price : ∀ ph : Fin 4, price (writerRowsF ph.val)=Layout2Writer3.writerLen ph.val ∧
    (writerRowsF ph.val).length=Layout2Writer3.writerLen ph.val := by decide +kernel

theorem rec_fetch (ph : Nat) (hp : ph<4) (last : Bool) : presentRows (recRows ph last) := by
  intro q hq
  simp only [recRows, List.mem_append] at hq
  rcases hq with (h|h)|h
  · exact salt_fetch ph hp q h
  · exact writer_fetch ph hp q h
  · exact tail_present ph hp last q h

theorem rec_cost (ph : Nat) (hp : ph<4) (last : Bool) :
    (recRows ph last).length=recLen ph last ∧ price (recRows ph last)=recLen ph last := by
  have w : price (writerRowsF ph)=Layout2Writer3.writerLen ph ∧ (writerRowsF ph).length=Layout2Writer3.writerLen ph :=
    writer_price ⟨ph,hp⟩
  have t := tail_cost ph hp last
  have sp : price (saltRows ph)=4 := rfl
  have sl : (saltRows ph).length=4 := rfl
  unfold recRows recLen
  rw [List.length_append, List.length_append, price_append, price_append, w.1, w.2, t.1, t.2, sp, sl]
  exact ⟨by omega, by omega⟩

theorem row_lengths (ph : Nat) : (headRows ph).length=13 ∧ price (headRows ph)=13 ∧ (postRows ph).length=3 ∧
    price (postRows ph)=3 :=
  ⟨rfl,rfl,rfl,rfl⟩

/-! ### Geometry of the blocks -/

/-- Word index of record `j`'s block. -/
def blockW (j : Nat) : Nat := destOf j/8

theorem block_mul (j : Nat) : 8*blockW j=destOf j := by
  have := dest_aligned j; unfold blockW; omega

theorem block_address (j : Nat) : wordAddress (blockW j)=BitVec.ofNat 64 (destOf j) := by
  unfold wordAddress; rw [block_mul]

theorem block_room (j : Nat) (hj : j ≤ 16777216) : proofBase/8 ≤ blockW j ∧ blockW j+67 ≤ 2^32 := by
  have b := dest_bound j
  have m := block_mul j
  have pb : proofBase=13824430176 := rfl
  unfold stride at b
  constructor <;> (split_ifs at b <;> omega)

end TwoPermutationPrototype.GroupedOpening.Layout2F
