import CommitGolfCandidate.InputMemory
import CommitGolfCandidate.TwoPermutationMemoryBridge
import CommitGolfCandidate.PentaCapSpec

/-! Loader facts for the checker wrapper: the proof buffer and the bytes below it.

`expandProof` turns a level-7 cap proof (1136-byte records, then the 8,704-byte table of every slot
of levels 7 to 10) into the donor's 1424-byte records: record `r` is its salt, the four other slots of each of its level-0..6 groups in rotation order, followed
by, for each level `7 + lvl`, the four other children of the level-`(8 + lvl)` node above the
record's index in rotation order, read from the table. Only the proof buffer differs between the
loader states of a check input and of its expansion, so on aligned words the loader state of the
expansion is exactly `expandedTarget`, which the wrapper builds in place. -/

namespace TwoPermutationPrototype.PentaWrap
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.RV64 (memoryView wordAddress)

/-! ### The loader layout -/

def proofWord : Nat := 1350566924
def PENTA_PROOF_BASE : Nat := 10804535392

/-- The check-side layout facts the wrapper relies on. -/
structure WrapLayout (sub : Submission) : Prop where
  layout : sub.layout = ⟨4096, 4294971392, 4294971424, 6375350304, 6509568096, 10804535392⟩
  data : (sub.image .check).data = []

theorem data_base_value {sub : Submission} (lay : WrapLayout sub) : dataBase (sub.image .check) = 2^36 := by
  unfold dataBase
  rw [lay.data]
  rfl

private theorem card_bound (positions : Positions) : positions.card ≤ 16777216 := by
  have : positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ positions
  exact this

/-- Every byte at or above the proof buffer is the proof byte there (zero past its end). -/
theorem proof_input_byte {sub : Submission} (lay : WrapLayout sub) (input : CheckInput) (address : Nat)
    (above : PENTA_PROOF_BASE ≤ address) :
    inputByte sub .check input address = (input.proof[address - PENTA_PROOF_BASE]?).getD 0 := by
  have card := card_bound input.positions
  have base := data_base_value lay
  have hc : sub.layout.commitment = 4294971392 := by rw [lay.layout]
  have hi : sub.layout.indices = 6375350304 := by rw [lay.layout]
  have hv : sub.layout.values = 6509568096 := by rw [lay.layout]
  have hp : sub.layout.proof = 10804535392 := by rw [lay.layout]
  unfold PENTA_PROOF_BASE at above ⊢
  have e₁ : (DIGEST_BITS + 7) / 8 = 32 := rfl
  have e₂ : LEAF_SIZE / 8 = 256 := rfl
  have no₁ : ¬ (4294971392 ≤ address ∧ address < 4294971392 + 32) := by omega
  have no₂ : ¬ (6375350304 ≤ address ∧ address < 6375350304 + 8 * input.positions.card) := by omega
  have no₃ : ¬ (6509568096 ≤ address ∧ address < 6509568096 + 256 * input.positions.card) := by omega
  unfold inputByte
  simp only [Submission.inputBuffers, hc, hi, hv, hp, fixedBuffer, positionsBuffer, valuesBuffer,
    Finset.length_sort, Finset.card_attach, e₁, e₂,
    List.find?_cons, List.find?_nil, no₁, no₂, no₃, decide_false]
  by_cases inside : address < 10804535392 + input.proof.length
  · have yes : 10804535392 ≤ address ∧ address < 10804535392 + input.proof.length := ⟨above, inside⟩
    simp only [yes, and_self, decide_true]
  · have no₄ : ¬ (10804535392 ≤ address ∧ address < 10804535392 + input.proof.length) := by omega
    have none : input.proof[address - 10804535392]? = none := by
      apply List.getElem?_eq_none; omega
    simp only [no₄, decide_false, none, Option.getD_none, base, lay.data]
    split <;> simp

/-- Below the proof buffer the loader bytes do not depend on the proof. -/
theorem lower_input_byte {sub : Submission} (lay : WrapLayout sub) (input : CheckInput) (proof : Proof)
    (address : Nat) (below : address < PENTA_PROOF_BASE) :
    inputByte sub .check { input with proof := proof } address = inputByte sub .check input address := by
  have hp : sub.layout.proof = 10804535392 := by rw [lay.layout]
  unfold PENTA_PROOF_BASE at below
  have no : ∀ n : Nat, ¬ (10804535392 ≤ address ∧ address < 10804535392 + n) := by intro n; omega
  unfold inputByte
  simp only [Submission.inputBuffers, hp, List.find?_cons, List.find?_nil, no, decide_false]

/-- The packed doubleword of the loader at word `w`. -/
theorem loader_word {sub : Submission} (input : CheckInput) (w : Nat) (small : w < 2^33) :
    memoryView (sub.initialState .check input) w =
      BitVec.ofNat 64 (∑ j ∈ Finset.range 8, (inputByte sub .check input (8*w+j)).toNat * 2^(8*j)) := by
  unfold memoryView wordAddress
  exact initial_input_word sub .check input (8*w) (by omega)

/-- Word `u` of the proof buffer (word `proofWord + u`) as packed proof bytes. -/
theorem proof_word {sub : Submission} (lay : WrapLayout sub) (input : CheckInput) (u : Nat)
    (small : proofWord + u < 2^33) :
    memoryView (sub.initialState .check input) (proofWord+u) =
      BitVec.ofNat 64 (∑ j ∈ Finset.range 8, ((input.proof[8*u+j]?).getD 0).toNat * 2^(8*j)) := by
  rw [loader_word input _ small]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have index : 8*(proofWord+u)+j - PENTA_PROOF_BASE = 8*u+j := by unfold proofWord PENTA_PROOF_BASE; omega
  rw [proof_input_byte lay input _ (by unfold proofWord PENTA_PROOF_BASE; omega), index]

end TwoPermutationPrototype.PentaWrap
