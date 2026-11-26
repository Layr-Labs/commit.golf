import CommitGolfCandidate.InputMemory
import CommitGolfCandidate.TwoPermutationMemoryBridge
import CommitGolfCandidate.PentaCapSpec

/-! The checker wrapper's proof expansion, at the byte level and on the loader's memory.

`expandProof` turns a level-7 cap proof (1136-byte records, then the 8,704-byte table of every slot
of levels 7 to 10) into the donor's 1424-byte records: record `r` is its salt, the four other slots of each of its level-0..6 groups in rotation order, followed
by, for each level `7 + lvl`, the four other children of the level-`(8 + lvl)` node above the
record's index in rotation order, read from the table. Only the proof buffer differs between the
loader states of a check input and of its expansion, so on aligned words the loader state of the
expansion is exactly `expandedTarget`, which the wrapper builds in place. -/

namespace TwoPermutationPrototype.PentaWrap
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.RV64 (memoryView wordAddress)

/-- First table group of level `7 + lvl`. -/
def capFirst (lvl : Nat) : Nat := match lvl with | 0 => 0 | 1 => 43 | 2 => 52 | _ => 54

/-- The level-`(7 + lvl)` quotient of an index: its node is `capQuot i lvl`, its group
`capQuot i lvl / 5`, its slot `capQuot i lvl % 5`. -/
def capQuot (i lvl : Nat) : Nat := i / 5^(7+lvl)

/-- Digit `k` (base 5) of an index: its slot within its level-`k` group. -/
def capDigit (i k : Nat) : Nat := i / 5^k % 5

/-- Byte `b` of the expansion of `proof` for `positions`. Record `r` of the proof holds the salt and,
for each level `k ≤ 6`, the five slots of the record's level-`k` group; the expansion keeps the
salt and the four other slots in rotation order. -/
def expandByte (positions : Positions) (proof : Proof) (b : Nat) : Byte :=
  let r := b / 1424
  let e := b % 1424
  if e < 16 then (proof[1136*r + e]?).getD 0
  else if e < 912 then
    let k := (e - 16) / 128
    let d := capDigit (sortedIndex positions r) k
    (proof[1136*r + 16 + 160*k + 32*((d + ((e - 16) % 128)/32 + 1) % 5) + (e - 16) % 32]?).getD 0
  else
    let lvl := (e - 912) / 128
    let q := capQuot (sortedIndex positions r) lvl
    (proof[1136*positions.card + 160*(capFirst lvl + q/5) +
      32*((q%5 + ((e - 912) % 128)/32 + 1) % 5) + (e - 912) % 32]?).getD 0

def expandProof (positions : Positions) (proof : Proof) : Proof :=
  (List.range (1424*positions.card)).map (expandByte positions proof)

theorem expand_proof_length (positions : Positions) (proof : Proof) :
    (expandProof positions proof).length = 1424*positions.card := by
  simp [expandProof]

/-- The check input the donor checker sees after the wrapper. -/
def expandInput (input : CheckInput) : CheckInput :=
  { input with proof := expandProof input.positions input.proof }

/-- Exact length accepted by the wrapper. -/
def capLength (positions : Positions) : Nat :=
  1136*positions.card + (if positions.card = 0 then 0 else 8704)

/-- Exact length of a level-7-table proof (the submitted format): records, then 43 table groups. -/
def capLength7 (positions : Positions) : Nat :=
  1136*positions.card + (if positions.card = 0 then 0 else 6880)

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

/-! ### The target of the expansion -/

/-- Our loader's word `proofWord + u`. -/
abbrev sourceWord (sub : Submission) (input : CheckInput) (u : Nat) : Word :=
  memoryView (sub.initialState .check input) (proofWord+u)

/-- Word `v < 178k` of the expanded proof, in terms of the cap proof's words. -/
def expandedWord (sub : Submission) (input : CheckInput) (v : Nat) : Word :=
  if v % 178 < 2 then sourceWord sub input (142*(v/178) + v % 178)
  else if v % 178 < 114 then
    let k := (v % 178 - 2) / 16
    let d := capDigit (sortedIndex input.positions (v/178)) k
    sourceWord sub input (142*(v/178) + 2 + 20*k + 4*((d + (v % 178 - 2) % 16 / 4 + 1) % 5) + (v % 178 - 2) % 4)
  else
    let lvl := (v % 178 - 114) / 16
    let q := capQuot (sortedIndex input.positions (v/178)) lvl
    sourceWord sub input (142*input.positions.card + 20*(capFirst lvl + q/5) +
      (4*(q%5+1) + (v % 178 - 114) % 16) % 20)

/-- What the wrapper leaves on aligned words outside its scratch table: the loader's words below the
proof buffer, the expanded proof over the record area, and zeros after it (the wrapper clears the
rest of the cap proof). -/
def expandedTarget (sub : Submission) (input : CheckInput) (w : Nat) : Word :=
  if w < proofWord then memoryView (sub.initialState .check input) w
  else if w < proofWord + 178*input.positions.card then expandedWord sub input (w - proofWord)
  else 0

private theorem zero_word : BitVec.ofNat 64 (∑ j ∈ Finset.range 8, (0 : Byte).toNat * 2^(8*j)) = 0 := by
  simp

private theorem pack_congr (f g : Nat → Byte) (same : ∀ j < 8, f j = g j) :
    BitVec.ofNat 64 (∑ j ∈ Finset.range 8, (f j).toNat * 2^(8*j)) =
      BitVec.ofNat 64 (∑ j ∈ Finset.range 8, (g j).toNat * 2^(8*j)) := by
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [same j (Finset.mem_range.mp hj)]

section bytes
variable (positions : Positions) (proof : Proof) (u j : Nat) (hj : j < 8)
include hj

private theorem div_mod_shape : (8*u+j)/1424 = u/178 ∧ (8*u+j)%1424 = 8*(u%178)+j := by
  constructor <;> omega

theorem byte_salt (h : u % 178 < 2) :
    expandByte positions proof (8*u+j) = (proof[8*(142*(u/178) + u % 178)+j]?).getD 0 := by
  obtain ⟨q, r⟩ := div_mod_shape u j hj
  unfold expandByte
  simp only [q, r]
  rw [if_pos (by omega), show 1136*(u/178) + (8*(u%178)+j) = 8*(142*(u/178) + u % 178)+j by omega]

theorem byte_prefix (h0 : ¬ u % 178 < 2) (h : u % 178 < 114) :
    expandByte positions proof (8*u+j) =
      (proof[8*(142*(u/178) + 2 + 20*((u % 178 - 2) / 16) +
        4*((capDigit (sortedIndex positions (u/178)) ((u % 178 - 2) / 16) + (u % 178 - 2) % 16 / 4 + 1) % 5) +
        (u % 178 - 2) % 4)+j]?).getD 0 := by
  obtain ⟨q, r⟩ := div_mod_shape u j hj
  unfold expandByte
  simp only [q, r]
  rw [if_neg (by omega), if_pos (by omega)]
  have k : (8*(u%178)+j - 16)/128 = (u % 178 - 2) / 16 := by omega
  simp only [k]
  generalize capDigit (sortedIndex positions (u/178)) ((u % 178 - 2) / 16) = d
  have i : (8*(u%178)+j - 16) % 128 / 32 = (u % 178 - 2) % 16 / 4 := by omega
  rw [i]
  have rot : (d + (u % 178 - 2) % 16 / 4 + 1) % 5 < 5 := Nat.mod_lt _ (by decide)
  congr 2
  omega

theorem byte_top (h : ¬ u % 178 < 114) :
    expandByte positions proof (8*u+j) =
      (proof[8*(142*positions.card + 20*(capFirst ((u % 178 - 114)/16) +
        capQuot (sortedIndex positions (u/178)) ((u % 178 - 114)/16) / 5) +
        (4*(capQuot (sortedIndex positions (u/178)) ((u % 178 - 114)/16) % 5 + 1) +
          (u % 178 - 114) % 16) % 20) + j]?).getD 0 := by
  obtain ⟨q, r⟩ := div_mod_shape u j hj
  unfold expandByte
  simp only [q, r]
  rw [if_neg (by omega), if_neg (by omega)]
  have lvl : (8*(u%178)+j - 912)/128 = (u % 178 - 114)/16 := by omega
  simp only [lvl]
  generalize capQuot (sortedIndex positions (u/178)) ((u % 178 - 114)/16) = qq
  generalize capFirst ((u % 178 - 114)/16) = first
  have rot : qq % 5 < 5 := Nat.mod_lt _ (by decide)
  have index : 1136*positions.card + 160*(first + qq/5) +
      32*((qq%5 + ((8*(u%178)+j - 912) % 128)/32 + 1) % 5) + (8*(u%178)+j - 912) % 32 =
      8*(142*positions.card + 20*(first + qq/5) + (4*(qq%5+1) + (u % 178 - 114) % 16) % 20) + j := by
    omega
  rw [index]

end bytes

/-- The record area of the expanded loader state. -/
theorem expanded_area {sub : Submission} (lay : WrapLayout sub) (input : CheckInput)
    (exact : input.proof.length = capLength input.positions) (u : Nat)
    (area : u < 178*input.positions.card) :
    BitVec.ofNat 64 (∑ j ∈ Finset.range 8, (((expandInput input).proof[8*u+j]?).getD 0).toNat * 2^(8*j)) =
      expandedWord sub input u := by
  have card := card_bound input.positions
  have bytes (j : Nat) (hj : j < 8) : ((expandInput input).proof[8*u+j]?).getD 0 =
      expandByte input.positions input.proof (8*u+j) := by
    have same : (expandInput input).proof = expandProof input.positions input.proof := rfl
    rw [same, expandProof, List.getElem?_map, List.getElem?_range (by omega)]
    rfl
  have room : ∀ x, x < 2^32 → proofWord + x < 2^33 := by
    intro x hx; unfold proofWord; omega
  unfold expandedWord sourceWord
  by_cases h0 : u % 178 < 2
  · rw [if_pos h0, proof_word lay input _ (room _ (by omega))]
    apply pack_congr
    intro j hj
    rw [bytes j hj, byte_salt _ _ _ _ hj h0]
  by_cases h : u % 178 < 114
  · rw [if_neg h0, if_pos h]
    dsimp only
    have rot : (capDigit (sortedIndex input.positions (u/178)) ((u % 178 - 2) / 16) + (u % 178 - 2) % 16 / 4 + 1) % 5 < 5 :=
      Nat.mod_lt _ (by decide)
    rw [proof_word lay input _ (room _ (by omega))]
    apply pack_congr
    intro j hj
    rw [bytes j hj, byte_prefix _ _ _ _ hj h0 h]
  · rw [if_neg h0, if_neg h]
    dsimp only
    have quot : capQuot (sortedIndex input.positions (u/178)) ((u % 178 - 114)/16) < 16777216 := by
      unfold capQuot
      have small := sorted_index_small input.positions (u/178)
      have := Nat.div_le_self (sortedIndex input.positions (u/178)) (5^(7+(u % 178 - 114)/16))
      omega
    have first : capFirst ((u % 178 - 114)/16) ≤ 54 := by
      unfold capFirst; split <;> omega
    rw [proof_word lay input _ (room _ (by omega))]
    apply pack_congr
    intro j hj
    rw [bytes j hj, byte_top _ _ _ _ hj h]

/-- The loader state of the expanded input is `expandedTarget` on every aligned word below `2^33`,
whenever the shared proof has the exact length. -/
theorem expanded_loader {sub : Submission} (lay : WrapLayout sub) (input : CheckInput)
    (exact : input.proof.length = capLength input.positions) (w : Nat) (small : w < 2^33) :
    memoryView (sub.initialState .check (expandInput input)) w = expandedTarget sub input w := by
  have card := card_bound input.positions
  unfold expandedTarget
  by_cases low : w < proofWord
  · rw [if_pos low, loader_word _ w small, loader_word _ w small]
    apply pack_congr
    intro j hj
    exact lower_input_byte lay input _ _ (by unfold proofWord at low; unfold PENTA_PROOF_BASE; omega)
  · obtain ⟨u, rfl⟩ : ∃ u, w = proofWord + u := ⟨w - proofWord, by omega⟩
    rw [proof_word lay (expandInput input) u small]
    rw [if_neg (by omega)]
    by_cases area : u < 178*input.positions.card
    · rw [if_pos (by omega), show proofWord + u - proofWord = u by omega]
      exact expanded_area lay input exact u area
    · rw [if_neg (by omega), ← zero_word]
      apply pack_congr
      intro j hj
      have past : (expandInput input).proof[8*u+j]? = none := by
        apply List.getElem?_eq_none
        rw [show (expandInput input).proof = expandProof input.positions input.proof from rfl,
          expand_proof_length]
        omega
      rw [past]
      rfl

end TwoPermutationPrototype.PentaWrap
