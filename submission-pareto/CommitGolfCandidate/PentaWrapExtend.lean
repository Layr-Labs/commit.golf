import CommitGolfCandidate.PentaWrapHash
import CommitGolfCandidate.PentaCapRoundtrip

/-! The reconstructed (old-format) cap input behind a level-7-table proof.

For a fixed oracle, `extInput` appends to the submitted proof the 228 doublewords of levels 8, 9 and
10 that the hash phase computes (`hashedTable`, read from the first copy of each doubled group). Its
proof has the old cap length `912k + 8704`; the loader states of the two inputs agree everywhere
except on those 228 proof words. -/

namespace TwoPermutationPrototype.PentaWrap
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.RV64
open TwoPermutationPrototype.CheckActions

set_option maxRecDepth 100000

/-- The doubled table after the table loop: the 43 level-7 groups, zeros above. -/
def initialTable (sub : Submission) (input : CheckInput) (x : Nat) : Word :=
  if x < 1720 then tableWord sub input x else 0

def hashedTable (o : Oracle) (sub : Submission) (input : CheckInput) : Nat → Word :=
  hashTable o (initialTable sub input) 54

def tailWord (o : Oracle) (sub : Submission) (input : CheckInput) (t : Nat) : Word :=
  hashedTable o sub input (40*(43 + t/20) + t%20)

def wordBytes (w : Word) : List Byte := List.ofFn fun j : Fin 8 => w.extractLsb' (8*j.val) 8

def tailBytes (o : Oracle) (sub : Submission) (input : CheckInput) : List Byte :=
  (List.range 228).flatMap fun t => wordBytes (tailWord o sub input t)

def extInput (o : Oracle) (sub : Submission) (input : CheckInput) : CheckInput :=
  { input with proof := input.proof ++ tailBytes o sub input }

theorem word_bytes_length (w : Word) : (wordBytes w).length = 8 := by simp [wordBytes]

theorem tail_bytes_length (o : Oracle) (sub : Submission) (input : CheckInput) :
    (tailBytes o sub input).length = 1824 := by
  unfold tailBytes
  rw [flat_map_length _ 8 _ (fun x _ => word_bytes_length _)]
  simp

theorem ext_length (o : Oracle) (sub : Submission) (input : CheckInput) :
    (extInput o sub input).proof.length = input.proof.length + 1824 := by
  simp [extInput, tail_bytes_length]

private theorem sum_digits (value count : Nat) :
    (∑ i ∈ Finset.range count, (value / 2^(8*i) % 256) * 2^(8*i)) = value % 2^(8*count) := by
  induction count with
  | zero => simp only [Finset.sum_range_zero, Nat.mul_zero, Nat.pow_zero, Nat.mod_one]
  | succ count ih =>
    rw [Finset.sum_range_succ, ih, Nat.mul_succ, Nat.pow_add, Nat.mod_mul]
    simp only [Nat.reducePow, Nat.mul_comm]

theorem pack_word_bytes (w : Word) :
    BitVec.ofNat 64 (∑ j ∈ Finset.range 8, (((wordBytes w)[j]?).getD 0).toNat * 2^(8*j)) = w := by
  apply BitVec.eq_of_toNat_eq
  have terms : (∑ j ∈ Finset.range 8, (((wordBytes w)[j]?).getD 0).toNat * 2^(8*j)) =
      ∑ j ∈ Finset.range 8, (w.toNat / 2^(8*j) % 256) * 2^(8*j) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_range.mp hj
    simp only [wordBytes, List.getElem?_ofFn, hj', dite_true, Option.getD_some]
    simp only [BitVec.extractLsb', Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
  rw [terms, sum_digits, BitVec.toNat_ofNat]
  simp only [Nat.reduceMul, Nat.mod_mod]
  exact Nat.mod_eq_of_lt w.isLt

/-! ### Loader words of the reconstructed input -/

theorem ext_word_prefix {sub : Submission} (lay : WrapLayout sub) (o : Oracle) (input : CheckInput) (u : Nat)
    (small : proofWord + u < 2^33) (inside : 8*u+8 ≤ input.proof.length) :
    sourceWord sub (extInput o sub input) u = sourceWord sub input u := by
  unfold sourceWord
  rw [proof_word lay _ u small, proof_word lay _ u small]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_range.mp hj
  simp only [extInput]
  rw [List.getElem?_append_left (by omega)]

theorem ext_word_beyond {sub : Submission} (lay : WrapLayout sub) (o : Oracle) (input : CheckInput) (u : Nat)
    (small : proofWord + u < 2^33) (past : input.proof.length + 1824 ≤ 8*u) :
    sourceWord sub (extInput o sub input) u = 0 := by
  unfold sourceWord
  rw [show proofWord + u = proofWord + u from rfl]
  exact beyond_zero lay _ u (by rw [ext_length]; exact past) small

theorem ext_word_tail {sub : Submission} (lay : WrapLayout sub) (o : Oracle) (input : CheckInput) (L t : Nat)
    (len : input.proof.length = 8*L) (ht : t < 228) (small : proofWord + L + t < 2^33) :
    sourceWord sub (extInput o sub input) (L + t) = tailWord o sub input t := by
  unfold sourceWord
  rw [proof_word lay _ (L+t) (by omega)]
  conv_rhs => rw [← pack_word_bytes (tailWord o sub input t)]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_range.mp hj
  simp only [extInput]
  rw [List.getElem?_append_right (by omega), len, show 8*(L+t)+j-8*L = 8*t+j by omega]
  unfold tailBytes
  rw [flat_map_chunk _ 8 _ (fun x _ => word_bytes_length _) t j hj', List.getElem?_range ht, Option.bind_some]

theorem ext_view {sub : Submission} (lay : WrapLayout sub) (o : Oracle) (input : CheckInput) (L w : Nat)
    (len : input.proof.length = 8*L) (small : w < 2^33)
    (outside : w < proofWord + L ∨ proofWord + L + 228 ≤ w) :
    memoryView (sub.initialState .check (extInput o sub input)) w = memoryView (sub.initialState .check input) w := by
  by_cases low : w < proofWord
  · rw [loader_word _ w small, loader_word _ w small]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_range.mp hj
    exact congrArg (fun b : Byte => b.toNat * 2^(8*j))
      (lower_input_byte lay input _ _ (by unfold proofWord PENTA_PROOF_BASE at *; omega))
  · obtain ⟨u, rfl⟩ : ∃ u, w = proofWord + u := ⟨w - proofWord, by omega⟩
    rcases outside with a | a
    · exact ext_word_prefix lay o input u small (by omega)
    · rw [show memoryView (sub.initialState .check (extInput o sub input)) (proofWord + u) =
          sourceWord sub (extInput o sub input) u from rfl, ext_word_beyond lay o input u small (by omega)]
      exact (beyond_zero lay input u (by omega) small).symm

/-! ### Scratch memory is zero in the loader state -/

theorem scratch_byte {sub : Submission} (lay : WrapLayout sub) (input : CheckInput) (address : Nat)
    (low : address < 4294971392) : inputByte sub .check input address = 0 := by
  have base := data_base_value lay
  have hc : sub.layout.commitment = 4294971392 := by rw [lay.layout]
  have hi : sub.layout.indices = 6375350304 := by rw [lay.layout]
  have hv : sub.layout.values = 6509568096 := by rw [lay.layout]
  have hp : sub.layout.proof = 10804535392 := by rw [lay.layout]
  have e₁ : (DIGEST_BITS + 7) / 8 = 32 := rfl
  have e₂ : LEAF_SIZE / 8 = 256 := rfl
  have no₁ : ¬ (4294971392 ≤ address ∧ address < 4294971392 + 32) := by omega
  have no₂ : ¬ (6375350304 ≤ address ∧ address < 6375350304 + 8 * input.positions.card) := by omega
  have no₃ : ¬ (6509568096 ≤ address ∧ address < 6509568096 + 256 * input.positions.card) := by omega
  have no₄ : ¬ (10804535392 ≤ address ∧ address < 10804535392 + input.proof.length) := by omega
  have below : ¬ (2^36 ≤ address) := by omega
  unfold inputByte
  simp only [Submission.inputBuffers, hc, hi, hv, hp, fixedBuffer, positionsBuffer, valuesBuffer,
    Finset.length_sort, Finset.card_attach, e₁, e₂,
    List.find?_cons, List.find?_nil, no₁, no₂, no₃, no₄, decide_false, base, below, if_false]

theorem scratch_zero {sub : Submission} (lay : WrapLayout sub) (input : CheckInput) (w : Nat)
    (low : 8*w + 8 ≤ 4294971392) : memoryView (sub.initialState .check input) w = 0 := by
  rw [loader_word _ w (by omega)]
  have h (j : Nat) (hj : j ∈ Finset.range 8) :
      (inputByte sub .check input (8*w+j)).toNat * 2^(8*j) = 0 := by
    rw [scratch_byte lay input _ (by have := Finset.mem_range.mp hj; omega)]; simp
  rw [Finset.sum_eq_zero h]; rfl

/-! ### The hashed table -/

theorem dst_facts : ∀ i < 54, 1720 ≤ dstOff i ∧ dstOff i % 40 ≤ 16 ∧
    (dstOff i ≤ 2132 ∨ dstOff i = 2160 ∨ dstOff i = 2164) := by decide

theorem hash_table_keep (o : Oracle) (T : Nat → Word) (x : Nat) : ∀ n ≤ 54,
    (∀ i < n, ¬(dstOff i ≤ x ∧ x < dstOff i + 4) ∧ ¬(dstOff i + 20 ≤ x ∧ x < dstOff i + 24)) →
    hashTable o T n x = T x := by
  intro n
  induction n with
  | zero => intro _ _; rfl
  | succ n ih =>
    intro le avoid
    show hashStep o (hashTable o T n) n x = T x
    unfold hashStep
    obtain ⟨a, b⟩ := avoid n (by omega)
    rw [dif_neg a, dif_neg b]
    exact ih (by omega) (fun i hi => avoid i (by omega))

theorem hash_table_mirror (o : Oracle) (T : Nat → Word)
    (base : ∀ x, 1720 ≤ x → x < 2200 → 20 ≤ x % 40 → T x = T (x - 20)) :
    ∀ n ≤ 54, ∀ x, 1720 ≤ x → x < 2200 → 20 ≤ x % 40 → hashTable o T n x = hashTable o T n (x - 20) := by
  intro n
  induction n with
  | zero => intro _; exact base
  | succ n ih =>
    intro le x lo hi half
    obtain ⟨d₁, d₂, _⟩ := dst_facts n (by omega)
    show hashStep o (hashTable o T n) n x = hashStep o (hashTable o T n) n (x - 20)
    unfold hashStep
    have notLow : ¬(dstOff n ≤ x ∧ x < dstOff n + 4) := by omega
    rw [dif_neg notLow]
    by_cases high : dstOff n + 20 ≤ x ∧ x < dstOff n + 24
    · rw [dif_pos high, dif_pos (show dstOff n ≤ x - 20 ∧ x - 20 < dstOff n + 4 by omega)]
      congr 2; omega
    · rw [dif_neg high, dif_neg (show ¬(dstOff n ≤ x - 20 ∧ x - 20 < dstOff n + 4) by omega),
        dif_neg (show ¬(dstOff n + 20 ≤ x - 20 ∧ x - 20 < dstOff n + 24) by omega)]
      exact ih (by omega) x lo hi half

/-- Every doubled-table word of the reconstructed input is the hashed table's. -/
theorem hashed_table_word {sub : Submission} (lay : WrapLayout sub) (o : Oracle) (input : CheckInput)
    (k : Nat) (card : input.positions.card = k) (hk : k ≤ 16777216)
    (len : input.proof.length = 912*k + 6880) (x : Nat) (hx : x < 2200) :
    hashedTable o sub input x = tableWord sub (extInput o sub input) x := by
  have pw : proofWord = 1350566924 := rfl
  unfold tableWord
  rw [show (extInput o sub input).positions.card = k from card]
  by_cases low : x < 1720
  · rw [hashedTable, hash_table_keep o _ x 54 le_rfl (fun i hi => by
        obtain ⟨d₁, _, _⟩ := dst_facts i hi; omega), initialTable, if_pos low, tableWord, card,
      ext_word_prefix lay o input _ (by omega) (by omega)]
  · have G := x / 40
    have mirror : hashedTable o sub input x = hashedTable o sub input (40*(x/40) + (x%40)%20) := by
      by_cases half : 20 ≤ x % 40
      · rw [hashedTable, hash_table_mirror o _ (fun y a b c => by
            simp only [initialTable, if_neg (show ¬ y < 1720 by omega), if_neg (show ¬ y - 20 < 1720 by omega)])
          54 le_rfl x (by omega) hx half]
        congr 1; omega
      · congr 1; omega
    by_cases inTail : 20*(x/40 - 43) + (x%40)%20 < 228
    · rw [mirror, show 114*k + 20*(x/40) + (x%40)%20 = (114*k+860) + (20*(x/40 - 43) + (x%40)%20) by omega,
        ext_word_tail lay o input (114*k+860) _ (by omega) inTail (by omega), tailWord]
      congr 1; omega
    · rw [ext_word_beyond lay o input _ (by omega) (by rw [len]; omega), hashedTable,
        hash_table_keep o _ x 54 le_rfl (fun i hi => by obtain ⟨d₁, d₂, d₃⟩ := dst_facts i hi; omega),
        initialTable, if_neg low]

/-! ### From the 43-group table to the reconstructed 55-group table -/

set_option maxHeartbeats 2000000 in
theorem hash_bridge {sub : Submission} (lay : WrapLayout sub) (wrap : WrapImage (sub.image .check)) (o : Oracle)
    (input : CheckInput) (nonempty : input.positions.card ≠ 0)
    (exact : input.proof.length = capLength7 input.positions)
    (st : MachineState) (pc : st.pc = BitVec.ofNat 64 (4096+4*(460+315))) (at_ : TableAt sub input 43 43 st) :
    ∃ t : MachineState, ∃ rows : List PublicRow, (∀ fuel : Nat,
      checkEvaluation o (recordRows (execute (sub.image .check) (3142 + fuel) st false)) =
        let tail := checkEvaluation o (recordRows (execute (sub.image .check) fuel t false))
        ((tail.1.1.charge (3142 + 7 * 54) 54, rows ++ tail.1.2), 54 + tail.2)) ∧
      t.pc = BitVec.ofNat 64 (4096+4*(460+3457)) ∧ TableAt sub (extInput o sub input) 55 55 t := by
  let k := input.positions.card
  have card : k ≤ 16777216 := card_bound' input.positions
  have len : input.proof.length = 912*k + 6880 := by rw [exact]; unfold capLength7; simp [k, nonempty]
  have pw : proofWord = 1350566924 := rfl
  have tw : TBW = 33554432 := rfl
  have hw : HBW = 67108864 := rfl
  have ow : OBW = 67108896 := rfl
  let init := sub.initialState .check input
  have kept (r : Reg) (m : r ∈ keptRegs) : st.getReg r = init.getReg r := at_.kept r m
  have tbl : ∀ x < 2200, memoryView st (TBW+x) = initialTable sub input x := by
    intro x hx
    unfold initialTable
    by_cases low : x < 1720
    · rw [if_pos low]; exact at_.table x (by omega)
    · rw [if_neg low, at_.rest _ (by omega) (by omega) (by omega)]
      exact scratch_zero lay input _ (by omega)
  have scratch (j : Nat) (base : Nat) (hb : base = HBW ∨ base = OBW) (hj : j < 25) :
      memoryView st (base+j) = 0 := by
    rw [at_.rest _ (by rcases hb with h | h <;> subst h <;> omega) (by rcases hb with h | h <;> subst h <;> omega)
      (by rcases hb with h | h <;> subst h <;> omega)]
    exact scratch_zero lay input _ (by rcases hb with h | h <;> subst h <;> omega)
  have phase := hash_phase o wrap st pc (initialTable sub input) tbl (fun j hj => scratch j HBW (Or.inl rfl) hj)
      (fun j hj => scratch j OBW (Or.inr rfl) hj) _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl
  obtain ⟨_, tpc, z10, z11, z12, z13, z17, z6, z7, frame, ttbl, tmem⟩ := phase 0
  refine ⟨_, _, fun fuel => (phase fuel).1, tpc, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [z6, at_.x6, show signExtend12 (1920 : BitVec 12) = BitVec.ofNat 64 1920 by decide, ← BitVec.ofNat_add]
    exact congrArg (BitVec.ofNat 64) (by simp only [extInput])
  · rw [z7]
  · rw [frame _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), at_.x28]
  · intro r member
    have regExt : (sub.initialState .check (extInput o sub input)).getReg r =
        loaderReg input.positions.card (input.proof.length + 1824) r := by
      rw [loader_reg lay, ext_length]; rfl
    rw [regExt]
    simp only [keptRegs, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h
    · rw [frame _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), kept _ (by decide), loader_reg lay]; rfl
    · rw [frame _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), kept _ (by decide), loader_reg lay]; rfl
    · rw [frame _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), kept _ (by decide), loader_reg lay]; rfl
    · rw [frame _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), kept _ (by decide), loader_reg lay]; rfl
    · rw [z10, kept _ (by decide), loader_reg lay]; rfl
    · rw [z11, kept _ (by decide), loader_reg lay]; rfl
    · rw [z12, kept _ (by decide), loader_reg lay]; rfl
    · rw [z13, kept _ (by decide), loader_reg lay]; rfl
    · rw [frame _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), kept _ (by decide), loader_reg lay]; rfl
    · rw [frame _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), kept _ (by decide), loader_reg lay]; rfl
    · rw [frame _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), kept _ (by decide), loader_reg lay]; rfl
    · rw [z17, kept _ (by decide), loader_reg lay, show signExtend12 (1824 : BitVec 12) = BitVec.ofNat 64 1824 by decide]
      show BitVec.ofNat 64 input.proof.length + BitVec.ofNat 64 1824 = BitVec.ofNat 64 (input.proof.length + 1824)
      rw [← BitVec.ofNat_add]
  · intro x hx
    rw [ttbl x hx]
    exact hashed_table_word lay o input k rfl card len x hx
  · intro f hf
    simp only [show (extInput o sub input).positions.card = k from rfl]
    rw [tmem _ (by omega) (by omega)]
    by_cases low : f < 860
    · exact at_.cleared f (by omega)
    · rw [at_.rest _ (by omega) (by omega) (by omega)]
      rw [show proofWord + 114*k + f = proofWord + (114*k+f) by omega]
      exact beyond_zero lay input (114*k+f) (by omega) (by omega)
  · intro w hw' side side'
    simp only [show (extInput o sub input).positions.card = k from rfl] at side'
    rw [tmem w hw' side, at_.rest w hw' (by omega) (by omega)]
    exact (ext_view lay o input (114*k+860) w (by omega) hw' (by omega)).symm

end TwoPermutationPrototype.PentaWrap
