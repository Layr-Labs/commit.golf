import CommitGolfCandidate.HybWrapLevel
import CommitGolfCandidate.PentaWrapLoader

/-! One record of the expansion (words 2542-3413): the compact record goes to the buffer, the salt
and the 17 levels are written, then the virtual index; the latch steps to the previous record. -/

namespace TwoPermutationPrototype.HybWrap
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Checker TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.CheckActions
open TwoPermutationPrototype.PentaWrap (loaderReg proof_word proofWord index_word)
open TwoPermutationPrototype.Quad.Checker (loaderReference packedImage)

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

/-! ### Donor words of a record -/

theorem expanded_salt (positions : Positions) (proof : Proof) (up : Nat → Nat → BitVec 256) (r e : Nat) (he : e < 2) :
    expandedWord positions proof up (275*r+e) = packWord proof (82*r+e) := by
  unfold expandedWord
  rw [show (275*r+e)/275 = r by omega, show (275*r+e)%275 = e by omega]
  simp only [he, if_true]

theorem expanded_virt (positions : Positions) (proof : Proof) (up : Nat → Nat → BitVec 256) (r : Nat) :
    expandedWord positions proof up (275*r+2) = BitVec.ofNat 64 (virtIndex (sortedIndex positions r)) := by
  unfold expandedWord
  rw [show (275*r+2)/275 = r by omega, show (275*r+2)%275 = 2 by omega]
  simp

theorem expanded_level (positions : Positions) (proof : Proof) (up : Nat → Nat → BitVec 256) (r k m : Nat)
    (hk : k < 17) (hm : m < 16) :
    expandedWord positions proof up (275*r+(3+16*k+m)) =
      if k < 2 then packWord proof (82*r+2+16*k+m)
      else if k = 2 then
        (if (sortedIndex positions r / placeValue k % 3+m/4+3)%5 < 2 then 0
         else packWord proof (82*r+34+4*(((sortedIndex positions r / placeValue k % 3+m/4+3)%5+6-
           sortedIndex positions r / placeValue k % 3)%3)+m%4))
      else if k < 13 then
        (if m/4 = 3*(sortedIndex positions r / placeValue k % 2) then packWord proof (82*r+42+4*(k-3)+m%4) else 0)
      else (up (k-13) (5*(sortedIndex positions r / placeValue k / 5) +
        (sortedIndex positions r / placeValue k % 5 + m/4 + 1) % 5)).extractLsb' (64*(m%4)) 64 := by
  unfold expandedWord
  rw [show (275*r+(3+16*k+m))/275 = r by omega, show (275*r+(3+16*k+m))%275 = 3+16*k+m by omega]
  simp only [show ¬ (3+16*k+m < 2) by omega, show ¬ (3+16*k+m = 2) by omega, if_false]
  rw [show (3+16*k+m-3)/16 = k by omega, show (3+16*k+m-3)%16 = m by omega]

/-- Partial virtual index: the slot digits of the first `k` levels. -/
def vsum (index k : Nat) : Nat := ∑ i ∈ Finset.range k, hybridSlot index i * 5^i

theorem vsum_lt (index k : Nat) : vsum index k < 5^k := by
  induction k with
  | zero => simp [vsum]
  | succ k ih =>
    unfold vsum at *
    rw [Finset.sum_range_succ, pow_succ]
    have := hybrid_slot_lt index k
    have : hybridSlot index k * 5^k ≤ 4 * 5^k := Nat.mul_le_mul_right _ (by omega)
    omega

theorem virt_sum (index : Nat) : vsum index 17 = virtIndex index := by
  have gen : ∀ n k, (∑ i ∈ Finset.range n, hybridSlot index (k+i) * 5^i) = virtFrom index k n := by
    intro n
    induction n with
    | zero => intro k; simp [virtFrom]
    | succ n ih =>
      intro k
      rw [Finset.sum_range_succ', virtFrom, ← ih (k+1)]
      simp only [Nat.add_zero, pow_zero, Nat.mul_one, pow_succ]
      rw [Finset.mul_sum]
      rw [Nat.add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [show k + (i+1) = k+1+i by omega]
      ring
  have := gen 17 0
  simp only [Nat.zero_add] at this
  unfold vsum virtIndex
  rw [this]; rfl

/-! ### The level loop of a record -/

abbrev expW (o : Oracle) (input : CheckInput) (v : Nat) : Word :=
  expandedWord input.positions input.proof (U o input) v

theorem slot_low (index k : Nat) (hk : k < 2) : hybridSlot index k = index / placeValue k % 5 := by
  unfold hybridSlot; rw [slot_base_low k (by unfold PENTA_LOW; omega), radix_low k (by unfold PENTA_LOW; omega)]; simp

theorem slot_quad (index : Nat) : hybridSlot index 2 = index / placeValue 2 % 3 + 2 := by
  unfold hybridSlot; rw [show slotBase 2 = 2 from slot_base_quad, show radix 2 = 3 from radix_quad]; omega

theorem slot_high (index k : Nat) (hk : 3 ≤ k) (hk' : k < 13) : hybridSlot index k = index / placeValue k % 2 + 3 := by
  unfold hybridSlot
  rw [slot_base_mid k (by unfold BIN_LOW; omega) (by unfold PENTA_HIGH; omega),
    radix_mid k (by unfold BIN_LOW; omega) (by unfold PENTA_HIGH; omega)]; omega

theorem slot_top (index k : Nat) (hk : 13 ≤ k) : hybridSlot index k = index / placeValue k % 5 := by
  unfold hybridSlot; rw [slot_base_high k (by unfold PENTA_HIGH; omega), radix_high k (by unfold PENTA_HIGH; omega)]; simp

theorem place_low (k : Nat) (hk : k < 2) : placeValue (k+1) = placeValue k * 5 := by
  rw [placeValue, radix_low k (by unfold PENTA_LOW; omega)]

theorem place_quad : placeValue 3 = placeValue 2 * 3 := by
  rw [placeValue, show radix 2 = 3 from radix_quad]

theorem place_high (k : Nat) (hk : 3 ≤ k) (hk' : k < 13) : placeValue (k+1) = placeValue k * 2 := by
  rw [placeValue, radix_mid k (by unfold BIN_LOW; omega) (by unfold PENTA_HIGH; omega)]

theorem place_top (k : Nat) (hk : 13 ≤ k) : placeValue (k+1) = placeValue k * 5 := by
  rw [placeValue, radix_high k (by unfold PENTA_HIGH; omega)]

/-- The record context: the buffer holds compact record `r`, the scratch tables the upper nodes. -/
structure RecCtx (o : Oracle) (input : CheckInput) (r : Nat) (base : MachineState) : Prop where
  present : r < input.positions.card
  buf : ∀ m < 82, memoryView base (BUFW+m) = packWord input.proof (82*r+m)
  slots : ∀ L, 13 ≤ L → L ≤ 16 → ∀ j < 5 * groups L, ∀ q < 4,
    memoryView base (slotW L j + q) = (U o input (L-13) j).extractLsb' (64*q) 64

structure LevelInv (o : Oracle) (input : CheckInput) (r : Nat) (base : MachineState) (k : Nat) (t : MachineState) :
    Prop where
  pre : LevelPre k (proofWord+275*r+3+16*k) (sortedIndex input.positions r / placeValue k)
    (vsum (sortedIndex input.positions r) k) t
  pc : t.pc = BitVec.ofNat 64 (4096+4*(464+levelOff k))
  kept : ∀ x, LevelKept x → t.getReg x = base.getReg x
  mem : ∀ w < 2^33, memoryView t w =
    if proofWord+275*r+3 ≤ w ∧ w < proofWord+275*r+3+16*k then expW o input (w - proofWord) else memoryView base w

theorem level_ends : ∀ k < 17, levelOff (k+1) = levelOff k + (levelCode k).length := by decide

theorem level_step (o : Oracle) (input : CheckInput) (r : Nat) (base : MachineState) (ctx : RecCtx o input r base)
    (k : Nat) (hk : k < 17) (t : MachineState) (inv : LevelInv o input r base k t) :
    ∃ t' cycles, Obs o packedImage t t' (levelCode k).length cycles 0 [] ∧ LevelInv o input r base (k+1) t' := by
  have small := card_small input
  have idxLt := sorted_index_small input.positions r
  generalize hi : sortedIndex input.positions r = idx at inv idxLt
  have nLt : idx / placeValue k < pentaCount k := place_div_lt_count idx idxLt k
  have nB : idx / placeValue k < 2^40 := by
    have := Nat.div_le_self idx (placeValue k); omega
  have vLt := vsum_lt idx k
  have code := level_codes k hk
  have ends := level_ends k hk
  have hr := ctx.present
  let D := proofWord+275*r+3+16*k
  have hDv : D = proofWord+275*r+3+16*k := rfl
  have hD : D + 16 ≤ 2^33 := by rw [hDv]; unfold proofWord; omega
  have pre0 : LevelPre k D (idx / placeValue k) (vsum idx k) t := by rw [← hi]; exact inv.pre
  have sameT : ∀ w < 2^33, ¬ (proofWord+275*r+3 ≤ w ∧ w < proofWord+275*r+3+16*k) →
      memoryView t w = memoryView base w := by
    intro w hw out; rw [inv.mem w hw, if_neg out]
  -- block value from the level lemma, then the next invariant
  have finish : ∀ (ops : List Action) (t' : MachineState) (n' V' : Nat),
      ops.map Action.op = levelCode k → PermFree ops → validFixed o ops t →
      LevelPre (k+1) (D+16) n' V' t' → fixedOps o ops t = t' →
      n' = idx / placeValue (k+1) → V' = vsum idx (k+1) →
      (∀ x, LevelKept x → t'.getReg x = t.getReg x) →
      (∀ w < 2^33, D ≤ w → w < D+16 → memoryView t' w = expW o input (w - proofWord)) →
      (∀ w < 2^33, ¬ (D ≤ w ∧ w < D+16) → memoryView t' w = memoryView t w) →
      ∃ t' cycles, Obs o packedImage t t' (levelCode k).length cycles 0 [] ∧ LevelInv o input r base (k+1) t' := by
    intro ops t' n' V' same free ok pre' eq hn hV keep blk out
    have len : ops.length = (levelCode k).length := by rw [← same, List.length_map]
    have obs := Obs.free o packedImage ops (464+levelOff k) t inv.pc (wrap_fetch_ops image_wrap code ops same) ok free
    rw [eq] at obs
    refine ⟨t', _, obs.cast len rfl rfl rfl, ?_, ?_, ?_, ?_⟩
    · rw [hn, hV] at pre'
      have e : D + 16 = proofWord+275*r+3+16*(k+1) := by show proofWord+275*r+3+16*k+16 = _; ring
      rw [e] at pre'; rw [hi]; exact pre'
    · rw [← eq, fixed_ops_pc, pc_after _ _ _ inv.pc, len, ends]; rw [Nat.add_assoc]
    · intro x hx; rw [keep x hx, inv.kept x hx]
    · intro w hw
      by_cases nb : D ≤ w ∧ w < D+16
      · rw [blk w hw nb.1 nb.2, if_pos ⟨by omega, by omega⟩]
      · rw [out w hw nb, inv.mem w hw]
        by_cases old : proofWord+275*r+3 ≤ w ∧ w < proofWord+275*r+3+16*k
        · rw [if_pos old, if_pos ⟨old.1, by omega⟩]
        · rw [if_neg old, if_neg (by omega)]
  -- word positions inside the block
  have wpos : ∀ w, D ≤ w → w < D+16 → w - proofWord = 275*r+(3+16*k+(w-D)) := by
    intro w a b; omega
  by_cases low : k < 2
  · obtain ⟨ok, pre', keep, mem⟩ := penta_level o k D (idx / placeValue k) (vsum idx k) t low pre0 nB vLt hD
      (by rw [hDv]; unfold BUFW proofWord; omega)
    refine finish _ _ _ _ (by rw [penta_acts_op]; unfold levelCode; rw [if_pos low]) (penta_free _ _ _ _) ok pre' rfl
      (by rw [place_low k low, Nat.div_div_eq_div_mul]) (by unfold vsum; rw [Finset.sum_range_succ, slot_low idx k low])
      keep ?_ ?_
    · intro w hw a b
      rw [mem w hw, if_pos ⟨a, b⟩, sameT _ (by unfold BUFW; omega) (by unfold BUFW proofWord; omega),
        show BUFW+2+16*k+(w-D) = BUFW+(2+16*k+(w-D)) by omega, ctx.buf _ (by omega), wpos w a b, expW,
        expanded_level _ _ _ r k (w-D) hk (by omega), if_pos low]
      congr 1; omega
    · intro w hw nb; rw [mem w hw, if_neg nb]
  · by_cases quad : k = 2
    · subst quad
      obtain ⟨ok, pre', keep, mem⟩ := quad_level o D (idx / placeValue 2) (vsum idx 2) t pre0 nB vLt hD
        (by rw [hDv]; unfold BUFW proofWord; omega)
      refine finish _ _ _ _ (by rw [quad_acts_op]; unfold levelCode; rw [if_neg low, if_pos rfl]) (quad_free _ _ _) ok pre'
        rfl (by rw [place_quad, Nat.div_div_eq_div_mul])
        (by show vsum idx 2 + (idx / placeValue 2 % 3 + 2) * 25 = vsum idx (2+1)
            unfold vsum; rw [Finset.sum_range_succ _ 2, slot_quad idx]; rfl)
        keep ?_ ?_
      · intro w hw a b
        rw [mem w hw, if_pos ⟨a, b⟩, wpos w a b, expW, expanded_level _ _ _ r 2 (w-D) hk (by omega), if_neg low,
          if_pos rfl, hi]
        by_cases zero : (idx / placeValue 2 % 3 + (w-D)/4 + 3) % 5 < 2
        · rw [if_pos zero, if_pos zero]
        · rw [if_neg zero, if_neg zero]
          have t4 := Nat.mod_lt (((idx / placeValue 2 % 3 + (w-D)/4 + 3) % 5) + 6 - idx / placeValue 2 % 3) (show 3 > 0 by decide)
          rw [sameT _ (by unfold BUFW; omega) (by unfold BUFW proofWord; omega),
            show BUFW+34+4*(((idx / placeValue 2 % 3 + (w-D)/4 + 3) % 5 + 6 - idx / placeValue 2 % 3) % 3)+(w-D)%4 =
              BUFW+(34+4*(((idx / placeValue 2 % 3 + (w-D)/4 + 3) % 5 + 6 - idx / placeValue 2 % 3) % 3)+(w-D)%4) by omega,
            ctx.buf _ (by omega)]
          congr 1; omega
      · intro w hw nb; rw [mem w hw, if_neg nb]
    by_cases mid : k < 13
    · obtain ⟨ok, pre', keep, mem⟩ := bin_low o k D (idx / placeValue k) (vsum idx k) t (by omega) (by omega) pre0
        nB vLt hD (by rw [hDv]; unfold BUFW proofWord; omega)
      refine finish _ _ _ _ (by rw [bin_low_op]; unfold levelCode; rw [if_neg low, if_neg quad, if_pos mid]) (bin_low_free _ _ _ _) ok
        pre' rfl (by rw [place_high k (by omega) mid, Nat.div_div_eq_div_mul])
        (by unfold vsum; rw [Finset.sum_range_succ, slot_high idx k (by omega) mid]) keep ?_ ?_
      · intro w hw a b
        rw [mem w hw, if_pos ⟨a, b⟩, wpos w a b, expW, expanded_level _ _ _ r k (w-D) hk (by omega), if_neg low,
          if_neg quad, if_pos mid, hi]
        have m2 := Nat.mod_lt (idx / placeValue k) (show 2 > 0 by decide)
        by_cases sib : D+12*(idx / placeValue k % 2) ≤ w ∧ w < D+12*(idx / placeValue k % 2)+4
        · rw [if_pos sib, if_pos (by omega), sameT _ (by unfold BUFW; omega) (by unfold BUFW proofWord; omega),
            show BUFW+42+4*(k-3)+(w-(D+12*(idx / placeValue k % 2))) = BUFW+(42+4*(k-3)+(w-(D+12*(idx / placeValue k % 2))))
              by omega, ctx.buf _ (by omega)]
          congr 1; omega
        · rw [if_neg sib, if_neg (by omega)]
      · intro w hw nb; rw [mem w hw, if_neg nb]
    · obtain ⟨ok, pre', keep, mem⟩ := penta_high o k D (idx / placeValue k) (vsum idx k) t (by omega) (by omega) pre0
        nLt vLt hD (by rw [hDv]; unfold TEND proofWord; omega)
      refine finish _ _ _ _ (by rw [penta_high_op]; unfold levelCode; rw [if_neg low, if_neg quad, if_neg mid]) (penta_high_free _ _ _ _) ok
        pre' rfl (by rw [place_top k (by omega), Nat.div_div_eq_div_mul])
        (by unfold vsum; rw [Finset.sum_range_succ, slot_top idx k (by omega)]) keep ?_ ?_
      · intro w hw a b
        rw [mem w hw, if_pos ⟨a, b⟩, wpos w a b, expW, expanded_level _ _ _ r k (w-D) hk (by omega), if_neg low,
          if_neg quad, if_neg mid, hi]
        have cnt := count_penta k (by omega) (by omega)
        have hb := hb_val k (by omega) (by omega)
        have nc : idx / placeValue k < count k := by rw [cnt]; exact nLt
        generalize hn : idx / placeValue k = n at nc ⊢
        have gk : n / 5 < groups k := by unfold groups; omega
        have t5 := Nat.mod_lt (n%5+(w-D)/4+1) (show 5 > 0 by decide)
        have jlt : sibSlot n ((w-D)/4) < 5 * groups k := by unfold sibSlot; omega
        have q4 : (w-D)%4 < 4 := Nat.mod_lt _ (by decide)
        have slotIn : slotW k (sibSlot n ((w-D)/4)) + 4 ≤ TEND := by
          unfold slotW groupW sibSlot
          rw [show (5*(n/5)+(n%5+(w-D)/4+1)%5)/5 = n/5 by omega,
            show (5*(n/5)+(n%5+(w-D)/4+1)%5)%5 = (n%5+(w-D)/4+1)%5 by omega]
          have h2 := hb.2.1
          omega
        have far' : TEND ≤ proofWord := by unfold TEND proofWord; omega
        rw [sameT _ (by unfold TEND at slotIn; omega) (by omega),
          ctx.slots k (by omega) (by omega) _ jlt _ q4]
        unfold sibSlot
        congr 2 <;> omega
      · intro w hw nb; rw [mem w hw, if_neg nb]

theorem level_off_mono : ∀ k ≤ 17, levelOff 0 ≤ levelOff k := by decide

theorem level_loop (o : Oracle) (input : CheckInput) (r : Nat) (base : MachineState) (ctx : RecCtx o input r base)
    (t₀ : MachineState) (inv₀ : LevelInv o input r base 0 t₀) :
    ∀ k ≤ 17, ∃ t cycles, Obs o packedImage t₀ t (levelOff k - levelOff 0) cycles 0 [] ∧ LevelInv o input r base k t := by
  intro k
  induction k with
  | zero => intro _; exact ⟨t₀, 0, by simpa using Obs.refl o packedImage t₀, inv₀⟩
  | succ k ih =>
    intro hk
    obtain ⟨t, c, obs, inv⟩ := ih (by omega)
    obtain ⟨t', c', step, inv'⟩ := level_step o input r base ctx k (by omega) t inv
    have e := level_ends k (by omega)
    have m := level_off_mono k (by omega)
    exact ⟨t', _, (obs.trans step).cast (by omega) rfl rfl rfl, inv'⟩

/-! ### The record loop invariant -/

def IDXW : Nat := 796918788
def IDXB : Nat := 6375350304

def RecKept (x : Reg) : Prop :=
  x ≠ .x1 ∧ x ≠ .x3 ∧ x ≠ .x4 ∧ x ≠ .x5 ∧ x ≠ .x6 ∧ x ≠ .x7 ∧ x ≠ .x8 ∧ x ≠ .x9 ∧ x ≠ .x10 ∧ x ≠ .x11 ∧ x ≠ .x12 ∧
    x ≠ .x18 ∧ x ≠ .x19 ∧ x ≠ .x20 ∧ x ≠ .x21 ∧ x ≠ .x22 ∧ x ≠ .x23 ∧ x ≠ .x30 ∧ x ≠ .x31

instance (x : Reg) : Decidable (RecKept x) := by unfold RecKept; infer_instance

/-- Everything but the program counter of the record loop, `c` records left, from the state `e`. -/
structure RecMem (o : Oracle) (input : CheckInput) (e : MachineState) (c : Nat) (t : MachineState) : Prop where
  x8 : t.getReg .x8 = BitVec.ofNat 64 (PB+656*c-656)
  x9 : t.getReg .x9 = BitVec.ofNat 64 (PB+2200*c-2200)
  x18 : t.getReg .x18 = BitVec.ofNat 64 (IDXB+8*c-8)
  x19 : t.getReg .x19 = BitVec.ofNat 64 c
  x20 : t.getReg .x20 = BitVec.ofNat 64 BUF
  x4 : t.getReg .x4 = BitVec.ofNat 64 5
  x30 : t.getReg .x30 = BitVec.ofNat 64 96
  x5 : t.getReg .x5 = BitVec.ofNat 64 368
  keep : ∀ x, RecKept x → t.getReg x = e.getReg x
  slots : ∀ L, 13 ≤ L → L ≤ 16 → ∀ j < 5 * groups L, ∀ q < 4,
    memoryView t (slotW L j + q) = (U o input (L-13) j).extractLsb' (64*q) 64
  low : ∀ w < 2^33, (w < 2^25 ∨ 2^26 ≤ w) → w < proofWord + 82*c → memoryView t w = memoryView (start input) w
  exp : ∀ w < 2^33, proofWord + 275*c ≤ w → w < proofWord + 275*input.positions.card →
    memoryView t w = expW o input (w - proofWord)
  high : ∀ w < 2^33, proofWord + 275*input.positions.card ≤ w → memoryView t w = memoryView (start input) w

/-! ### The front of a record: buffer copy, salt and index -/

theorem record_codes : WrapAt 2078 recordCopy ∧ WrapAt 2242 saltCode ∧ WrapAt 2943 (latchCode.take 6) ∧
    wrapCode[2949]? = some (.BNE .x19 .x0 4708) := by decide

def saltActs (r idx : Nat) : List Action :=
  copyActs .x20 .x9 0 0 BUFW (proofWord+275*r) 2 ++
    [.load .x21 .x18 0 (IDXW+r), .offset .x22 .x21 0 (BitVec.ofNat 64 idx), .offset .x23 .x0 0 (BitVec.ofNat 64 0),
     .offset .x1 .x0 1 (BitVec.ofNat 64 1), .offset .x7 .x9 24 (BitVec.ofNat 64 (8*(proofWord+275*r)+24))]

theorem salt_acts_op (r idx : Nat) : (saltActs r idx).map Action.op = saltCode := by
  simp only [saltActs, List.map_append, copy_acts_op]; rfl

theorem salt_free (r idx : Nat) : PermFree (saltActs r idx) := by
  refine perm_free_append (copy_free _ _ _ _ _ _ _) ?_
  intro x hx; simp at hx; rcases hx with h | h | h | h | h <;> subst h <;> rfl

theorem index_view (input : CheckInput) (r : Nat) (present : r < input.positions.card) :
    memoryView (start input) (IDXW + r) = BitVec.ofNat 64 (sortedIndex input.positions r) :=
  index_word loader_layout input r present

theorem record_front (o : Oracle) (input : CheckInput) (e : MachineState) (c : Nat) (hc1 : 1 ≤ c)
    (hc : c ≤ input.positions.card) (t : MachineState) (mem : RecMem o input e c t)
    (pc : t.pc = BitVec.ofNat 64 (4096+4*(464+2078))) :
    ∃ base cycles, Obs o packedImage t base 173 cycles 0 [] ∧ RecCtx o input (c-1) base ∧
      LevelInv o input (c-1) base 0 base ∧
      (∀ x, LevelKept x → RecKept x → base.getReg x = e.getReg x) ∧
      base.getReg .x8 = t.getReg .x8 ∧ base.getReg .x9 = t.getReg .x9 ∧ base.getReg .x18 = t.getReg .x18 ∧
      base.getReg .x19 = t.getReg .x19 ∧
      (∀ w < 2^33, memoryView base w =
        if proofWord+275*(c-1) ≤ w ∧ w < proofWord+275*(c-1)+2 then expW o input (w - proofWord)
        else if BUFW ≤ w ∧ w < BUFW+82 then packWord input.proof (82*(c-1)+(w-BUFW))
        else memoryView t w) := by
  have small := card_small input
  obtain ⟨r, rfl⟩ : ∃ r, c = r+1 := ⟨c-1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have present : r < input.positions.card := by omega
  obtain ⟨cR, sR, _, _⟩ := record_codes
  -- copy the compact record to the buffer
  have x8 : t.getReg .x8 = BitVec.ofNat 64 (PB+656*r) := by rw [mem.x8]; congr 1
  obtain ⟨okC, regsC, memC⟩ := copy_run o t .x8 .x20 (by decide) (by decide) 0 0 (proofWord+82*r) BUFW 82
    (PB+656*r) BUF x8 mem.x20 (by unfold PB proofWord; omega) (by unfold BUF BUFW; omega) (by decide) (by decide)
    (by unfold proofWord; omega) (by unfold BUFW; omega) (Or.inr (by unfold BUFW proofWord; omega))
  have obsC := Obs.free o packedImage _ (464+2078) t pc (wrap_fetch_ops image_wrap cR _ (copy_acts_op _ _ _ _ _ _ _))
    okC (copy_free _ _ _ _ _ _ _)
  generalize hp : fixedOps o (copyActs .x8 .x20 0 0 (proofWord+82*r) BUFW 82) t = p at okC regsC memC obsC
  have bufP : ∀ m < 82, memoryView p (BUFW+m) = packWord input.proof (82*r+m) := by
    intro m hm
    rw [memC _ (by unfold BUFW; omega), if_pos (by omega), show proofWord+82*r+(BUFW+m-BUFW) = proofWord+(82*r+m) by omega,
      mem.low _ (by unfold proofWord; omega) (Or.inr (by unfold proofWord; omega)) (by omega)]
    show memoryView (loaderReference.initialState .check input) _ = _
    rw [proof_word loader_layout input _ (by unfold proofWord; omega)]
    rfl
  have pcP : p.pc = BitVec.ofNat 64 (4096+4*(464+2242)) := by
    rw [← hp, fixed_ops_pc, pc_after _ _ _ pc, copy_acts_length]
  -- salt words and the index
  have x9 : p.getReg .x9 = BitVec.ofNat 64 (8*(proofWord+275*r)) := by
    rw [regsC .x9 (by decide), mem.x9]; unfold PB proofWord; congr 1; omega
  obtain ⟨okS, regsS, memS⟩ := copy_run o p .x20 .x9 (by decide) (by decide) 0 0 BUFW (proofWord+275*r) 2 BUF
    (8*(proofWord+275*r)) ((regsC .x20 (by decide)).trans mem.x20) x9 (by unfold BUF BUFW; omega) (by omega) (by decide)
    (by decide) (by unfold BUFW; omega) (by unfold proofWord; omega) (Or.inl (by unfold BUFW proofWord; omega))
  generalize hq : fixedOps o (copyActs .x20 .x9 0 0 BUFW (proofWord+275*r) 2) p = q at okS regsS memS
  have q18 : q.getReg .x18 = BitVec.ofNat 64 (8*(IDXW+r)) := by
    rw [regsS .x18 (by decide), regsC .x18 (by decide), mem.x18]; unfold IDXB IDXW; congr 1; omega
  have idxQ : memoryView q (IDXW+r) = BitVec.ofNat 64 (sortedIndex input.positions r) := by
    rw [memS _ (by unfold IDXW; omega), if_neg (by unfold IDXW proofWord; omega),
      memC _ (by unfold IDXW; omega), if_neg (by unfold IDXW BUFW; omega),
      mem.low _ (by unfold IDXW; omega) (Or.inr (by unfold IDXW; omega)) (by unfold IDXW proofWord; omega),
      index_view input r present]
  have idxLt := sorted_index_small input.positions r
  let u₁ := putReg q .x21 (memoryView q (IDXW+r))
  let u₂ := putReg u₁ .x22 (BitVec.ofNat 64 (sortedIndex input.positions r))
  let u₃ := putReg u₂ .x23 (BitVec.ofNat 64 0)
  let u₄ := putReg u₃ .x1 (BitVec.ofNat 64 1)
  let base := putReg u₄ .x7 (BitVec.ofNat 64 (8*(proofWord+275*r)+24))
  have baseEq : fixedOps o (saltActs r (sortedIndex input.positions r)) p = base := by
    unfold saltActs; rw [fixedOps_append, hq]; rfl
  have u9 : u₄.getReg .x9 = BitVec.ofNat 64 (8*(proofWord+275*r)) := by
    simp only [u₄, u₃, u₂, u₁, put_reg_reg, ne_eq, reduceCtorEq, false_and, if_false]
    rw [regsS .x9 (by decide), x9]
  have okSalt : validFixed o (saltActs r (sortedIndex input.positions r)) p := by
    unfold saltActs
    rw [validFixed_append, hq]
    refine ⟨okS, ⟨?_, by unfold IDXW; omega⟩, ?_, ?_, ?_, ?_, trivial⟩
    · rw [q18, show (0 : BitVec 12) = BitVec.ofNat 12 0 from rfl, add_small _ 0 (by decide) (by unfold IDXW; omega)]; rfl
    · show u₁.getReg .x21 + _ = _
      simp only [u₁, put_reg_reg, ne_eq, reduceCtorEq, not_false_eq_true, and_self, if_true]
      rw [idxQ, show (0 : BitVec 12) = BitVec.ofNat 12 0 from rfl, add_small _ 0 (by decide) (by omega)]; rfl
    · show u₂.getReg .x0 + _ = _; rw [reg_zero]; decide
    · show u₃.getReg .x0 + _ = _; rw [reg_zero]; decide
    · show u₄.getReg .x9 + _ = _
      rw [u9, show (24 : BitVec 12) = BitVec.ofNat 12 24 from rfl, add_small _ 24 (by decide) (by unfold proofWord; omega)]
  have obsS := Obs.free o packedImage _ (464+2242) p pcP (wrap_fetch_ops image_wrap sR _ (salt_acts_op _ _)) okSalt
    (salt_free _ _)
  rw [baseEq] at obsS
  have baseView : ∀ w < 2^33, memoryView base w = memoryView q w := by
    intro w _; simp only [base, u₄, u₃, u₂, u₁, put_reg_view]
  have baseKeep : ∀ x, x ≠ .x7 → x ≠ .x1 → x ≠ .x23 → x ≠ .x22 → x ≠ .x21 → x ≠ .x31 → base.getReg x = t.getReg x := by
    intro x a b c d f g
    simp only [base, u₄, u₃, u₂, u₁]
    rw [put_reg_reg, if_neg (fun h => a h.1.symm), put_reg_reg, if_neg (fun h => b h.1.symm), put_reg_reg,
      if_neg (fun h => c h.1.symm), put_reg_reg, if_neg (fun h => d h.1.symm), put_reg_reg, if_neg (fun h => f h.1.symm),
      regsS x g, regsC x g]
  have baseBuf : ∀ m < 82, memoryView base (BUFW+m) = packWord input.proof (82*r+m) := by
    intro m hm
    rw [baseView _ (by unfold BUFW; omega), memS _ (by unfold BUFW; omega), if_neg (by unfold BUFW proofWord; omega),
      bufP m hm]
  refine ⟨base, _, (obsC.trans obsS).cast (by rw [copy_acts_length]; rfl) rfl rfl rfl, ⟨present, baseBuf, ?_⟩, ?_, ?_,
    baseKeep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    baseKeep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    baseKeep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    baseKeep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ?_⟩
  · intro L h1 h2 j hj q' hq
    have hb := hb_val L h1 (by omega)
    have sw : slotW L j + q' + 4 ≤ TEND + 4 := by unfold slotW groupW groups at *; omega
    rw [baseView _ (by unfold TEND at sw; omega), memS _ (by unfold TEND at sw; omega),
      if_neg (by unfold TEND proofWord at *; omega), memC _ (by unfold TEND at sw; omega),
      if_neg (by unfold slotW groupW groups BUFW TEND at *; omega), mem.slots L h1 h2 j hj q' hq]
  · refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, fun _ _ => rfl, fun w _ => ?_⟩
    · show base.getReg .x7 = _
      simp only [base, put_reg_reg, ne_eq, reduceCtorEq, not_false_eq_true, and_self, if_true]
      congr 1
    · rw [baseKeep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), mem.x20]
    · simp only [base, u₄, u₃, u₂, put_reg_reg, ne_eq, reduceCtorEq, not_false_eq_true, and_self, if_true, false_and,
        if_false]
      simp [placeValue]
    · simp only [base, u₄, u₃, put_reg_reg, ne_eq, reduceCtorEq, not_false_eq_true, and_self, if_true, false_and,
        if_false]
      simp [vsum]
    · simp only [base, u₄, put_reg_reg, ne_eq, reduceCtorEq, not_false_eq_true, and_self, if_true, false_and,
        if_false]
      simp
    · rw [baseKeep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), mem.x4]
    · rw [baseKeep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), mem.x30]
    · rw [baseKeep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), mem.x5]
    · rw [← baseEq, fixed_ops_pc, pc_after _ _ _ pcP]; rfl
    · rw [if_neg (by omega)]
  · intro x lk rk
    obtain ⟨a, b, c', d, f, g, h, i, j, l⟩ := lk
    rw [baseKeep x d a j i (by unfold RecKept at rk; tauto) l, mem.keep x rk]
  · intro w hw
    rw [baseView w hw, memS w hw]
    by_cases salt : proofWord+275*r ≤ w ∧ w < proofWord+275*r+2
    · rw [if_pos salt, if_pos salt, memC _ (by unfold BUFW; omega), if_pos (by unfold BUFW; omega)]
      show _ = expandedWord input.positions input.proof (U o input) _
      rw [show w - proofWord = 275*r+(w-(proofWord+275*r)) by omega, expanded_salt _ _ _ r _ (by omega),
        show proofWord+82*r+(BUFW+(w-(proofWord+275*r))-BUFW) = proofWord+(82*r+(w-(proofWord+275*r))) by omega,
        mem.low _ (by unfold proofWord; omega) (Or.inr (by unfold proofWord; omega)) (by omega)]
      show memoryView (loaderReference.initialState .check input) _ = _
      rw [proof_word loader_layout input _ (by unfold proofWord; omega)]
      rfl
    · rw [if_neg salt, if_neg salt, memC w hw]
      by_cases bf : BUFW ≤ w ∧ w < BUFW+82
      · rw [if_pos bf, if_pos bf, ← bufP (w-BUFW) (by omega), show BUFW+(w-BUFW) = w by omega, memC w hw, if_pos bf]
      · rw [if_neg bf, if_neg bf]

/-! ### The latch and one whole record -/

def latchActs (r : Nat) : List Action :=
  [.store .x9 .x23 16 (proofWord+275*r+2), .offset .x8 .x8 3440 (BitVec.ofNat 64 (PB+656*r-656)),
   .offset .x9 .x9 2996 (BitVec.ofNat 64 (PB+2200*r-1100)), .offset .x9 .x9 2996 (BitVec.ofNat 64 (PB+2200*r-2200)),
   .offset .x18 .x18 4088 (BitVec.ofNat 64 (IDXB+8*r-8)), .offset .x19 .x19 4095 (BitVec.ofNat 64 r)]

theorem latch_op (r : Nat) : (latchActs r).map Action.op = latchCode.take 6 := rfl

theorem latch_free (r : Nat) : PermFree (latchActs r) := by
  intro x hx; simp [latchActs] at hx; rcases hx with h | h | h | h | h | h <;> subst h <;> rfl

theorem record_step (o : Oracle) (input : CheckInput) (e : MachineState) (c : Nat) (hc1 : 1 ≤ c)
    (hc : c ≤ input.positions.card) (t : MachineState) (mem : RecMem o input e c t)
    (pc : t.pc = BitVec.ofNat 64 (4096+4*(464+2078))) :
    ∃ t' cycles, Obs o packedImage t t' 872 cycles 0 [] ∧ RecMem o input e (c-1) t' ∧
      t'.pc = BitVec.ofNat 64 (4096+4*(464+(if c-1 = 0 then 2950 else 2078))) := by
  have small := card_small input
  obtain ⟨base, cF, obsF, ctx, inv₀, keepF, f8, f9, f18, f19, memF⟩ := record_front o input e c hc1 hc t mem pc
  obtain ⟨r, rfl⟩ : ∃ r, c = r+1 := ⟨c-1, by omega⟩
  simp only [Nat.add_sub_cancel] at *
  obtain ⟨t₂₁, cL, obsL, inv⟩ := level_loop o input r base ctx base inv₀ 17 le_rfl
  have idxLt := sorted_index_small input.positions r
  -- registers before the latch
  have l9 : t₂₁.getReg .x9 = BitVec.ofNat 64 (PB+2200*r) := by
    rw [inv.kept .x9 (by unfold LevelKept; decide), f9, mem.x9]; congr 1
  have l8 : t₂₁.getReg .x8 = BitVec.ofNat 64 (PB+656*r) := by
    rw [inv.kept .x8 (by unfold LevelKept; decide), f8, mem.x8]; congr 1
  have l18 : t₂₁.getReg .x18 = BitVec.ofNat 64 (IDXB+8*r) := by
    rw [inv.kept .x18 (by unfold LevelKept; decide), f18, mem.x18]; congr 1
  have l19 : t₂₁.getReg .x19 = BitVec.ofNat 64 (r+1) := by
    rw [inv.kept .x19 (by unfold LevelKept; decide), f19, mem.x19]
  have l23 : t₂₁.getReg .x23 = BitVec.ofNat 64 (virtIndex (sortedIndex input.positions r)) := by
    rw [inv.pre.x23, virt_sum]
  let a₁ := putWord t₂₁ (proofWord+275*r+2) (t₂₁.getReg .x23)
  let a₂ := putReg a₁ .x8 (BitVec.ofNat 64 (PB+656*r-656))
  let a₃ := putReg a₂ .x9 (BitVec.ofNat 64 (PB+2200*r-1100))
  let a₄ := putReg a₃ .x9 (BitVec.ofNat 64 (PB+2200*r-2200))
  let a₅ := putReg a₄ .x18 (BitVec.ofNat 64 (IDXB+8*r-8))
  let a₆ := putReg a₅ .x19 (BitVec.ofNat 64 r)
  have latchEq : fixedOps o (latchActs r) t₂₁ = a₆ := rfl
  have okL : validFixed o (latchActs r) t₂₁ := by
    refine ⟨⟨?_, by unfold proofWord; omega⟩, ?_, ?_, ?_, ?_, ?_, trivial⟩
    · rw [l9, show (16 : BitVec 12) = BitVec.ofNat 12 16 from rfl, add_small _ 16 (by decide) (by unfold PB; omega)]
      unfold wordAddress PB proofWord; congr 1; omega
    · show a₁.getReg .x8 + _ = _
      rw [put_word_reg, l8, show (3440 : BitVec 12) = BitVec.ofNat 12 3440 from rfl,
        add_neg (PB+656*r) 3440 (by decide) (by decide) (by unfold PB; omega) (by unfold PB; omega)]
    · show a₂.getReg .x9 + _ = _
      rw [put_reg_reg, if_neg (by decide), put_word_reg, l9, show (2996 : BitVec 12) = BitVec.ofNat 12 2996 from rfl,
        add_neg (PB+2200*r) 2996 (by decide) (by decide) (by unfold PB; omega) (by unfold PB; omega)]
    · show a₃.getReg .x9 + _ = _
      rw [put_reg_reg, if_pos ⟨rfl, by decide⟩, show (2996 : BitVec 12) = BitVec.ofNat 12 2996 from rfl,
        add_neg (PB+2200*r-1100) 2996 (by decide) (by decide) (by unfold PB; omega) (by unfold PB; omega)]
      congr 1
    · show a₄.getReg .x18 + _ = _
      rw [put_reg_reg, if_neg (by decide), put_reg_reg, if_neg (by decide), put_reg_reg, if_neg (by decide),
        put_word_reg, l18, show (4088 : BitVec 12) = BitVec.ofNat 12 4088 from rfl,
        add_neg (IDXB+8*r) 4088 (by decide) (by decide) (by unfold IDXB; omega) (by unfold IDXB; omega)]
    · show a₅.getReg .x19 + _ = _
      rw [put_reg_reg, if_neg (by decide), put_reg_reg, if_neg (by decide), put_reg_reg, if_neg (by decide),
        put_reg_reg, if_neg (by decide), put_word_reg, l19, show (4095 : BitVec 12) = BitVec.ofNat 12 4095 from rfl,
        add_neg (r+1) 4095 (by decide) (by decide) (by omega) (by omega)]
      congr 1
  have pcL : t₂₁.pc = BitVec.ofNat 64 (4096+4*(464+2943)) := by rw [inv.pc]; rfl
  obtain ⟨_, _, cLatch, cBne⟩ := record_codes
  have obsA := Obs.free o packedImage (latchActs r) (464+2943) t₂₁ pcL (wrap_fetch_ops image_wrap cLatch _ (latch_op r))
    okL (latch_free r)
  rw [latchEq] at obsA
  have pc6 : a₆.pc = BitVec.ofNat 64 (4096+4*(464+2949)) := by
    rw [← latchEq, fixed_ops_pc, pc_after _ _ _ pcL]; rfl
  have a19 : a₆.getReg .x19 = BitVec.ofNat 64 r := by
    show (putReg a₅ .x19 _).getReg .x19 = _; rw [put_reg_reg, if_pos ⟨rfl, by decide⟩]
  let fin := execInstrBr a₆ (.BNE .x19 .x0 4708)
  have obsB := Obs.step o packedImage a₆ fin _ (wrap_fetch image_wrap _ 2949 _ cBne pc6) (branch_step _ _ (Or.inl rfl))
  have finReg : ∀ x, fin.getReg x = a₆.getReg x := fun x => by
    show (execInstrBr a₆ (.BNE .x19 .x0 4708)).getReg x = _; rw [bne_exec, set_pc_reg]
  have finView : memoryView fin = memoryView a₆ := by
    show memoryView (execInstrBr a₆ (.BNE .x19 .x0 4708)) = _; rw [bne_exec, set_pc_view]
  have aView : ∀ w < 2^33, memoryView a₆ w =
      if w = proofWord+275*r+2 then t₂₁.getReg .x23 else memoryView t₂₁ w := by
    intro w hw
    simp only [a₆, a₅, a₄, a₃, a₂, put_reg_view]
    exact put_word_view _ _ _ _ (by unfold proofWord; omega) (by omega)
  have aKeep : ∀ x, x ≠ .x8 → x ≠ .x9 → x ≠ .x18 → x ≠ .x19 → a₆.getReg x = t₂₁.getReg x := by
    intro x h8 h9 h18 h19
    simp only [a₆, a₅, a₄, a₃, a₂]
    rw [put_reg_reg, if_neg (fun h => h19 h.1.symm), put_reg_reg, if_neg (fun h => h18 h.1.symm), put_reg_reg,
      if_neg (fun h => h9 h.1.symm), put_reg_reg, if_neg (fun h => h9 h.1.symm), put_reg_reg,
      if_neg (fun h => h8 h.1.symm), put_word_reg]
  -- memory of t₂₁ outside the new words
  have t21View : ∀ w < 2^33, memoryView t₂₁ w =
      if proofWord+275*r+3 ≤ w ∧ w < proofWord+275*r+3+16*17 then expW o input (w - proofWord)
      else if proofWord+275*r ≤ w ∧ w < proofWord+275*r+2 then expW o input (w - proofWord)
      else if BUFW ≤ w ∧ w < BUFW+82 then packWord input.proof (82*r+(w-BUFW))
      else memoryView t w := by
    intro w hw
    rw [inv.mem w hw, memF w hw]
  have hl : (latchActs r).length = 6 := rfl
  have hlo : levelOff 17 - levelOff 0 = 692 := by decide
  refine ⟨fin, _, (obsF.trans (obsL.trans (obsA.trans obsB))).cast (by rw [hl, hlo]) rfl rfl rfl, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [finReg]; show (putReg a₅ .x19 _).getReg .x8 = _
      rw [put_reg_reg, if_neg (by decide), put_reg_reg, if_neg (by decide), put_reg_reg, if_neg (by decide),
        put_reg_reg, if_neg (by decide), put_reg_reg, if_pos ⟨rfl, by decide⟩]
    · rw [finReg]; show (putReg a₅ .x19 _).getReg .x9 = _
      rw [put_reg_reg, if_neg (by decide), put_reg_reg, if_neg (by decide), put_reg_reg, if_pos ⟨rfl, by decide⟩]
    · rw [finReg]; show (putReg a₅ .x19 _).getReg .x18 = _
      rw [put_reg_reg, if_neg (by decide), put_reg_reg, if_pos ⟨rfl, by decide⟩]
    · rw [finReg, a19]
    · rw [finReg, aKeep _ (by decide) (by decide) (by decide) (by decide), inv.pre.x20]
    · rw [finReg, aKeep _ (by decide) (by decide) (by decide) (by decide), inv.pre.x4]
    · rw [finReg, aKeep _ (by decide) (by decide) (by decide) (by decide), inv.pre.x30]
    · rw [finReg, aKeep _ (by decide) (by decide) (by decide) (by decide), inv.pre.x5]
    · intro x rk
      have lk : LevelKept x := by unfold RecKept at rk; unfold LevelKept; tauto
      rw [finReg, aKeep x (by unfold RecKept at rk; tauto) (by unfold RecKept at rk; tauto)
        (by unfold RecKept at rk; tauto) (by unfold RecKept at rk; tauto), inv.kept x lk, keepF x lk rk]
    · intro L h1 h2 j hj q hq
      have hb := hb_val L h1 (by omega)
      have sw : slotW L j + q + 4 ≤ TEND + 4 := by unfold slotW groupW groups at *; omega
      rw [finView, aView _ (by unfold TEND at sw; omega), if_neg (by unfold TEND proofWord at *; omega),
        t21View _ (by unfold TEND at sw; omega), if_neg (by unfold TEND proofWord at *; omega),
        if_neg (by unfold TEND proofWord at *; omega), if_neg (by unfold slotW groupW groups BUFW TEND at *; omega),
        mem.slots L h1 h2 j hj q hq]
    · intro w hw out below
      rw [finView, aView w hw, if_neg (by omega), t21View w hw, if_neg (by omega), if_neg (by omega),
        if_neg (by unfold BUFW at *; omega), mem.low w hw out (by omega)]
    · intro w hw lo hi
      rw [finView, aView w hw]
      by_cases v : w = proofWord+275*r+2
      · rw [if_pos v, l23]
        show _ = expandedWord input.positions input.proof (U o input) _
        rw [v, show proofWord+275*r+2-proofWord = 275*r+2 by omega, expanded_virt]
      · rw [if_neg v, t21View w hw]
        by_cases lv : proofWord+275*r+3 ≤ w ∧ w < proofWord+275*r+3+16*17
        · rw [if_pos lv]
        · rw [if_neg lv]
          by_cases sl : proofWord+275*r ≤ w ∧ w < proofWord+275*r+2
          · rw [if_pos sl]
          · rw [if_neg sl, if_neg (by unfold BUFW proofWord at *; omega), mem.exp w hw (by omega) hi]
    · intro w hw hi
      have hr : r < input.positions.card := by omega
      rw [finView, aView w hw, if_neg (by omega), t21View w hw, if_neg (by omega), if_neg (by omega),
        if_neg (by unfold BUFW proofWord at *; omega), mem.high w hw hi]
  · show (execInstrBr a₆ (.BNE .x19 .x0 4708)).pc = _
    rw [bne_exec, a19, reg_zero, pc6]
    by_cases z : r = 0
    · rw [if_pos (by rw [z]), if_pos z]
      show (BitVec.ofNat 64 (4096+4*(464+2949)) + 4 : Word) = _
      decide
    · rw [if_neg (by rw [show (0#64 : Word) = BitVec.ofNat 64 0 from rfl, word_eq_iff _ _ (by omega) (by decide)]; exact z),
        if_neg z]
      show (BitVec.ofNat 64 (4096+4*(464+2949)) + signExtend13 4708 : Word) = _
      decide

end TwoPermutationPrototype.HybWrap
