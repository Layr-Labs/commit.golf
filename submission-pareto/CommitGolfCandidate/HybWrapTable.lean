import CommitGolfCandidate.HybWrapEntry
import CommitGolfCandidate.HybWrapSpec

/-! The table copy (words 487-2696): the 263 level-12 nodes of the compact proof go to slots 0-4
of the 53 scratch groups at `H`. Also: the scratch region is zero in the loader state, and the
level-9 node words are proof words. -/

namespace TwoPermutationPrototype.HybWrap
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Checker TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.CheckActions
open TwoPermutationPrototype.PentaWrap (WrapLayout loaderReg loader_reg loader_pc loader_word proof_word proofWord)
open TwoPermutationPrototype.Quad.Checker (loaderReference packedImage)

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

/-! ### Loader facts -/

theorem scratch_zero (input : CheckInput) (w : Nat) (lo : 2^25 ≤ w) (hi : w < 2^26) :
    memoryView (start input) w = 0 := by
  rw [loader_word input w (by omega)]
  have zero : ∀ j < 8, inputByte loaderReference .check input (8*w+j) = 0 := by
    intro j hj
    have l := loader_layout.layout
    have base := PentaWrap.data_base_value loader_layout
    have e₁ : (DIGEST_BITS + 7) / 8 = 32 := rfl
    have no₁ : ¬ (4294971392 ≤ 8*w+j ∧ 8*w+j < 4294971392 + 32) := by omega
    have no₂ : ∀ n, ¬ (6375350304 ≤ 8*w+j ∧ 8*w+j < 6375350304 + n) := by intro n; omega
    have no₃ : ∀ n, ¬ (6509568096 ≤ 8*w+j ∧ 8*w+j < 6509568096 + n) := by intro n; omega
    have no₄ : ∀ n, ¬ (10804535392 ≤ 8*w+j ∧ 8*w+j < 10804535392 + n) := by intro n; omega
    unfold inputByte
    simp only [Submission.inputBuffers, l, fixedBuffer, positionsBuffer, valuesBuffer, e₁, List.find?_cons,
      List.find?_nil, no₁, no₂, no₃, no₄, decide_false, base]
    rw [if_neg (by omega)]
  rw [Finset.sum_eq_zero (fun j hj => by rw [zero j (Finset.mem_range.mp hj)]; simp)]
  rfl

private theorem digits32 (b : Nat → Nat) (bnd : ∀ i, b i < 256) (q : Nat) (hq : q < 4) :
    (∑ t ∈ Finset.range 32, b t * 2^(8*t)) % 2^256 / 2^(64*q) % 2^64 =
      ∑ j ∈ Finset.range 8, b (8*q+j) * 2^(8*j) := by
  let W : Nat → Nat := fun p => ∑ j ∈ Finset.range 8, b (8*p+j) * 2^(8*j)
  have Wlt : ∀ p, W p < 2^64 := by
    intro p
    have := bnd (8*p); have := bnd (8*p+1); have := bnd (8*p+2); have := bnd (8*p+3)
    have := bnd (8*p+4); have := bnd (8*p+5); have := bnd (8*p+6); have := bnd (8*p+7)
    simp only [W, Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
    omega
  have split : ∑ t ∈ Finset.range 32, b t * 2^(8*t) = W 0 + 2^64 * W 1 + 2^128 * W 2 + 2^192 * W 3 := by
    simp only [W, Finset.sum_range_succ, Finset.sum_range_zero]
    ring
  have w0 := Wlt 0; have w1 := Wlt 1; have w2 := Wlt 2; have w3 := Wlt 3
  rw [split]
  show _ = W q
  interval_cases q <;> simp only [Nat.reducePow, Nat.reduceMul, Nat.mul_zero, Nat.pow_zero] <;> omega

/-- Word `q` of a 32-byte digest at an aligned offset is the proof word there. -/
theorem digest_at_word (A : Proof) (off q : Nat) (aligned : off % 8 = 0) (hq : q < 4) :
    (digestAt A off).extractLsb' (64*q) 64 = packWord A (off/8+q) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat]
  unfold digestAt packWord
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    digits32 (fun t => ((A[off+t]?).getD 0).toNat) (fun t => BitVec.isLt _) q hq]
  have bound : ∑ j ∈ Finset.range 8, ((A[off + (8*q+j)]?).getD 0).toNat * 2^(8*j) < 2^64 := by
    have bnd : ∀ j, ((A[off + (8*q+j)]?).getD 0).toNat < 256 := fun j => BitVec.isLt _
    have := bnd 0; have := bnd 1; have := bnd 2; have := bnd 3
    have := bnd 4; have := bnd 5; have := bnd 6; have := bnd 7
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
    omega
  have e : ∑ j ∈ Finset.range 8, ((A[8*(off/8+q)+j]?).getD 0).toNat * 2^(8*j) =
      ∑ j ∈ Finset.range 8, ((A[off + (8*q+j)]?).getD 0).toNat * 2^(8*j) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [show 8*(off/8+q)+j = off + (8*q+j) by omega]
  rw [e, Nat.mod_eq_of_lt bound]

/-! ### The table copy -/

/-- Word of slot 0 of scratch group 0 of level 14. -/
def TW0 : Nat := 33554437

def tgroupOps (k g : Nat) : List Action :=
  copyActs .x6 .x7 0 0 (proofWord+114*k+20*g) (TW0+46*g) 20 ++
    [.offset .x6 .x6 160 (BitVec.ofNat 64 (PB+912*k+160*(g+1))), .offset .x7 .x7 368 (BitVec.ofNat 64 (H+40+368*(g+1)))]

theorem table_group_code_0 : ∀ i < 4, WrapAt (21+42*(4*0+i)) tableGroup := by decide
theorem table_group_code_1 : ∀ i < 4, WrapAt (21+42*(4*1+i)) tableGroup := by decide
theorem table_group_code_2 : ∀ i < 4, WrapAt (21+42*(4*2+i)) tableGroup := by decide
theorem table_group_code_3 : ∀ i < 4, WrapAt (21+42*(4*3+i)) tableGroup := by decide
theorem table_group_code_4 : ∀ i < 4, WrapAt (21+42*(4*4+i)) tableGroup := by decide
theorem table_group_code_5 : ∀ i < 4, WrapAt (21+42*(4*5+i)) tableGroup := by decide
theorem table_group_code_6 : ∀ i < 2, WrapAt (21+42*(4*6+i)) tableGroup := by decide
theorem table_group_code : ∀ g < 26, WrapAt (21+42*g) tableGroup := by
  intro g hg
  have e : g = 4*(g/4)+g%4 := by omega
  have hq : g/4 < 7 := by omega
  have hi : g%4 < 4 := Nat.mod_lt _ (by decide)
  have hr : g/4*4+g%4 < 26 := by omega
  rw [e]; revert hr hi hq; generalize g/4 = q; generalize g%4 = i; intro hq hi hr
  interval_cases q <;> first
    | exact table_group_code_0 i (by omega)
    | exact table_group_code_1 i (by omega)
    | exact table_group_code_2 i (by omega)
    | exact table_group_code_3 i (by omega)
    | exact table_group_code_4 i (by omega)
    | exact table_group_code_5 i (by omega)
    | exact table_group_code_6 i (by omega)

theorem table_half_code : WrapAt 1113 tableHalf := by decide

/-- Table copy invariant after `g` groups, from the entry state `e`. -/
structure TableAt (input : CheckInput) (e : MachineState) (g : Nat) (t : MachineState) : Prop where
  pc : t.pc = BitVec.ofNat 64 (4096+4*(464+(21+42*g)))
  x6 : t.getReg .x6 = BitVec.ofNat 64 (PB+912*input.positions.card+160*g)
  x7 : t.getReg .x7 = BitVec.ofNat 64 (H+40+368*g)
  keep : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x31 → t.getReg r = e.getReg r
  mem : ∀ w < 2^33, memoryView t w =
    if TW0 ≤ w ∧ (w-TW0)/46 < g ∧ (w-TW0)%46 < 20 then
      memoryView (start input) (proofWord+114*input.positions.card+20*((w-TW0)/46)+(w-TW0)%46)
    else memoryView (start input) w

theorem table_step (o : Oracle) (input : CheckInput) (e : MachineState) (g : Nat) (hg : g < 26) (t : MachineState)
    (at_ : TableAt input e g t) :
    ∃ cycles, Obs o packedImage t (fixedOps o (tgroupOps input.positions.card g) t) 42 cycles 0 [] ∧
      TableAt input e (g+1) (fixedOps o (tgroupOps input.positions.card g) t) := by
  have small := card_small input
  obtain ⟨okC, regsC, memC⟩ := copy_run o t .x6 .x7 (by decide) (by decide) 0 0 (proofWord+114*input.positions.card+20*g)
    (TW0+46*g) 20 (PB+912*input.positions.card+160*g) (H+40+368*g) at_.x6 at_.x7
    (by unfold PB proofWord; omega) (by unfold H TW0; omega) (by decide) (by decide)
    (by unfold proofWord; omega) (by unfold TW0; omega) (by unfold TW0 proofWord; omega)
  generalize hc : fixedOps o (copyActs .x6 .x7 0 0 (proofWord+114*input.positions.card+20*g) (TW0+46*g) 20) t = c
    at okC regsC memC
  have c6 : c.getReg .x6 = BitVec.ofNat 64 (PB+912*input.positions.card+160*g) := (regsC .x6 (by decide)).trans at_.x6
  have c7 : c.getReg .x7 = BitVec.ofNat 64 (H+40+368*g) := (regsC .x7 (by decide)).trans at_.x7
  have valid : validFixed o (tgroupOps input.positions.card g) t := by
    unfold tgroupOps
    rw [validFixed_append, hc]
    refine ⟨okC, ?_, ?_, trivial⟩
    · show c.getReg .x6 + signExtend12 160 = _
      rw [c6, show (160 : BitVec 12) = BitVec.ofNat 12 160 from rfl, add_small _ 160 (by decide) (by unfold PB; omega)]
      congr 1
    · show (putReg c .x6 _).getReg .x7 + signExtend12 368 = _
      rw [put_reg_reg, if_neg (by decide), c7, show (368 : BitVec 12) = BitVec.ofNat 12 368 from rfl,
        add_small _ 368 (by decide) (by unfold H; omega)]
      congr 1
  have code := table_group_code g hg
  have same : (tgroupOps input.positions.card g).map Action.op = tableGroup := by
    rw [tgroupOps, List.map_append, copy_acts_op]; rfl
  have cells := wrap_fetch_ops image_wrap code _ same
  have free : PermFree (tgroupOps input.positions.card g) :=
    perm_free_append (copy_free _ _ _ _ _ _ _) (by intro x hx; simp at hx; rcases hx with h | h <;> subst h <;> rfl)
  have ops := Obs.free o packedImage (tgroupOps input.positions.card g) (464+(21+42*g)) t at_.pc cells valid free
  have len : (tgroupOps input.positions.card g).length = 42 := by
    rw [tgroupOps, List.length_append, copy_acts_length]; rfl
  refine ⟨_, ops.cast len rfl rfl rfl, ?_⟩
  have fin : fixedOps o (tgroupOps input.positions.card g) t =
      putReg (putReg c .x6 (BitVec.ofNat 64 (PB+912*input.positions.card+160*(g+1)))) .x7
        (BitVec.ofNat 64 (H+40+368*(g+1))) := by
    unfold tgroupOps; rw [fixedOps_append, hc]; rfl
  rw [fin]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have := fixed_ops_pc o (tgroupOps input.positions.card g) t
    rw [fin, len, pc_after _ _ _ at_.pc] at this
    rw [this]; congr 2
  · rw [put_reg_reg, if_neg (by decide), put_reg_reg, if_pos ⟨rfl, by decide⟩]
  · rw [put_reg_reg, if_pos ⟨rfl, by decide⟩]
  · intro r h6 h7 h31
    rw [put_reg_reg, if_neg (fun h => h7 h.1.symm), put_reg_reg, if_neg (fun h => h6 h.1.symm), regsC r h31,
      at_.keep r h6 h7 h31]
  · intro w hw
    rw [put_reg_view, put_reg_view, memC w hw]
    by_cases fresh : TW0+46*g ≤ w ∧ w < TW0+46*g+20
    · rw [if_pos fresh, at_.mem _ (by unfold proofWord; omega), if_neg (by unfold TW0 proofWord; omega),
        if_pos (by unfold TW0 at fresh ⊢; omega)]
      apply congrArg (memoryView (start input))
      unfold TW0 at fresh ⊢
      have h1 : (w - 33554437)/46 = g := by omega
      have h2 : (w - 33554437)%46 = w - (33554437+46*g) := by omega
      rw [h1, h2]
    · rw [if_neg fresh, at_.mem w hw]
      unfold TW0 at fresh ⊢
      by_cases old : 33554437 ≤ w ∧ (w-33554437)/46 < g ∧ (w-33554437)%46 < 20
      · rw [if_pos old, if_pos (by omega)]
      · rw [if_neg old, if_neg (by omega)]

theorem table_loop (o : Oracle) (input : CheckInput) (e : MachineState) (t₀ : MachineState) (at₀ : TableAt input e 0 t₀) :
    ∀ g ≤ 26, ∃ t cycles, Obs o packedImage t₀ t (42*g) cycles 0 [] ∧ TableAt input e g t := by
  intro g
  induction g with
  | zero => intro _; exact ⟨t₀, 0, Obs.refl o packedImage t₀, at₀⟩
  | succ g ih =>
    intro hg
    obtain ⟨t, c, obs, at_⟩ := ih (by omega)
    obtain ⟨c', step, at'⟩ := table_step o input e g (by omega) t at_
    exact ⟨_, _, (obs.trans step).cast (by ring) rfl rfl rfl, at'⟩

/-! ### The last group: nodes 260-262 -/

def thalfOps (k : Nat) : List Action :=
  copyActs .x6 .x7 0 0 (proofWord+114*k+20*26) (TW0+46*26) 20 ++
    [.offset .x6 .x6 160 (BitVec.ofNat 64 (PB+912*k+160*26+160)), .offset .x7 .x7 368 (BitVec.ofNat 64 (H+40+368*27))]

/-- The table copy is complete: the 263 level-12 nodes are in slots 0-4 of the 53 groups. -/
structure TableDone (input : CheckInput) (e : MachineState) (t : MachineState) : Prop where
  pc : t.pc = BitVec.ofNat 64 (4096+4*(464+1155))
  keep : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x31 → t.getReg r = e.getReg r
  mem : ∀ w < 2^33, memoryView t w =
    if TW0 ≤ w ∧ (((w-TW0)/46 < 26 ∧ (w-TW0)%46 < 20) ∨ ((w-TW0)/46 = 26 ∧ (w-TW0)%46 < 20)) then
      memoryView (start input) (proofWord+114*input.positions.card+20*((w-TW0)/46)+(w-TW0)%46)
    else memoryView (start input) w

theorem table_half (o : Oracle) (input : CheckInput) (e : MachineState) (t : MachineState)
    (at_ : TableAt input e 26 t) :
    ∃ cycles, Obs o packedImage t (fixedOps o (thalfOps input.positions.card) t) 42 cycles 0 [] ∧
      TableDone input e (fixedOps o (thalfOps input.positions.card) t) := by
  have small := card_small input
  obtain ⟨okC, regsC, memC⟩ := copy_run o t .x6 .x7 (by decide) (by decide) 0 0 (proofWord+114*input.positions.card+20*26)
    (TW0+46*26) 20 (PB+912*input.positions.card+160*26) (H+40+368*26) at_.x6 at_.x7
    (by unfold PB proofWord; omega) (by unfold H TW0; omega) (by decide) (by decide)
    (by unfold proofWord; omega) (by unfold TW0; omega) (by unfold TW0 proofWord; omega)
  generalize hc : fixedOps o (copyActs .x6 .x7 0 0 (proofWord+114*input.positions.card+20*26) (TW0+46*26) 20) t = c
    at okC regsC memC
  have c6 : c.getReg .x6 = BitVec.ofNat 64 (PB+912*input.positions.card+160*26) := (regsC .x6 (by decide)).trans at_.x6
  have c7 : c.getReg .x7 = BitVec.ofNat 64 (H+40+368*26) := (regsC .x7 (by decide)).trans at_.x7
  have valid : validFixed o (thalfOps input.positions.card) t := by
    unfold thalfOps
    rw [validFixed_append, hc]
    refine ⟨okC, ?_, ?_, trivial⟩
    · show c.getReg .x6 + signExtend12 160 = _
      rw [c6, show (160 : BitVec 12) = BitVec.ofNat 12 160 from rfl, add_small _ 160 (by decide) (by unfold PB; omega)]
    · show (putReg c .x6 _).getReg .x7 + signExtend12 368 = _
      rw [put_reg_reg, if_neg (by decide), c7, show (368 : BitVec 12) = BitVec.ofNat 12 368 from rfl,
        add_small _ 368 (by decide) (by unfold H; omega)]
  have same : (thalfOps input.positions.card).map Action.op = tableHalf := by
    rw [thalfOps, List.map_append, copy_acts_op]; rfl
  have cells := wrap_fetch_ops image_wrap table_half_code _ same
  have free : PermFree (thalfOps input.positions.card) :=
    perm_free_append (copy_free _ _ _ _ _ _ _) (by intro x hx; simp at hx; rcases hx with h | h <;> subst h <;> rfl)
  have ops := Obs.free o packedImage (thalfOps input.positions.card) (464+1113) t (by rw [at_.pc]) cells valid free
  have len : (thalfOps input.positions.card).length = 42 := by
    rw [thalfOps, List.length_append, copy_acts_length]; rfl
  refine ⟨_, ops.cast len rfl rfl rfl, ?_⟩
  have fin : fixedOps o (thalfOps input.positions.card) t =
      putReg (putReg c .x6 (BitVec.ofNat 64 (PB+912*input.positions.card+160*26+160))) .x7
        (BitVec.ofNat 64 (H+40+368*27)) := by
    unfold thalfOps; rw [fixedOps_append, hc]; rfl
  refine ⟨?_, ?_, ?_⟩
  · have := fixed_ops_pc o (thalfOps input.positions.card) t
    rw [len, pc_after _ (464+1113) _ (by rw [at_.pc])] at this
    rw [this]
  · intro r h6 h7 h31
    rw [fin, put_reg_reg, if_neg (fun h => h7 h.1.symm), put_reg_reg, if_neg (fun h => h6 h.1.symm), regsC r h31,
      at_.keep r h6 h7 h31]
  · intro w hw
    rw [fin, put_reg_view, put_reg_view, memC w hw]
    by_cases fresh : TW0+46*26 ≤ w ∧ w < TW0+46*26+20
    · rw [if_pos fresh, at_.mem _ (by unfold proofWord; omega), if_neg (by unfold TW0 proofWord; omega),
        if_pos (by unfold TW0 at fresh ⊢; omega)]
      apply congrArg (memoryView (start input))
      unfold TW0 at fresh ⊢
      have h1 : (w - 33554437)/46 = 26 := by omega
      have h2 : (w - 33554437)%46 = w - (33554437+46*26) := by omega
      rw [h1, h2]
    · rw [if_neg fresh, at_.mem w hw]
      unfold TW0 at fresh ⊢
      by_cases old : 33554437 ≤ w ∧ (w-33554437)/46 < 26 ∧ (w-33554437)%46 < 20
      · rw [if_pos old, if_pos (by omega)]
      · rw [if_neg old, if_neg (by omega)]

/-- After the table copy: slot words of the level-9 nodes are the table words. -/
theorem table_slot (input : CheckInput) (e t : MachineState) (at_ : TableDone input e t) (j q : Nat)
    (hj : j < 135) (hq : q < 4) :
    memoryView t (TW0+46*(j/5)+4*(j%5)+q) =
      memoryView (start input) (proofWord+114*input.positions.card+4*j+q) := by
  have small := card_small input
  have hj5 : j = 5*(j/5) + j%5 := by omega
  have jm : j % 5 < 5 := Nat.mod_lt _ (by decide)
  have jd : j / 5 < 27 := by omega
  have last : j / 5 = 26 → j % 5 < 5 := by omega
  generalize j / 5 = a at *
  generalize j % 5 = b at *
  subst hj5
  have sub : TW0+46*a+4*b+q - TW0 = 46*a+(4*b+q) := by omega
  have dv : (46*a+(4*b+q))/46 = a := by omega
  have md : (46*a+(4*b+q))%46 = 4*b+q := by omega
  rw [at_.mem _ (by unfold TW0; omega), sub, dv, md, if_pos ⟨by omega, by
    by_cases h32 : a = 26
    · right; have := last h32; omega
    · left; omega⟩]
  apply congrArg (memoryView (start input))
  omega

end TwoPermutationPrototype.HybWrap
