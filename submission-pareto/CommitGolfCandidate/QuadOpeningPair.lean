import CommitGolfCandidate.QuadOpeningLevel

/-! Paired record levels `(2p, 2p+1)`, `p = 0, 1, 2`: one division of the level-`2p` node by 25
selects one of 25 copy variants, which copies the four siblings at both levels. -/

namespace TwoPermutationPrototype.QuadOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 TwoPermutationPrototype.Sampling
open QOpening (trapdoorBase proofBase nonceBase)

attribute [local simp] QOpening.getReg_setReg MachineState.getReg_setPC

/-! ### Copy blocks with a register base and a fixed extra offset -/

set_option maxRecDepth 100000 in
theorem gen_offset_value : ∀ r < 5, ∀ v < 5, ∀ m < 16,
    signExtend12 (BitVec.ofNat 12 (368*r+variantOffset v m)) = BitVec.ofNat 64 (368*r+variantOffset v m) := by
  decide

set_option maxRecDepth 100000 in
theorem gen_store_value : ∀ k < 7, ∀ m < 16,
    signExtend12 (BitVec.ofNat 12 (storeOffset k m)) = BitVec.ofNat 64 (storeOffset k m) := by
  decide

theorem addr_small (S c : Nat) (h : signExtend12 (BitVec.ofNat 12 c) = BitVec.ofNat 64 c) :
    BitVec.ofNat 64 S + signExtend12 (BitVec.ofNat 12 c) = BitVec.ofNat 64 (S+c) := by
  rw [h, ← BitVec.ofNat_add]

theorem gen_pairs_get (reg : Reg) (off k v m : Nat) (hm : m < 16) :
    (genPairs reg off k v 16)[2*m]? = some (.LD .x31 reg (BitVec.ofNat 12 (off+variantOffset v m))) ∧
    (genPairs reg off k v 16)[2*m+1]? = some (.SD .x21 .x31 (BitVec.ofNat 12 (storeOffset k m))) := by
  unfold genPairs
  constructor
  · rw [show 2*m = 2*m+0 by omega, chunk_get _ 2 _ (fun _ _ => rfl) m 0 (by decide), List.getElem?_range hm]
    rfl
  · rw [chunk_get _ 2 _ (fun _ _ => rfl) m 1 (by decide), List.getElem?_range hm]
    rfl

theorem gen_pairs_succ (reg : Reg) (off k v n : Nat) : genPairs reg off k v (n+1) =
    genPairs reg off k v n ++ [.LD .x31 reg (BitVec.ofNat 12 (off+variantOffset v n)),
      .SD .x21 .x31 (BitVec.ofNat 12 (storeOffset k n))] := by
  simp [genPairs, List.range_succ, List.flatMap_append]

/-- One load/store pair of a generalized copy block. -/
theorem gen_pair_step (init state : MachineState) (source : Nat → Nat) (reg : Reg) (start off k v w count S T D : Nat)
    (r31 : reg ≠ .x31) (hk : k < 7) (live : w < 16) (code : CodeAt start (genPairs reg off k v 16))
    (addr : BitVec.ofNat 64 S + signExtend12 (BitVec.ofNat 12 (off+variantOffset v w)) =
      BitVec.ofNat 64 (T+variantOffset v w))
    (pc : state.pc = BitVec.ofNat 64 (4096+4*(start+2*w)))
    (from_ : state.getReg reg = BitVec.ofNat 64 S) (to_ : state.getReg .x21 = BitVec.ofNat 64 D)
    (target : D+storeOffset k w = proofBase+8*count) (aligned : T % 8 = 0) (low : trapdoorBase ≤ T)
    (high : T+160 ≤ proofBase) (fits : proofBase+8*count+8 ≤ MEMORY_BYTES)
    (named : source count = T+variantOffset v w) (inv : Inv init state source count) :
    let after := execInstrBr (execInstrBr state (.LD .x31 reg (BitVec.ofNat 12 (off+variantOffset v w))))
      (.SD .x21 .x31 (BitVec.ofNat 12 (storeOffset k w)))
    Runs state after 2 2 ∧ Inv init after source (count+1) ∧ after.pc = state.pc+8 ∧
      ∀ r, r ≠ .x31 → after.getReg r = state.getReg r := by
  intro after
  have offsetS := gen_store_value k hk w live
  have bound := variant_offset_bound v w
  have room : MEMORY_BYTES < 2^64 := by decide
  have heap : trapdoorBase % 8 = 0 := by decide
  have proofAligned : proofBase % 8 = 0 := by decide
  have below : proofBase ≤ MEMORY_BYTES := by decide
  let loaded := execInstrBr state (.LD .x31 reg (BitVec.ofNat 12 (off+variantOffset v w)))
  have loadAddress : state.getReg reg + signExtend12 (BitVec.ofNat 12 (off+variantOffset v w)) =
      BitVec.ofNat 64 (T+variantOffset v w) := by
    rw [from_, addr]
  have storeAddress : loaded.getReg .x21 + signExtend12 (BitVec.ofNat 12 (storeOffset k w)) =
      BitVec.ofNat 64 (proofBase+8*count) := by
    have keep : loaded.getReg .x21 = state.getReg .x21 := by
      simp [loaded, execInstrBr, QOpening.getReg_setReg]
    rw [keep, to_, offsetS, ← BitVec.ofNat_add, target]
  have codes := gen_pairs_get reg off k v w live
  have loadCode : program[start+2*w]? = some (.LD .x31 reg (BitVec.ofNat 12 (off+variantOffset v w))) := by
    have := code (2*w) (by rw [gen_pairs_length]; omega)
    rw [this, codes.1]
  have storeCode : program[start+2*w+1]? = some (.SD .x21 .x31 (BitVec.ofNat 12 (storeOffset k w))) := by
    have := code (2*w+1) (by rw [gen_pairs_length]; omega)
    rw [Nat.add_assoc, this, codes.2]
  have loadValid : memoryArgumentsValid state (.LD .x31 reg (BitVec.ofNat 12 (off+variantOffset v w))) = true := by
    simp only [memoryArgumentsValid, memAccess, loadAddress]
    exact QOpening.aligned_access _ (by omega) (by omega)
  have storeValid : memoryArgumentsValid loaded (.SD .x21 .x31 (BitVec.ofNat 12 (storeOffset k w))) = true := by
    simp only [memoryArgumentsValid, memAccess, storeAddress]
    exact QOpening.aligned_access _ (by omega) (by omega)
  have loadPC : loaded.pc = BitVec.ofNat 64 (4096+4*(start+2*w+1)) :=
    (straight_pc state _ rfl).trans (pc_next _ _ pc)
  have run₁ := runs_one state _ (start+2*w) loadCode pc rfl loadValid
  have run₂ := runs_one loaded _ (start+2*w+1) storeCode loadPC rfl storeValid
  have value : loaded.getReg .x31 = init.getMem (BitVec.ofNat 64 (source count)) := by
    simp only [loaded, execInstrBr, QOpening.getReg_setReg, MachineState.getReg_setPC]
    simp only [loadAddress, ite_true, ne_eq, reduceCtorEq, not_false_eq_true, and_self, named]
    exact inv.input _ (by omega) (by omega) (by omega)
  have memory : after.mem = (state.setMem (BitVec.ofNat 64 (proofBase+8*count))
      (init.getMem (BitVec.ofNat 64 (source count)))).mem := by
    show (execInstrBr loaded _).mem = _
    simp only [execInstrBr, storeAddress, value]
    rfl
  refine ⟨run₁.trans run₂, ?_, ?_, ?_⟩
  · exact (inv.store fits _ rfl).of_mem memory
  · show (execInstrBr loaded _).pc = _
    rw [straight_pc loaded _ rfl, straight_pc state _ rfl, BitVec.add_assoc]
    rfl
  · intro r other
    show (execInstrBr loaded _).getReg r = _
    simp [loaded, execInstrBr, QOpening.getReg_setReg, QOpening.getReg_setMem, Ne.symm other]

/-- The first `n ≤ 16` load/store pairs of a generalized copy block. -/
theorem gen_block (init : MachineState) (source : Nat → Nat) (reg : Reg) (start off k v S T D count : Nat)
    (r31 : reg ≠ .x31) (hk : k < 7)
    (code : CodeAt start (genPairs reg off k v 16))
    (addr : ∀ w < 16, BitVec.ofNat 64 S + signExtend12 (BitVec.ofNat 12 (off+variantOffset v w)) =
      BitVec.ofNat 64 (T+variantOffset v w))
    (aligned : T % 8 = 0) (low : trapdoorBase ≤ T)
    (high : T+160 ≤ proofBase) (target : D+storeOffset k 0 = proofBase+8*count)
    (fits : proofBase+8*(count+16) ≤ MEMORY_BYTES)
    (named : ∀ m < 16, source (count+m) = T+variantOffset v m) :
    ∀ n ≤ 16, ∀ state : MachineState, state.pc = BitVec.ofNat 64 (4096+4*start) →
      state.getReg reg = BitVec.ofNat 64 S → state.getReg .x21 = BitVec.ofNat 64 D →
      Inv init state source count →
      let after := (genPairs reg off k v n).foldl execInstrBr state
      Runs state after (2*n) (2*n) ∧ Inv init after source (count+n) ∧
        after.pc = BitVec.ofNat 64 (4096+4*(start+2*n)) ∧
        ∀ r, r ≠ .x31 → after.getReg r = state.getReg r := by
  intro n
  induction n with
  | zero =>
    intro _ state pc _ _ inv
    exact ⟨Runs.zero state, inv, pc, fun _ _ => rfl⟩
  | succ n ih =>
    intro le state pc from_ to_ inv
    obtain ⟨run, inv', pc', regs⟩ := ih (by omega) state pc from_ to_ inv
    let middle := (genPairs reg off k v n).foldl execInstrBr state
    have step := gen_pair_step init middle source reg start off k v n (count+n) S T D r31 hk (by omega) code
      (addr n (by omega)) pc' ((regs reg r31).trans from_) ((regs .x21 (by decide)).trans to_)
      (by unfold storeOffset at target ⊢; omega) aligned low high (by omega) (named n (by omega)) inv'
    obtain ⟨run₂, inv₂, pc₂, regs₂⟩ := step
    intro after
    have shape : after = execInstrBr (execInstrBr middle (.LD .x31 reg (BitVec.ofNat 12 (off+variantOffset v n))))
        (.SD .x21 .x31 (BitVec.ofNat 12 (storeOffset k n))) := by
      simp [after, middle, gen_pairs_succ, List.foldl_append]
    rw [shape]
    refine ⟨(run.trans run₂).cast (by omega) (by omega), by simpa [Nat.add_assoc] using inv₂, ?_, ?_⟩
    · rw [pc₂, pc', show (8 : Word) = BitVec.ofNat 64 8 from rfl, ← BitVec.ofNat_add]
      congr 1
    · intro r other
      exact (regs₂ r other).trans (regs r other)

/-! ### Pair head arithmetic -/

theorem divu_25 (n : Nat) (small : n < 2^40) :
    rv64_divu (BitVec.ofNat 64 n) (BitVec.ofNat 64 25) = BitVec.ofNat 64 (n/25) := by
  unfold rv64_divu
  rw [if_neg (by decide)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_udiv, word_lt n (by omega), word_lt 25 (by decide), word_lt _ (by omega)]

theorem remu_25 (n : Nat) (small : n < 2^40) :
    rv64_remu (BitVec.ofNat 64 n) (BitVec.ofNat 64 25) = BitVec.ofNat 64 (n%25) := by
  unfold rv64_remu
  rw [if_neg (by decide)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_umod, word_lt n (by omega), word_lt 25 (by decide), word_lt _ (by omega)]

theorem five_width (t : Nat) (small : t < 2^50) :
    (BitVec.ofNat 64 t <<< (2 : Nat)) + BitVec.ofNat 64 t = BitVec.ofNat 64 (5*t) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, word_lt _ (by omega), word_lt _ (by omega), Nat.shiftLeft_eq]
  omega

theorem shift_nine (r : Nat) (small : r < 2^40) :
    BitVec.ofNat 64 r <<< (9 : Nat) = BitVec.ofNat 64 (512*r) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, word_lt _ (by omega), word_lt _ (by omega), Nat.shiftLeft_eq]
  show r*2^9 % 2^64 = _
  omega

theorem prep_post (state : MachineState) (bk bk1 t : Reg) (n Bk Bk1 T : Nat) (small : n < 2^30)
    (bk7 : bk ≠ .x7) (bk25 : bk ≠ .x25) (bk6 : bk ≠ .x6) (bk10 : bk ≠ .x10) (bk11 : bk ≠ .x11)
    (bk17 : bk1 ≠ .x7) (bk125 : bk1 ≠ .x25) (bk16 : bk1 ≠ .x6) (bk110 : bk1 ≠ .x10)
    (t7 : t ≠ .x7) (t25 : t ≠ .x25) (t6 : t ≠ .x6) (t10 : t ≠ .x10) (t11 : t ≠ .x11) (t30 : t ≠ .x30)
    (node : state.getReg .x6 = BitVec.ofNat 64 n) (div : state.getReg .x26 = BitVec.ofNat 64 25)
    (width : state.getReg .x23 = BitVec.ofNat 64 368)
    (hbk : state.getReg bk = BitVec.ofNat 64 Bk) (hbk1 : state.getReg bk1 = BitVec.ofNat 64 Bk1)
    (ht : state.getReg t = BitVec.ofNat 64 T) (small' : Bk < 2^40) (small'' : Bk1 < 2^40) (smallT : T < 2^40) :
    let after := (prepWith bk bk1 t).foldl execInstrBr state
    after.getReg .x6 = BitVec.ofNat 64 (n/25) ∧ after.getReg .x25 = BitVec.ofNat 64 (n%25) ∧
      after.getReg .x11 = BitVec.ofNat 64 (Bk1+368*(n/25)) ∧
      after.getReg .x30 = BitVec.ofNat 64 (Bk+1840*(n/25)) ∧
      after.getReg .x7 = BitVec.ofNat 64 (512*(n%25)+T) ∧
      ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x10 → r ≠ .x11 → r ≠ .x25 → r ≠ .x30 → after.getReg r = state.getReg r := by
  intro after
  have quotient := divu_25 n (by omega)
  have remainder := remu_25 n (by omega)
  have w := mul_width (n/25) (by omega)
  have f := five_width (368*(n/25)) (by omega)
  have s9 := shift_nine (n%25) (by omega)
  have div' : state.getReg .x26 = BitVec.ofNat 64 25 := div
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [after, prepWith, execInstrBr, node, div', remainder, quotient]
  · simp [after, prepWith, execInstrBr, node, div', remainder]
  · simp [after, prepWith, execInstrBr, node, div', remainder, quotient, width, w, hbk1, bk110, Ne.symm bk110,
      bk16, Ne.symm bk16, bk125, Ne.symm bk125]
    rw [← BitVec.ofNat_add]; congr 1; omega
  · simp [after, prepWith, execInstrBr, node, div', remainder, quotient, width, w, hbk, f, bk10, Ne.symm bk10,
      bk6, Ne.symm bk6, bk25, Ne.symm bk25, bk7, Ne.symm bk7, bk11, Ne.symm bk11]
    rw [← BitVec.ofNat_add]; congr 1; omega
  · simp [after, prepWith, execInstrBr, node, div', remainder, quotient, width, w, ht, s9, t10, Ne.symm t10,
      t6, Ne.symm t6, t25, Ne.symm t25, t7, Ne.symm t7, t11, Ne.symm t11, t30, Ne.symm t30]
    rw [← BitVec.ofNat_add]
  · intro r a b c d e g
    simp [after, prepWith, execInstrBr, Ne.symm a, Ne.symm b, Ne.symm c, Ne.symm d, Ne.symm e, Ne.symm g]

/-! ### Code placement -/

theorem pair_prep_length (p : Nat) : (pairPrep p).length = 9 := by simp [pairPrep, prepWith]

theorem pair_head_codes (p : Nat) (hp : p < 2) :
    CodeAt (41+9*(2*p)) (pairPrep p) ∧ program[41+9*(2*p)+9]? = some (.JALR .x0 .x7 0) := by
  have block (i : Nat) (hi : i < 18) : program[41+9*(2*p)+i]? = (pairBlock p)[i]? := by
    rw [show 41+9*(2*p)+i = 41+18*p+i by omega]
    exact program_pair_block p i hp hi
  refine ⟨fun i hi => ?_, ?_⟩
  · rw [pair_prep_length] at hi
    rw [block i (by omega), pairBlock, pairHead, List.append_assoc, List.getElem?_append_left (by
      rw [pair_prep_length]; omega)]
  · rw [block 9 (by omega), pairBlock, pairHead, List.append_assoc, List.getElem?_append_right (by
      rw [pair_prep_length]), pair_prep_length]
    rfl

theorem program_pair_variant (p v i : Nat) (hp : p < 2) (hv : v < 25) (hi : i < 128) :
    program[pairStart p v + i]? = (pairVariantCode p v)[i]? := by
  rw [program_variants, List.getElem?_append_right (by rw [variants_head_length]; unfold pairStart; omega),
    variants_head_length, List.getElem?_append_right (by rw [variants_list_length]; unfold pairStart; omega),
    variants_list_length, pairTail, List.getElem?_append_right (by rw [List.length_replicate]; unfold pairStart; omega),
    List.length_replicate,
    show pairStart p v + i - 3072 - 2240 - 832 = 4096*p + (128*v + i) by unfold pairStart; omega]
  unfold pairsList
  rw [List.getElem?_append_left (by rw [chunk_length _ 4096 _ (fun p _ => pair_chunk_length p)]; simp; omega),
    chunk_get _ 4096 _ (fun p _ => pair_chunk_length p) p _ (by omega), List.getElem?_range hp, Option.bind_some,
    List.getElem?_append_left (by rw [chunk_length _ 128 _ (fun v _ => pair_variant_code_length p v)]; simp; omega),
    chunk_get _ 128 _ (fun v _ => pair_variant_code_length p v) v i hi, List.getElem?_range hv, Option.bind_some]

theorem pair_variant_codes (p v : Nat) (hp : p < 2) (hv : v < 25) :
    CodeAt (pairStart p v) (genPairs .x30 (368*(v/5)) (2*p) (v%5) 16) ∧
    CodeAt (pairStart p v+32) (genPairs .x11 0 (2*p+1) (v/5) 16) ∧
    program[pairExitWord p v]? = some (.JAL .x0 (backJump (pairExitWord p v) (41+9*(2*p+2)))) := by
  have l1 := gen_pairs_length .x30 (368*(v/5)) (2*p) (v%5) 16
  have l2 := gen_pairs_length .x11 0 (2*p+1) (v/5) 16
  have shape : pairVariantCode p v = genPairs .x30 (368*(v/5)) (2*p) (v%5) 16 ++
      (genPairs .x11 0 (2*p+1) (v/5) 16 ++ ([.JAL .x0 (backJump (pairExitWord p v) (41+9*(2*p+2)))] ++
        List.replicate 63 (.ADDI .x0 .x0 0))) := by
    simp only [pairVariantCode, List.append_assoc]
  refine ⟨fun i hi => ?_, fun i hi => ?_, ?_⟩
  · rw [l1] at hi
    rw [program_pair_variant p v i hp hv (by omega), shape, List.getElem?_append_left (by omega)]
  · rw [l2] at hi
    rw [Nat.add_assoc, program_pair_variant p v (32+i) hp hv (by omega), shape,
      List.getElem?_append_right (by omega), l1, Nat.add_sub_cancel_left, List.getElem?_append_left (by omega)]
  · unfold pairExitWord
    rw [program_pair_variant p v 64 hp hv (by omega), shape,
      List.getElem?_append_right (by omega), l1, List.getElem?_append_right (by omega), l2]
    rfl

set_option maxRecDepth 100000 in
theorem pair_dispatch_target : ∀ p < 3, ∀ v < 25,
    (BitVec.ofNat 64 (512*v+tableStart p) + signExtend12 0) &&& ~~~1#64 =
      BitVec.ofNat 64 (4096+4*pairStart p v) := by decide

set_option maxRecDepth 100000 in
theorem pair_exit_target : ∀ p < 3, ∀ v < 25,
    BitVec.ofNat 64 (4096+4*pairExitWord p v) + signExtend21 (backJump (pairExitWord p v) (41+9*(2*p+2))) =
      BitVec.ofNat 64 (4096+4*levelStart (2*p+2)) := by decide

theorem pair_regs (p : Nat) (hp : p < 3) :
    let bk := baseReg (2*p); let bk1 := baseReg (2*p+1); let t := tableReg p
    bk ≠ .x7 ∧ bk ≠ .x25 ∧ bk ≠ .x6 ∧ bk ≠ .x10 ∧ bk ≠ .x11 ∧
    bk1 ≠ .x7 ∧ bk1 ≠ .x25 ∧ bk1 ≠ .x6 ∧ bk1 ≠ .x10 ∧
    t ≠ .x7 ∧ t ≠ .x25 ∧ t ≠ .x6 ∧ t ≠ .x10 ∧ t ≠ .x11 ∧ t ≠ .x30 := by
  interval_cases p <;> decide

/-! ### One pair -/

def pairRun (p : Nat) (state : MachineState) : MachineState :=
  let s₁ := (pairPrep p).foldl execInstrBr state
  let s₂ := execInstrBr s₁ (.JALR .x0 .x7 0)
  let v := (s₁.getReg .x25).toNat
  let s₃ := (genPairs .x30 (368*(v/5)) (2*p) (v%5) 16).foldl execInstrBr s₂
  let s₄ := (genPairs .x11 0 (2*p+1) (v/5) 16).foldl execInstrBr s₃
  execInstrBr s₄ (.JAL .x0 (backJump (pairExitWord p v) (41+9*(2*p+2))))

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem pair_level_step (init state : MachineState) (positions : Positions) (o p : Nat) (hp : p < 2)
    (inside : ordinalIndex positions o < LENGTH) (ordinal : o < LENGTH)
    (at_ : LevelAt init state positions o (2*p)) :
    Runs state (pairRun p state) 75 84 ∧ LevelAt init (pairRun p state) positions o (2*p+2) ∧
      ∀ r, r ≠ .x27 → r ≠ .x6 → r ≠ .x7 → r ≠ .x10 → r ≠ .x11 → r ≠ .x21 → r ≠ .x24 → r ≠ .x25 →
        r ≠ .x30 → r ≠ .x31 → (pairRun p state).getReg r = state.getReg r := by
  let k := 2*p
  have hk : k < 7 := by omega
  let i := ordinalIndex positions o
  let n := i/5^k
  let v := n%25
  have hv : v < 25 := Nat.mod_lt _ (by decide)
  have small : n < 2^30 := by
    have := Nat.div_le_self i (5^k); have : i < 2^24 := inside; omega
  obtain ⟨c₁, c₂⟩ := pair_head_codes p hp
  obtain ⟨v₁, v₂, v₃⟩ := pair_variant_codes p v hp hv
  obtain ⟨a1, a2, a3, a4, a5, b1, b2, b3, b4, t1, t2, t3, t4, t5, t6⟩ := pair_regs p (by omega)
  have node : state.getReg .x6 = BitVec.ofNat 64 n := by
    have h := at_.node
    have e : nodeReg (2*p) = .x6 := by unfold nodeReg; rw [if_pos (by omega)]
    rwa [e] at h
  have div : state.getReg .x26 = BitVec.ofNat 64 25 := at_.tables 3 (by decide)
  have hT : state.getReg (tableReg p) = BitVec.ofNat 64 (tableStart p) := at_.tables p (by omega)
  have Bk := at_.bases (2*p) (by omega)
  have Bk1 := at_.bases (2*p+1) (by omega)
  have Tsmall : tableStart p < 2^40 := by interval_cases p <;> decide
  have room := group_room k (by omega)
  have room1 := group_room (k+1) (by omega)
  have bkSmall : ∀ j < 11, trapdoorBase+pentaGroupBase j+40 < 2^40 := by decide
  have hkp : k = 2*p := rfl
  have hn : n = i/5^k := rfl
  have hvn : v = n%25 := rfl
  have hTB : trapdoorBase = 4294971424 := rfl
  have hPB : proofBase = 10804535392 := rfl
  -- head
  let s₁ := (pairPrep p).foldl execInstrBr state
  have prepPure : (pairPrep p).all pureOp = true := by simp [pairPrep, prepWith, pureOp]
  have run₁ := runs_pure _ _ state c₁ at_.pc prepPure
  have post := prep_post state (baseReg (2*p)) (baseReg (2*p+1)) (tableReg p) n _ _ _ small
    a1 a2 a3 a4 a5 b1 b2 b3 b4 t1 t2 t3 t4 t5 t6 node div at_.width Bk Bk1 hT
    (bkSmall _ (by omega)) (bkSmall _ (by omega)) Tsmall
  obtain ⟨p6, p25, p11, p30, p7, pkeep⟩ := post
  replace p6 : s₁.getReg .x6 = _ := p6
  replace p25 : s₁.getReg .x25 = _ := p25
  replace p11 : s₁.getReg .x11 = _ := p11
  replace p30 : s₁.getReg .x30 = _ := p30
  replace p7 : s₁.getReg .x7 = _ := p7
  replace pkeep : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x10 → r ≠ .x11 → r ≠ .x25 → r ≠ .x30 →
      s₁.getReg r = state.getReg r := pkeep
  have pc₁ : s₁.pc = BitVec.ofNat 64 (4096+4*(41+9*(2*p)+9)) := by
    rw [pure_pc _ _ prepPure, at_.pc, pair_prep_length, pc_offset]
    rfl
  -- jump into the variant
  let s₂ := execInstrBr s₁ (.JALR .x0 .x7 0)
  have run₂ := runs_jalr s₁ .x0 .x7 _ c₂ pc₁
  obtain ⟨jpc₂, jmem₂, _, jkeep₂⟩ := jalr_post s₁ .x0 .x7
  have pc₂ : s₂.pc = BitVec.ofNat 64 (4096+4*pairStart p v) := by
    rw [jpc₂, p7]
    exact pair_dispatch_target p (by omega) v hv
  have keep₂ (r : Reg) : s₂.getReg r = s₁.getReg r := by
    by_cases z : r = .x0
    · subst z; rfl
    · exact jkeep₂ r z
  -- level 2p copy
  let G := trapdoorBase+pentaGroupBase k+40+1840*(n/25)
  let G1 := trapdoorBase+pentaGroupBase (k+1)+40+368*(n/25)
  have hG : G = trapdoorBase+pentaGroupBase k+40+1840*(n/25) := rfl
  have hG1 : G1 = trapdoorBase+pentaGroupBase (k+1)+40+368*(n/25) := rfl
  have count := div_lt_count i inside (k+2)
  have split2 : i/5^(k+2) = n/25 := by
    rw [show k+2 = k+1+1 by omega, pow_succ, pow_succ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul,
      Nat.div_div_eq_div_mul]
  have split1 : i/5^(k+1) = n/5 := by rw [pow_succ, Nat.div_div_eq_div_mul]
  rw [split2] at count
  have cnt1 : pentaCount (k+2) = (pentaCount (k+1)+4)/5 := rfl
  have cnt1' := div_lt_count i inside (k+1)
  rw [split1] at cnt1'
  have galign : (pentaGroupBase k+40) % 8 = 0 := by
    have : ∀ j < 11, (pentaGroupBase j+40) % 8 = 0 := by decide
    exact this k (by omega)
  have galign1 : (pentaGroupBase (k+1)+40) % 8 = 0 := by
    have : ∀ j < 11, (pentaGroupBase j+40) % 8 = 0 := by decide
    exact this (k+1) (by omega)
  have fitsAll : proofBase+8*(114*(o+1)) ≤ MEMORY_BYTES := by
    have : MEMORY_BYTES = 68719476736 := rfl
    have : LENGTH = 16777216 := rfl
    omega
  have notTop : levelDest o k = proofBase+8*(114*o) := by
    unfold levelDest; rw [if_neg (by omega)]; rfl
  have source0 (m : Nat) (hm : m < 16) :
      wordSource positions (levelWord o k+m) = G+368*(v/5)+variantOffset (v%5) m := by
    have level := word_source_level positions o k (m/4) (m%4) hk (by omega) (Nat.mod_lt _ (by decide))
    have neighbour := (neighbour_source i k (m/4) inside (by omega) (by omega)).1
    unfold levelWord
    rw [show 114*o+2+16*k+m = 114*o+2+16*k+4*(m/4)+m%4 by omega, level, neighbour]
    unfold variantOffset
    rw [hG, hvn, ← hn]
    omega
  have source1 (m : Nat) (hm : m < 16) :
      wordSource positions (levelWord o k+16+m) = G1+0+variantOffset (v/5) m := by
    have level := word_source_level positions o (k+1) (m/4) (m%4) (by omega) (by omega) (Nat.mod_lt _ (by decide))
    have neighbour := (neighbour_source i (k+1) (m/4) inside (by omega) (by omega)).1
    unfold levelWord
    rw [show 114*o+2+16*k+16+m = 114*o+2+16*(k+1)+4*(m/4)+m%4 by omega, level, neighbour, split1]
    unfold variantOffset
    rw [hG1, hvn]
    omega
  have x30₂ : s₂.getReg .x30 = BitVec.ofNat 64 G := by
    rw [keep₂, p30]
  have x11₂ : s₂.getReg .x11 = BitVec.ofNat 64 G1 := by
    rw [keep₂, p11]
  have x21₂ : s₂.getReg .x21 = BitVec.ofNat 64 (proofBase+8*(114*o)) := by
    rw [keep₂, pkeep .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), at_.dest, notTop]
  have inv₂ : Inv init s₂ (wordSource positions) (levelWord o k) := by
    refine (at_.inv.of_mem (pure_mem _ _ prepPure)).of_mem ?_
    rw [jmem₂]
  have r1 : v/5 < 5 := by omega
  have r0 : v%5 < 5 := Nat.mod_lt _ (by decide)
  obtain ⟨run₃, inv₃, pc₃, regs₃⟩ := gen_block init (wordSource positions) .x30 (pairStart p v) (368*(v/5)) k (v%5)
    G (G+368*(v/5)) (proofBase+8*(114*o)) (levelWord o k) (by decide) hk v₁
    (fun w hw => by rw [addr_small _ _ (gen_offset_value _ r1 _ r0 w hw), ← Nat.add_assoc])
    (by rw [hG]; omega) (by rw [hG]; omega)
    (by rw [hG, hvn]; omega) (by unfold storeOffset levelWord; omega) (by unfold levelWord; omega) source0
    16 le_rfl s₂ pc₂ x30₂ x21₂ inv₂
  let s₃ := (genPairs .x30 (368*(v/5)) k (v%5) 16).foldl execInstrBr s₂
  -- level 2p+1 copy
  have offv1 : ∀ w < 16, signExtend12 (BitVec.ofNat 12 (0+variantOffset (v/5) w)) =
      BitVec.ofNat 64 (0+variantOffset (v/5) w) := by
    intro w hw
    have := gen_offset_value 0 (by decide) (v/5) r1 w hw
    rwa [Nat.mul_zero] at this
  have fits1 : proofBase+8*(levelWord o k+16+16) ≤ MEMORY_BYTES := by
    have e : levelWord o k+16+16 = 114*o+2+16*k+32 := by unfold levelWord; omega
    rw [e]; omega
  obtain ⟨run₄, inv₄, pc₄, regs₄⟩ := gen_block init (wordSource positions) .x11 (pairStart p v+32) 0 (k+1) (v/5)
    G1 (G1+0) (proofBase+8*(114*o)) (levelWord o k+16) (by decide) (by omega) v₂
    (fun w hw => by rw [addr_small _ _ (offv1 w hw), ← Nat.add_assoc])
    (by rw [hG1]; omega) (by rw [hG1]; omega)
    (by rw [hG1]; omega) (by unfold storeOffset levelWord; omega) fits1 source1
    16 le_rfl s₃ (by rw [pc₃]) ((regs₃ .x11 (by decide)).trans x11₂) ((regs₃ .x21 (by decide)).trans x21₂)
    (inv₃.cast_count rfl)
  let s₄ := (genPairs .x11 0 (k+1) (v/5) 16).foldl execInstrBr s₃
  -- jump to the next level
  have run₅ := runs_jal s₄ _ _ v₃ (by rw [pc₄]; unfold pairExitWord; rfl)
  let s₅ := execInstrBr s₄ (.JAL .x0 (backJump (pairExitWord p v) (41+9*(2*p+2))))
  obtain ⟨jpc₅, jmem₅, jkeep₅⟩ := jal_post s₄ (backJump (pairExitWord p v) (41+9*(2*p+2)))
  have x25e : ((pairPrep p).foldl execInstrBr state).getReg .x25 = BitVec.ofNat 64 v := p25
  have shape : pairRun p state = s₅ := by
    simp only [pairRun, x25e, word_lt v (by omega)]
    rfl
  have keepAll (r : Reg) (a : r ≠ .x6) (b : r ≠ .x7) (c : r ≠ .x10) (d : r ≠ .x11) (e : r ≠ .x25)
      (f : r ≠ .x30) (g : r ≠ .x31) : (pairRun p state).getReg r = state.getReg r := by
    rw [shape, jkeep₅, regs₄ r g, regs₃ r g, keep₂, pkeep r a b c d e f]
  refine ⟨?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [shape]
    exact (run₁.trans (run₂.trans (run₃.trans (run₄.trans run₅)))).cast
      (by simp [pair_prep_length])
      (by simp [cost, pairPrep, prepWith, instructionCycles])
  · rw [shape, jpc₅, pc₄]
    have := pair_exit_target p (by omega) v hv
    unfold pairExitWord at this ⊢
    rw [show 4096+4*(pairStart p v+32+2*16) = 4096+4*(pairStart p v+64) by omega, this]
  · rw [shape, jkeep₅, regs₄ _ (by unfold nodeReg; split <;> decide), regs₃ _ (by unfold nodeReg; split <;> decide),
      keep₂]
    have e : nodeReg (2*p+2) = .x6 := by unfold nodeReg; rw [if_pos (by omega)]
    rw [e, p6]
    congr 1
    exact split2.symm
  · rw [shape, jkeep₅, regs₄ .x21 (by decide), regs₃ .x21 (by decide), x21₂]
    unfold levelDest
    rw [if_neg (by omega)]; rfl
  · exact (keepAll .x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      at_.heap
  · exact (keepAll .x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      at_.five
  · exact (keepAll .x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      at_.width
  · intro j hj
    obtain ⟨_, _, a, b, _, c, d, _, _, _, e, f, g⟩ := base_reg_frame j
    exact (keepAll (baseReg j) a b c d e f g).trans (at_.bases j hj)
  · intro j hj
    obtain ⟨_, _, a, b, _, c, d, _, _, _, e, f, g⟩ := table_reg_frame j
    exact (keepAll (tableReg j) a b c d e f g).trans (at_.tables j hj)
  · rw [shape]
    have mem : s₅.mem = s₄.mem := jmem₅
    exact (inv₄.of_mem mem).cast_count (by unfold levelWord; omega)
  · intro r _ a b c d _ _ e f g
    exact keepAll r a b c d e f g

end TwoPermutationPrototype.QuadOpening
