import CommitGolfCandidate.NonceExpandHalves

/-! The guards of the expansion (words 445..466). They reject odd lengths, lengths below
`560 * count`, footers that are not whole 32-byte fields and expanded lengths above the proof
capacity, before any proof byte is read or written. On an accepted proof they set up the copy
pointers. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The proof capacity of the checker. -/
abbrev nonceExpandCapacity : Nat := 13421772800

/-- Footer fields of a delivered proof of `length` bytes with `count` records. -/
def nonceExpandFooter (count length : Nat) : Nat := (length - 560 * count) / 32

/-- Length of the expanded proof. -/
def nonceExpandLength (count length : Nat) : Nat := 576 * count + 32 * nonceExpandFooter count length

/-- The guards accept exactly these lengths. -/
def NonceExpandAccepts (count length : Nat) : Prop :=
  560 * count ≤ length ∧ (length - 560 * count) % 32 = 0 ∧
    nonceExpandLength count length ≤ nonceExpandCapacity

instance (count length : Nat) : Decidable (NonceExpandAccepts count length) := by
  unfold NonceExpandAccepts; infer_instance

/-- Facts about the state at the first expansion word. -/
structure NonceExpandEntry (start : MachineState) (base count length indices : Nat) : Prop where
  pc : start.pc = BitVec.ofNat 64 (4096 + 4 * 445)
  proofReg : start.getReg .x15 = BitVec.ofNat 64 base
  countReg : start.getReg .x16 = BitVec.ofNat 64 count
  lengthReg : start.getReg .x17 = BitVec.ofNat 64 length
  indicesReg : start.getReg .x13 = BitVec.ofNat 64 indices
  lengthBound : length ≤ nonceExpandCapacity
  countBound : count ≤ 2 ^ 24
  window : base + nonceExpandCapacity ≤ MEMORY_BYTES
  aligned : base % 8 = 0
  indicesAligned : indices % 8 = 0
  indicesBelow : indices + 8 * count ≤ base

/-- The guards, from the first expansion word. On an accepted length they reach word 467 with
the copy pointers set; otherwise the reject sequence at word 178. -/
theorem nonce_expand_guards (start : MachineState) (base count length indices : Nat)
    (entry : NonceExpandEntry start base count length indices) :
    ∃ next regs steps, steps ≤ 22 ∧ NonceExpandRuns start steps next ∧
      NonceAt next (if NonceExpandAccepts count length then 467 else 178) regs ∧
      (NonceExpandAccepts count length → steps = 22 ∧ next.mem = start.mem ∧
        regs .x26 = start.getReg .x11 ∧
        regs .x18 = BitVec.ofNat 64 (nonceExpandLength count length) ∧
        regs .x23 = BitVec.ofNat 64 (base + length) ∧
        regs .x25 = BitVec.ofNat 64 (base + nonceExpandLength count length) ∧
        regs .x24 = BitVec.ofNat 64 count ∧
        regs .x29 = BitVec.ofNat 64 (nonceExpandFooter count length) ∧
        regs .x28 = BitVec.ofNat 64 (nonceExpandFooter count length) ∧
        (∀ reg, reg ∉ [Reg.x6, .x7, .x18, .x19, .x23, .x24, .x25, .x26, .x28, .x29, .x30] →
          regs reg = start.getReg reg)) := by
  have memoryBound : MEMORY_BYTES = 2 ^ 36 := rfl
  have lengthBound := entry.lengthBound
  have countBound := entry.countBound
  have window := entry.window
  have here : NonceAt start 445 start.getReg := ⟨entry.pc, fun _ => rfl⟩
  have zero := nonce_reg_zero here
  -- 445, 446, 447: parity
  obtain ⟨run1, at1⟩ := nonce_step_addi here .x26 .x11 0 (by decide) (by omega) (by omega) rfl
  obtain ⟨r1, at1, v1, f1⟩ := at1.fresh
  obtain ⟨run2, at2⟩ := nonce_step_andi at1 .x6 .x17 1 (by decide) (by omega) (by omega) rfl
  obtain ⟨r2, at2, v2, f2⟩ := at2.fresh
  have v2' : r2 .x6 = BitVec.ofNat 64 (length % 2) := by
    rw [v2, f1 _ (by decide), entry.lengthReg]
    apply nonce_word_of_toNat
    rw [BitVec.toNat_and, nonce_toNat_ofNat _ (by omega), show (signExtend12 1).toNat = 1 from rfl,
      Nat.and_one_is_mod]
  have z2 : r2 .x0 = 0 := nonce_reg_zero at2
  obtain ⟨run3, at3⟩ := nonce_step_bne at2 .x6 .x0 7116 178 (by omega) (by omega) rfl (by decide)
  rw [v2', z2] at at3
  by_cases odd : length % 2 = 1
  · have rejected : ¬NonceExpandAccepts count length := by
      unfold NonceExpandAccepts nonceExpandLength nonceExpandFooter; omega
    rw [if_neg (fun same => by have := (nonce_ofNat_eq_zero _ (by omega)).mp same; omega)] at at3
    refine ⟨_, r2, 3, by norm_num, (run1.trans (run2.trans run3)).cast rfl, ?_,
      fun accepted => absurd accepted rejected⟩
    rwa [if_neg rejected]
  rw [if_pos ((nonce_ofNat_eq_zero _ (by omega)).mpr (by omega))] at at3
  -- 448, 449, 450: minimum
  obtain ⟨run4, at4⟩ := nonce_step_addi at3 .x29 .x0 560 (by decide) (by omega) (by omega) rfl
  obtain ⟨r4, at4, v4, f4⟩ := at4.fresh
  obtain ⟨run5, at5⟩ := nonce_step_mul at4 .x6 .x16 .x29 (by decide) (by omega) (by omega) rfl
  obtain ⟨r5, at5, v5, f5⟩ := at5.fresh
  have v5' : r5 .x6 = BitVec.ofNat 64 (560 * count) := by
    rw [v5, f4 _ (by decide), f2 _ (by decide), f1 _ (by decide), entry.countReg, v4, z2]
    apply nonce_word_of_toNat
    rw [BitVec.toNat_mul, nonce_toNat_ofNat _ (by omega)]
    have : (0 + signExtend12 560 : Word).toNat = 560 := rfl
    rw [this]
    omega
  have l5 : r5 .x17 = BitVec.ofNat 64 length := by
    rw [f5 _ (by decide), f4 _ (by decide), f2 _ (by decide), f1 _ (by decide), entry.lengthReg]
  obtain ⟨run6, at6⟩ := nonce_step_bltu at5 .x17 .x6 7104 178 (by omega) (by omega) rfl (by decide)
  rw [l5, v5', nonce_toNat_ofNat _ (by omega), nonce_toNat_ofNat _ (by omega)] at at6
  by_cases short : length < 560 * count
  · have rejected : ¬NonceExpandAccepts count length := by
      unfold NonceExpandAccepts; omega
    rw [if_pos short] at at6
    refine ⟨_, r5, 6, by norm_num, (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans run6))))).cast rfl,
      ?_, fun accepted => absurd accepted rejected⟩
    rwa [if_neg rejected]
  rw [if_neg short] at at6
  -- 451, 452, 453, 454: whole footer fields
  obtain ⟨run7, at7⟩ := nonce_step_sub at6 .x28 .x17 .x6 (by decide) (by omega) (by omega) rfl
  obtain ⟨r7, at7, v7, f7⟩ := at7.fresh
  have v7' : r7 .x28 = BitVec.ofNat 64 (length - 560 * count) := by
    rw [v7, l5, v5']
    apply nonce_word_of_toNat
    rw [BitVec.toNat_sub, nonce_toNat_ofNat _ (by omega), nonce_toNat_ofNat _ (by omega)]
    omega
  obtain ⟨run8, at8⟩ := nonce_step_addi at7 .x7 .x0 32 (by decide) (by omega) (by omega) rfl
  obtain ⟨r8, at8, v8, f8⟩ := at8.fresh
  have v8' : r8 .x7 = BitVec.ofNat 64 32 := by
    rw [v8, f7 _ (by decide), f5 _ (by decide), f4 _ (by decide), z2]; rfl
  obtain ⟨run9, at9⟩ := nonce_step_remu at8 .x30 .x28 .x7 (by decide) (by omega) (by omega) rfl
  obtain ⟨r9, at9, v9, f9⟩ := at9.fresh
  have v9' : r9 .x30 = BitVec.ofNat 64 ((length - 560 * count) % 32) := by
    rw [v9, f8 _ (by decide), v7', v8', rv64_remu, if_neg (by decide)]
    apply nonce_word_of_toNat
    rw [BitVec.toNat_umod, nonce_toNat_ofNat _ (by omega), nonce_toNat_ofNat _ (by omega)]
  have z9 : r9 .x0 = 0 := nonce_reg_zero at9
  obtain ⟨run10, at10⟩ := nonce_step_bne at9 .x30 .x0 7088 178 (by omega) (by omega) rfl (by decide)
  rw [v9', z9] at at10
  by_cases ragged : (length - 560 * count) % 32 ≠ 0
  · have rejected : ¬NonceExpandAccepts count length := by
      unfold NonceExpandAccepts; omega
    rw [if_neg (fun same => ragged ((nonce_ofNat_eq_zero _ (by omega)).mp same))] at at10
    refine ⟨_, r9, 10, by norm_num, (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans
      (run7.trans (run8.trans (run9.trans run10))))))))).cast rfl, ?_,
      fun accepted => absurd accepted rejected⟩
    rwa [if_neg rejected]
  rw [if_pos ((nonce_ofNat_eq_zero _ (by omega)).mpr (by omega))] at at10
  -- 455..462: expanded length and capacity
  obtain ⟨run11, at11⟩ := nonce_step_divu at10 .x28 .x28 .x7 (by decide) (by omega) (by omega) rfl
  obtain ⟨r11, at11, v11, f11⟩ := at11.fresh
  have v11' : r11 .x28 = BitVec.ofNat 64 (nonceExpandFooter count length) := by
    rw [v11, f9 _ (by decide), f8 _ (by decide), v7', f9 _ (by decide), v8', rv64_divu, if_neg (by decide)]
    apply nonce_word_of_toNat
    rw [BitVec.toNat_udiv, nonce_toNat_ofNat _ (by omega), nonce_toNat_ofNat _ (by omega)]
    rfl
  obtain ⟨run12, at12⟩ := nonce_step_addi at11 .x29 .x0 576 (by decide) (by omega) (by omega) rfl
  obtain ⟨r12, at12, v12, f12⟩ := at12.fresh
  obtain ⟨run13, at13⟩ := nonce_step_mul at12 .x18 .x16 .x29 (by decide) (by omega) (by omega) rfl
  obtain ⟨r13, at13, v13, f13⟩ := at13.fresh
  have c12 : r12 .x16 = BitVec.ofNat 64 count := by
    rw [f12 _ (by decide), f11 _ (by decide), f9 _ (by decide), f8 _ (by decide), f7 _ (by decide),
      f5 _ (by decide), f4 _ (by decide), f2 _ (by decide), f1 _ (by decide), entry.countReg]
  have v13' : r13 .x18 = BitVec.ofNat 64 (576 * count) := by
    rw [v13, c12, v12, f11 _ (by decide), z9]
    apply nonce_word_of_toNat
    rw [BitVec.toNat_mul, nonce_toNat_ofNat _ (by omega)]
    have : (0 + signExtend12 576 : Word).toNat = 576 := rfl
    rw [this]
    omega
  obtain ⟨run14, at14⟩ := nonce_step_slli at13 .x7 .x28 5 (by decide) (by omega) (by omega) rfl
  obtain ⟨r14, at14, v14, f14⟩ := at14.fresh
  have footerBound : nonceExpandFooter count length ≤ length := by
    unfold nonceExpandFooter; omega
  have v14' : r14 .x7 = BitVec.ofNat 64 (32 * nonceExpandFooter count length) := by
    rw [v14, f13 _ (by decide), f12 _ (by decide), v11']
    apply nonce_word_of_toNat
    rw [BitVec.toNat_shiftLeft, nonce_toNat_ofNat _ (by omega), Nat.shiftLeft_eq]
    have : (5 : BitVec 6).toNat = 5 := rfl
    rw [this]
    omega
  obtain ⟨run15, at15⟩ := nonce_step_add at14 .x18 .x18 .x7 (by decide) (by omega) (by omega) rfl
  obtain ⟨r15, at15, v15, f15⟩ := at15.fresh
  have v15' : r15 .x18 = BitVec.ofNat 64 (nonceExpandLength count length) := by
    rw [v15, f14 _ (by decide), v13', v14', ← BitVec.ofNat_add]
    rfl
  obtain ⟨run16, at16⟩ := nonce_step_addi at15 .x19 .x0 25 (by decide) (by omega) (by omega) rfl
  obtain ⟨r16, at16, v16, f16⟩ := at16.fresh
  obtain ⟨run17, at17⟩ := nonce_step_slli at16 .x19 .x19 29 (by decide) (by omega) (by omega) rfl
  obtain ⟨r17, at17, v17, f17⟩ := at17.fresh
  have v17' : r17 .x19 = BitVec.ofNat 64 nonceExpandCapacity := by
    rw [v17, v16, f15 _ (by decide), f14 _ (by decide), f13 _ (by decide), f12 _ (by decide),
      f11 _ (by decide), z9]
    decide
  have e17 : r17 .x18 = BitVec.ofNat 64 (nonceExpandLength count length) := by
    rw [f17 _ (by decide), f16 _ (by decide), v15']
  have lengthSmall : nonceExpandLength count length < 2 ^ 64 := by
    unfold nonceExpandLength; omega
  obtain ⟨run18, at18⟩ := nonce_step_bltu at17 .x19 .x18 7056 178 (by omega) (by omega) rfl (by decide)
  rw [v17', e17, nonce_toNat_ofNat _ (by omega), nonce_toNat_ofNat _ lengthSmall] at at18
  by_cases large : nonceExpandCapacity < nonceExpandLength count length
  · have rejected : ¬NonceExpandAccepts count length := by
      unfold NonceExpandAccepts; omega
    rw [if_pos large] at at18
    refine ⟨_, r17, 18, by norm_num, (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans
      (run7.trans (run8.trans (run9.trans (run10.trans (run11.trans (run12.trans (run13.trans
      (run14.trans (run15.trans (run16.trans (run17.trans run18))))))))))))))))).cast rfl, ?_,
      fun accepted => absurd accepted rejected⟩
    rwa [if_neg rejected]
  rw [if_neg large] at at18
  have accepted : NonceExpandAccepts count length := by
    unfold NonceExpandAccepts; omega
  -- 463..466: pointers
  obtain ⟨run19, at19⟩ := nonce_step_add at18 .x23 .x15 .x17 (by decide) (by omega) (by omega) rfl
  obtain ⟨r19, at19, v19, f19⟩ := at19.fresh
  obtain ⟨run20, at20⟩ := nonce_step_add at19 .x25 .x15 .x18 (by decide) (by omega) (by omega) rfl
  obtain ⟨r20, at20, v20, f20⟩ := at20.fresh
  obtain ⟨run21, at21⟩ := nonce_step_addi at20 .x24 .x16 0 (by decide) (by omega) (by omega) rfl
  obtain ⟨r21, at21, v21, f21⟩ := at21.fresh
  obtain ⟨run22, at22⟩ := nonce_step_addi at21 .x29 .x28 0 (by decide) (by omega) (by omega) rfl
  obtain ⟨r22, at22, v22, f22⟩ := at22.fresh
  have p17 : r17 .x15 = BitVec.ofNat 64 base := by
    rw [f17 _ (by decide), f16 _ (by decide), f15 _ (by decide), f14 _ (by decide), f13 _ (by decide),
      f12 _ (by decide), f11 _ (by decide), f9 _ (by decide), f8 _ (by decide), f7 _ (by decide),
      f5 _ (by decide), f4 _ (by decide), f2 _ (by decide), f1 _ (by decide), entry.proofReg]
  have l17 : r17 .x17 = BitVec.ofNat 64 length := by
    rw [f17 _ (by decide), f16 _ (by decide), f15 _ (by decide), f14 _ (by decide), f13 _ (by decide),
      f12 _ (by decide), f11 _ (by decide), f9 _ (by decide), f8 _ (by decide), f7 _ (by decide), l5]
  refine ⟨_, r22, 22, by norm_num, (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans
      (run7.trans (run8.trans (run9.trans (run10.trans (run11.trans (run12.trans (run13.trans
      (run14.trans (run15.trans (run16.trans (run17.trans (run18.trans (run19.trans (run20.trans
      (run21.trans run22))))))))))))))))))))).cast rfl, by rwa [if_pos accepted],
    fun _ => ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact (nonce_addi_mem _ _ _ _).trans <| (nonce_addi_mem _ _ _ _).trans <| (nonce_add_mem _ _ _ _).trans <|
      (nonce_add_mem _ _ _ _).trans <| (nonce_bltu_mem _ _ _ _).trans <| (nonce_slli_mem _ _ _ _).trans <|
      (nonce_addi_mem _ _ _ _).trans <| (nonce_add_mem _ _ _ _).trans <| (nonce_slli_mem _ _ _ _).trans <|
      (nonce_mul_mem _ _ _ _).trans <| (nonce_addi_mem _ _ _ _).trans <| (nonce_divu_mem _ _ _ _).trans <|
      (nonce_bne_mem _ _ _ _).trans <| (nonce_remu_mem _ _ _ _).trans <| (nonce_addi_mem _ _ _ _).trans <|
      (nonce_sub_mem _ _ _ _).trans <| (nonce_bltu_mem _ _ _ _).trans <| (nonce_mul_mem _ _ _ _).trans <|
      (nonce_addi_mem _ _ _ _).trans <| (nonce_bne_mem _ _ _ _).trans <| (nonce_andi_mem _ _ _ _).trans <|
      (nonce_addi_mem _ _ _ _)
  · rw [f22 _ (by decide), f21 _ (by decide), f20 _ (by decide), f19 _ (by decide), f17 _ (by decide),
      f16 _ (by decide), f15 _ (by decide), f14 _ (by decide), f13 _ (by decide), f12 _ (by decide),
      f11 _ (by decide), f9 _ (by decide), f8 _ (by decide), f7 _ (by decide), f5 _ (by decide),
      f4 _ (by decide), f2 _ (by decide), v1, nonce_add_zero]
  · rw [f22 _ (by decide), f21 _ (by decide), f20 _ (by decide), f19 _ (by decide), e17]
  · rw [f22 _ (by decide), f21 _ (by decide), f20 _ (by decide), v19, p17, l17, ← BitVec.ofNat_add]
  · rw [f22 _ (by decide), f21 _ (by decide), v20, f19 .x15 (by decide), f19 .x18 (by decide), p17, e17,
      ← BitVec.ofNat_add]
  · rw [f22 _ (by decide), v21, f20 _ (by decide), f19 _ (by decide), f17 _ (by decide), f16 _ (by decide),
      f15 _ (by decide), f14 _ (by decide), f13 _ (by decide), c12, nonce_add_zero]
  · rw [v22, f21 _ (by decide), f20 _ (by decide), f19 _ (by decide), f17 _ (by decide), f16 _ (by decide),
      f15 _ (by decide), f14 _ (by decide), f13 _ (by decide), f12 _ (by decide), v11', nonce_add_zero]
  · rw [f22 _ (by decide), f21 _ (by decide), f20 _ (by decide), f19 _ (by decide), f17 _ (by decide),
      f16 _ (by decide), f15 _ (by decide), f14 _ (by decide), f13 _ (by decide), f12 _ (by decide), v11']
  · intro reg outside
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
    obtain ⟨n6, n7, n18, n19, n23, n24, n25, n26, n28, n29, n30⟩ := outside
    rw [f22 _ n29, f21 _ n24, f20 _ n25, f19 _ n23, f17 _ n19, f16 _ n19, f15 _ n18, f14 _ n7, f13 _ n18,
      f12 _ n29, f11 _ n28, f9 _ n30, f8 _ n7, f7 _ n28, f5 _ n6, f4 _ n29, f2 _ n6, f1 _ n26]

end CommitGolfCandidate
