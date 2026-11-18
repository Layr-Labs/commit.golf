import CommitGolfCandidate.NonceExpandFooterLoop

/-! One record of the expansion (words 472..491): the 534-byte record at `fields` becomes the
576-byte record at `nodes`: 13 nodes, 128 copied bytes, eight zero bytes, the tag of the
record's position, read from the position buffer, and the 16-byte nonce. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The expanded record at `nodes` of the delivered record at `fields`, whose position word is
`position`. -/
structure NonceRecordTarget (start : MachineState) (target : Nat → Byte) (fields nodes position : Nat) :
    Prop where
  siblings : NonceFooterTarget start target (fields + 144) (nodes + 160) 13
  middle : ∀ m < 128, target (nodes + 32 + m) = start.getByte (BitVec.ofNat 64 (fields + 16 + m))
  zeros : ∀ m < 8, target (nodes + 24 + m) = 0
  tag : ∀ m < 8, target (nodes + 16 + m) = extractByte (BitVec.ofNat 64 (4072 + 256 * position)) m
  nonce : ∀ m < 16, target (nodes + m) = start.getByte (BitVec.ofNat 64 (fields + m))

/-- The sibling loop (words 473..475), as the footer loop. -/
theorem nonce_sibling_loop (start : MachineState) (target : Nat → Byte) (fields nodes high : Nat)
    (facts : NonceFooterTarget start target fields nodes 13)
    (order : fields ≤ nodes) (evenFields : fields % 2 = 0) (evenNodes : nodes % 2 = 0)
    (within : nodes + 32 * 13 ≤ high) (range : high ≤ MEMORY_BYTES) :
    ∀ s < 13, ∀ (state : MachineState) (regs : Reg → Word), NonceAt state 473 regs →
      regs .x29 = BitVec.ofNat 64 (s + 1) → regs .x23 = BitVec.ofNat 64 (fields + 30 * (s + 1)) →
      regs .x25 = BitVec.ofNat 64 (nodes + 32 * (s + 1)) →
      NonceExpandMem start state (nodes + 32 * (s + 1)) high target →
      ∃ next later, NonceExpandRuns state (37 * (s + 1)) next ∧ NonceAt next 476 later ∧
        later .x23 = BitVec.ofNat 64 fields ∧ later .x25 = BitVec.ofNat 64 nodes ∧
        (∀ reg, reg ∉ [Reg.x1, .x6, .x23, .x25, .x29] → later reg = regs reg) ∧
        NonceExpandMem start next nodes high target := by
  have memoryBound : MEMORY_BYTES < 2 ^ 64 := by decide
  have step : ∀ s < 13, ∀ (state : MachineState) (regs : Reg → Word), NonceAt state 473 regs →
      regs .x29 = BitVec.ofNat 64 (s + 1) → regs .x23 = BitVec.ofNat 64 (fields + 30 * (s + 1)) →
      regs .x25 = BitVec.ofNat 64 (nodes + 32 * (s + 1)) →
      NonceExpandMem start state (nodes + 32 * (s + 1)) high target →
      ∃ next later, NonceExpandRuns state 37 next ∧ NonceAt next (if s = 0 then 476 else 473) later ∧
        later .x29 = BitVec.ofNat 64 s ∧
        later .x23 = BitVec.ofNat 64 (fields + 30 * s) ∧ later .x25 = BitVec.ofNat 64 (nodes + 32 * s) ∧
        (∀ reg, reg ∉ [Reg.x1, .x6, .x23, .x25, .x29] → later reg = regs reg) ∧
        NonceExpandMem start next (nodes + 32 * s) high target := by
    intro s bounded state regs here counter source dest mem
    obtain ⟨run1, at1⟩ := nonce_step_jal here .x1 156 512 (by omega) (by omega) rfl (by decide)
    rw [if_neg (by decide)] at at1
    obtain ⟨r1, at1, v1, f1⟩ := at1.fresh
    have mem1 : NonceExpandMem start (execInstrBr state (.JAL .x1 156)) (nodes + 32 * s + 32) high target := by
      have m := mem.same_mem (nonce_jal_mem state .x1 156)
      rwa [show nodes + 32 * (s + 1) = nodes + 32 * s + 32 by ring] at m
    obtain ⟨next2, r2, run2, at2, source2, dest2, frame2, mem2⟩ :=
      nonce_expand_node start _ r1 (fields + 30 * s) (nodes + 32 * s) high 474 target at1
        (by rw [f1 _ (by decide), source]; congr 1 <;> ring)
        (by rw [f1 _ (by decide), dest]; congr 1 <;> ring) v1 (by omega) (by decide) mem1
        (by omega) (by omega) (by omega) (by omega) range
        (fun o inside => facts.copies s bounded o inside) (facts.zeros s bounded)
    obtain ⟨run3, at3⟩ := nonce_step_addi at2 .x29 .x29 4095 (by decide) (by omega) (by omega) rfl
    obtain ⟨r3, at3, v3, f3⟩ := at3.fresh
    have counter3 : r3 .x29 = BitVec.ofNat 64 s := by
      rw [v3, frame2 _ (by decide) (by decide) (by decide), f1 _ (by decide), counter,
        nonce_address_sub _ 1 _ (by decide) (by omega) (by omega) (by omega)]
      congr 1
    have zero3 := nonce_reg_zero at3
    obtain ⟨run4, at4⟩ := nonce_step_bne at3 .x29 .x0 8184 473 (by omega) (by omega) rfl (by decide)
    have test : (r3 .x29 = r3 .x0) ↔ s = 0 := by
      rw [counter3, zero3]
      exact nonce_ofNat_eq_zero s (by omega)
    refine ⟨_, r3, (run1.trans (run2.trans (run3.trans run4))).cast (by omega), ?_, counter3,
      by rw [f3 _ (by decide), source2], by rw [f3 _ (by decide), dest2], ?_,
      (mem2.same_mem (nonce_addi_mem _ .x29 .x29 4095)).same_mem (nonce_bne_mem _ .x29 .x0 8184)⟩
    · by_cases empty : s = 0
      · simpa only [if_pos (test.mpr empty), if_pos empty] using at4
      · simpa only [if_neg (fun same => empty (test.mp same)), if_neg empty] using at4
    · intro reg outside
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
      obtain ⟨n1, n6, n23, n25, n29⟩ := outside
      rw [f3 _ n29, frame2 _ n6 n23 n25, f1 _ n1]
  intro s
  induction s with
  | zero =>
    intro bounded state regs here counter source dest mem
    obtain ⟨next, later, run, final, _, source', dest', frame, mem'⟩ :=
      step 0 bounded state regs here counter source dest mem
    exact ⟨next, later, run.cast rfl, by simpa using final, by simpa using source', by simpa using dest',
      frame, by simpa using mem'⟩
  | succ s ih =>
    intro bounded state regs here counter source dest mem
    obtain ⟨next, later, run, final, counter', source', dest', frame, mem'⟩ :=
      step (s + 1) bounded state regs here counter source dest mem
    rw [if_neg (by omega)] at final
    obtain ⟨last, regsLast, run', final', sourceLast, destLast, frame', memLast⟩ :=
      ih (by omega) next later final counter' source' dest' mem'
    refine ⟨last, regsLast, (run.trans run').cast (by ring), final', sourceLast, destLast, ?_, memLast⟩
    intro reg outside
    rw [frame' reg outside, frame reg outside]

theorem nonce_tag_word (position : Nat) (small : position < 2 ^ 24) :
    ((BitVec.ofNat 64 position <<< (8 : BitVec 6).toNat) + signExtend12 2047) + signExtend12 2025 =
      BitVec.ofNat 64 (4072 + 256 * position) := by
  apply nonce_word_of_toNat
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_shiftLeft, nonce_toNat_ofNat _ (by omega),
    Nat.shiftLeft_eq]
  have eight : (8 : BitVec 6).toNat = 8 := rfl
  have first : (signExtend12 2047).toNat = 2047 := rfl
  have second : (signExtend12 2025).toNat = 2025 := rfl
  rw [eight, first, second]
  omega

/-- One record, entered at word 472 with x24 = `record + 1`. -/
theorem nonce_expand_record (start : MachineState) (target : Nat → Byte)
    (fields nodes indices record position high : Nat)
    (facts : NonceRecordTarget start target fields nodes position)
    (positionWord : start.getMem (BitVec.ofNat 64 (indices + 8 * record)) = BitVec.ofNat 64 position)
    (positionBound : position < 2 ^ 24) (indicesAligned : indices % 8 = 0)
    (indicesBelow : indices + 8 * record + 8 ≤ nodes) (recordBound : record < 2 ^ 24)
    (order : fields ≤ nodes) (evenFields : fields % 2 = 0) (alignedNodes : nodes % 8 = 0)
    (within : nodes + 576 ≤ high) (range : high ≤ MEMORY_BYTES)
    (state : MachineState) (regs : Reg → Word) (here : NonceAt state 472 regs)
    (counter : regs .x24 = BitVec.ofNat 64 (record + 1)) (indexBase : regs .x13 = BitVec.ofNat 64 indices)
    (source : regs .x23 = BitVec.ofNat 64 (fields + 534)) (dest : regs .x25 = BitVec.ofNat 64 (nodes + 576))
    (mem : NonceExpandMem start state (nodes + 576) high target) :
    ∃ next later, NonceExpandRuns state 932 next ∧ NonceAt next (if record = 0 then 492 else 472) later ∧
      later .x24 = BitVec.ofNat 64 record ∧ later .x23 = BitVec.ofNat 64 fields ∧
      later .x25 = BitVec.ofNat 64 nodes ∧
      (∀ reg, reg ∉ [Reg.x1, .x6, .x23, .x24, .x25, .x28, .x29] → later reg = regs reg) ∧
      NonceExpandMem start next nodes high target := by
  have memoryBound : MEMORY_BYTES = 2 ^ 36 := rfl
  have zero := nonce_reg_zero here
  -- 472 and the 13 siblings
  obtain ⟨run1, at1⟩ := nonce_step_addi here .x29 .x0 13 (by decide) (by omega) (by omega) rfl
  obtain ⟨r1, at1, v1, f1⟩ := at1.fresh
  obtain ⟨next2, r2, run2, at2, source2, dest2, frame2, mem2⟩ :=
    nonce_sibling_loop start target (fields + 144) (nodes + 160) high facts.siblings (by omega) (by omega)
      (by omega) (by omega) range 12 (by omega) _ r1 at1 (by rw [v1, zero]; rfl)
      (by rw [f1 _ (by decide), source]; all_goals (congr 1 <;> omega))
      (by rw [f1 _ (by decide), dest]; all_goals (congr 1 <;> omega)) (mem.same_mem (nonce_addi_mem _ _ _ _) |> fun m => by
        simpa using m)
  -- 476, 477 and the 128 middle bytes
  obtain ⟨run3, at3⟩ := nonce_step_addi at2 .x28 .x0 64 (by decide) (by omega) (by omega) rfl
  obtain ⟨r3, at3, v3, f3⟩ := at3.fresh
  obtain ⟨run4, at4⟩ := nonce_step_jal at3 .x1 112 505 (by omega) (by omega) rfl (by decide)
  rw [if_neg (by decide)] at at4
  obtain ⟨r4, at4, v4, f4⟩ := at4.fresh
  have zero2 : r2 .x0 = 0 := nonce_reg_zero at2
  obtain ⟨next5, r5, run5, at5, source5, dest5, counter5, frame5, mem5⟩ :=
    nonce_expand_halves start _ r4 (fields + 16) (nodes + 32) 64 high 478 target at4 (by omega)
      (by rw [f4 _ (by decide), f3 _ (by decide), source2])
      (by rw [f4 _ (by decide), f3 _ (by decide), dest2])
      (by rw [f4 _ (by decide), v3, zero2]; rfl) v4 (by omega) (by decide)
      ((mem2.same_mem (nonce_addi_mem _ _ _ _)).same_mem (nonce_jal_mem _ _ _))
      (by omega) (by omega) (by omega) (by omega) range facts.middle
  -- 478..480: the zero word
  obtain ⟨run6, at6⟩ := nonce_step_addi at5 .x25 .x25 4088 (by decide) (by omega) (by omega) rfl
  obtain ⟨r6, at6, v6, f6⟩ := at6.fresh
  have dest6 : r6 .x25 = BitVec.ofNat 64 (nodes + 24) := by
    rw [v6, dest5, nonce_address_sub _ 8 _ (by decide) (by omega) (by omega) (by omega)]
    all_goals (congr 1 <;> omega)
  have zeroAddress : r6 .x25 + signExtend12 0 = BitVec.ofNat 64 (nodes + 24) := by
    rw [dest6, nonce_add_zero]
  have zero6 : r6 .x0 = 0 := nonce_reg_zero at6
  obtain ⟨run7, at7, mem7⟩ := nonce_step_sd_mem at6 .x25 .x0 0 (by omega) (by omega) rfl zeroAddress
    (mem5.same_mem (nonce_addi_mem _ _ _ _)) (by omega) (by omega) range
    (fun m inside => by rw [zero6, facts.zeros m inside]; interval_cases m <;> rfl)
  obtain ⟨run8, at8⟩ := nonce_step_addi at7 .x25 .x25 4088 (by decide) (by omega) (by omega) rfl
  obtain ⟨r8, at8, v8, f8⟩ := at8.fresh
  have dest8 : r8 .x25 = BitVec.ofNat 64 (nodes + 16) := by
    rw [v8, dest6, nonce_address_sub _ 8 _ (by decide) (by omega) (by omega) (by omega)]
    all_goals (congr 1 <;> omega)
  -- 481..487: the tag
  have counter8 : r8 .x24 = BitVec.ofNat 64 (record + 1) := by
    rw [f8 _ (by decide), f6 _ (by decide), frame5 _ (by decide) (by decide) (by decide) (by decide),
      f4 _ (by decide), f3 _ (by decide), frame2 _ (by simp), f1 _ (by decide), counter]
  have base8 : r8 .x13 = BitVec.ofNat 64 indices := by
    rw [f8 _ (by decide), f6 _ (by decide), frame5 _ (by decide) (by decide) (by decide) (by decide),
      f4 _ (by decide), f3 _ (by decide), frame2 _ (by simp), f1 _ (by decide), indexBase]
  obtain ⟨run9, at9⟩ := nonce_step_slli at8 .x6 .x24 3 (by decide) (by omega) (by omega) rfl
  obtain ⟨r9, at9, v9, f9⟩ := at9.fresh
  obtain ⟨run10, at10⟩ := nonce_step_add at9 .x6 .x6 .x13 (by decide) (by omega) (by omega) rfl
  obtain ⟨r10, at10, v10, f10⟩ := at10.fresh
  have address10 : r10 .x6 + signExtend12 4088 = BitVec.ofNat 64 (indices + 8 * record) := by
    rw [v10, v9, f9 _ (by decide), counter8, base8]
    apply nonce_word_of_toNat
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_shiftLeft, nonce_toNat_ofNat _ (by omega),
      nonce_toNat_ofNat _ (by omega), Nat.shiftLeft_eq]
    have three : (3 : BitVec 6).toNat = 3 := rfl
    have back : (signExtend12 4088).toNat = 2 ^ 64 - 8 := by decide
    rw [three, back]
    omega
  obtain ⟨run11, at11⟩ := nonce_step_ld at10 .x6 .x6 4088 (by decide) (by omega) (by omega) rfl
    (by rw [address10]; exact nonce_access_valid _ _ (by omega) (by omega))
  rw [address10] at at11
  have mem8 := mem7.same_mem (nonce_addi_mem _ .x25 .x25 4088)
  have mem10 := (mem8.same_mem (nonce_slli_mem _ .x6 .x24 3)).same_mem (nonce_add_mem _ .x6 .x6 .x13)
  have loaded : (execInstrBr (execInstrBr (execInstrBr (execInstrBr (execInstrBr next5 (.ADDI .x25 .x25 4088))
      (.SD .x25 .x0 0)) (.ADDI .x25 .x25 4088)) (.SLLI .x6 .x24 3)) (.ADD .x6 .x6 .x13)).getMem
      (BitVec.ofNat 64 (indices + 8 * record)) = BitVec.ofNat 64 position := by
    rw [mem10.read_word _ (by omega) (Or.inl (by omega)) (by omega), positionWord]
  rw [loaded] at at11
  obtain ⟨r11, at11, v11, f11⟩ := at11.fresh
  obtain ⟨run12, at12⟩ := nonce_step_slli at11 .x6 .x6 8 (by decide) (by omega) (by omega) rfl
  obtain ⟨r12, at12, v12, f12⟩ := at12.fresh
  obtain ⟨run13, at13⟩ := nonce_step_addi at12 .x6 .x6 2047 (by decide) (by omega) (by omega) rfl
  obtain ⟨r13, at13, v13, f13⟩ := at13.fresh
  obtain ⟨run14, at14⟩ := nonce_step_addi at13 .x6 .x6 2025 (by decide) (by omega) (by omega) rfl
  obtain ⟨r14, at14, v14, f14⟩ := at14.fresh
  have tag14 : r14 .x6 = BitVec.ofNat 64 (4072 + 256 * position) := by
    rw [v14, v13, v12, v11]
    exact nonce_tag_word position positionBound
  have dest14 : r14 .x25 + signExtend12 0 = BitVec.ofNat 64 (nodes + 16) := by
    rw [f14 _ (by decide), f13 _ (by decide), f12 _ (by decide), f11 _ (by decide), f10 _ (by decide),
      f9 _ (by decide), dest8, nonce_add_zero]
  have mem14 := ((((mem10.same_mem (nonce_ld_mem _ .x6 .x6 4088)).same_mem (nonce_slli_mem _ .x6 .x6 8)).same_mem
    (nonce_addi_mem _ .x6 .x6 2047)).same_mem (nonce_addi_mem _ .x6 .x6 2025))
  obtain ⟨run15, at15, mem15⟩ := nonce_step_sd_mem at14 .x25 .x6 0 (by omega) (by omega) rfl dest14
    mem14 (by omega) (by omega) range (fun m inside => by rw [tag14]; exact (facts.tag m inside).symm)
  -- 488..490: the nonce
  obtain ⟨run16, at16⟩ := nonce_step_addi at15 .x28 .x0 8 (by decide) (by omega) (by omega) rfl
  obtain ⟨r16, at16, v16, f16⟩ := at16.fresh
  obtain ⟨run17, at17⟩ := nonce_step_jal at16 .x1 64 505 (by omega) (by omega) rfl (by decide)
  rw [if_neg (by decide)] at at17
  obtain ⟨r17, at17, v17, f17⟩ := at17.fresh
  have zero14 : r14 .x0 = 0 := nonce_reg_zero at14
  obtain ⟨next18, r18, run18, at18, source18, dest18, counter18, frame18, mem18⟩ :=
    nonce_expand_halves start _ r17 fields nodes 8 high 490 target at17 (by omega)
      (by rw [f17 _ (by decide), f16 _ (by decide), f14 _ (by decide), f13 _ (by decide), f12 _ (by decide),
        f11 _ (by decide), f10 _ (by decide), f9 _ (by decide), f8 _ (by decide), f6 _ (by decide),
        source5])
      (by rw [f17 _ (by decide), f16 _ (by decide), f14 _ (by decide), f13 _ (by decide), f12 _ (by decide),
        f11 _ (by decide), f10 _ (by decide), f9 _ (by decide), dest8])
      (by rw [f17 _ (by decide), v16, zero14]; rfl) v17 (by omega) (by decide)
      ((mem15.same_mem (nonce_addi_mem _ _ _ _)).same_mem (nonce_jal_mem _ _ _))
      (by omega) (by omega) (by omega) (by omega) range facts.nonce
  obtain ⟨run19, at19⟩ := nonce_step_addi at18 .x24 .x24 4095 (by decide) (by omega) (by omega) rfl
  obtain ⟨r19, at19, v19, f19⟩ := at19.fresh
  have counter19 : r19 .x24 = BitVec.ofNat 64 record := by
    rw [v19, frame18 _ (by decide) (by decide) (by decide) (by decide), f17 _ (by decide),
      f16 _ (by decide), f14 _ (by decide), f13 _ (by decide), f12 _ (by decide), f11 _ (by decide),
      f10 _ (by decide), f9 _ (by decide), counter8,
      nonce_address_sub _ 1 _ (by decide) (by omega) (by omega) (by omega)]
    congr 1
  have zero19 := nonce_reg_zero at19
  obtain ⟨run20, at20⟩ := nonce_step_bne at19 .x24 .x0 8116 472 (by omega) (by omega) rfl (by decide)
  have test : (r19 .x24 = r19 .x0) ↔ record = 0 := by
    rw [counter19, zero19]
    exact nonce_ofNat_eq_zero record (by omega)
  refine ⟨_, r19, (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans
    (run8.trans (run9.trans (run10.trans (run11.trans (run12.trans (run13.trans (run14.trans (run15.trans
    (run16.trans (run17.trans (run18.trans (run19.trans run20))))))))))))))))))).cast (by omega),
    ?_, counter19, by rw [f19 _ (by decide), source18], by rw [f19 _ (by decide), dest18], ?_,
    (mem18.same_mem (nonce_addi_mem _ _ _ _)).same_mem (nonce_bne_mem _ _ _ _)⟩
  · by_cases empty : record = 0
    · simpa only [if_pos (test.mpr empty), if_pos empty] using at20
    · simpa only [if_neg (fun same => empty (test.mp same)), if_neg empty] using at20
  · intro reg outside
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
    obtain ⟨n1, n6, n23, n24, n25, n28, n29⟩ := outside
    rw [f19 _ n24, frame18 _ n6 n23 n25 n28, f17 _ n1, f16 _ n28, f14 _ n6, f13 _ n6, f12 _ n6, f11 _ n6,
      f10 _ n6, f9 _ n6, f8 _ n25, f6 _ n25, frame5 _ n6 n23 n25 n28, f4 _ n1, f3 _ n28,
      frame2 _ (by simp [n1, n6, n23, n25, n29]), f1 _ n29]

end CommitGolfCandidate
