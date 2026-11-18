import CommitGolfCandidate.NonceExpandFinish
import CommitGolfCandidate.NonceExpandGuards
import CommitGolfCandidate.NonceExpandCodec
import CommitGolfCandidate.NonceExpandedInput
import CommitGolfCandidate.NonceStateEquiv
import CommitGolfCandidate.InputMemory
import CommitGolfCandidate.CapCheckIndexBytes

/-! The expansion as a whole. On an accepted delivered proof the checker reaches word 1 in a
state that agrees, register for register and at every aligned doubleword, with the retained
checker after its first word on the expanded input; otherwise it reaches the reject sequence. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- Replacing the proof leaves every loader byte outside both proof ranges unchanged. -/
theorem nonce_expand_loader_byte (input : CheckInput) (proof : Proof) (location : Nat)
    (outsideOld : ¬(capProgram.layout.proof ≤ location ∧
      location < capProgram.layout.proof + input.proof.length))
    (outsideNew : ¬(capProgram.layout.proof ≤ location ∧ location < capProgram.layout.proof + proof.length)) :
    inputByte capProgram .check {input with proof := proof} location = inputByte capProgram .check input location := by
  simp only [inputByte, Submission.inputBuffers, List.find?_cons, fixedBuffer, positionsBuffer, valuesBuffer,
    outsideOld, outsideNew, decide_false, List.find?_nil]

/-- Word 0 of the delivered checker jumps to the expansion (word 445). -/
theorem nonce_expand_entry (state : MachineState) (pc : state.pc = 4096) :
    NonceExpandRuns state 1 (state.setPC (BitVec.ofNat 64 (4096 + 4 * 445))) := by
  have word : nonceExpandedImage.code[0]? = some 0x6f40006f := by decide
  apply nonce_expand_runs_step _ _ (.base (.JAL .x0 1780))
  · apply nonce_image_fetch _ _ 0 _ (by norm_num) (by rw [pc]; rfl)
    rw [word]
    rfl
  · show some ((state.setReg .x0 (state.pc + 4)).setPC (state.pc + signExtend21 1780)) = _
    rw [pc]
    rfl

theorem nonce_extract_byte (value m : Nat) (small : value < 2 ^ 64) (byte : m < 8) :
    extractByte (BitVec.ofNat 64 value) m = BitVec.ofNat 8 (value / 2 ^ (8 * m)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt small, Nat.shiftRight_eq_div_pow]
  rw [Nat.mul_comm m 8]

theorem nonce_initial_register_other (input : CheckInput) (proof : Proof) (reg : Reg)
    (outside : reg ≠ .x17) :
    (capProgram.initialState .check {input with proof := proof}).getReg reg =
      (capProgram.initialState .check input).getReg reg := by
  unfold Submission.initialState
  rw [MachineState.getReg_setReg_ne _ .x17 reg _ (Ne.symm outside),
    MachineState.getReg_setReg_ne _ .x17 reg _ (Ne.symm outside)]
  simp only [inputCount]
  cases reg <;> simp only [MachineState.getReg, MachineState.setReg, BEq.beq, decide_false, decide_true,
    ite_true, ite_false]

theorem nonce_expanded_register (input : CheckInput) (reg : Reg) (outside : reg ≠ .x17) :
    (capProgram.initialState .check (nonceExpandedInput input)).getReg reg =
      (capProgram.initialState .check input).getReg reg :=
  nonce_initial_register_other input _ reg outside

theorem nonce_initial_scratch (input : CheckInput) :
    ∀ reg ∈ [Reg.x1, .x6, .x7, .x18, .x19, .x23, .x24, .x25, .x28, .x29, .x30],
      (capProgram.initialState .check input).getReg reg = 0 := by
  intro reg member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem nonce_expand_layout :
    capProgram.layout.proof % 8 = 0 ∧ capProgram.layout.indices % 8 = 0 ∧
      capProgram.layout.indices + 8 * 2 ^ 24 ≤ capProgram.layout.proof ∧
      capProgram.layout.proof + nonceExpandCapacity ≤ MEMORY_BYTES ∧
      capProgram.sizes.proof = nonceExpandCapacity := by
  decide

theorem nonce_check_accepts (input : CheckInput) :
    NonceCheckValid input ↔ NonceExpandAccepts input.positions.card input.proof.length := by
  have sortedLength : (input.positions.sort (· ≤ ·)).length = input.positions.card :=
    Finset.length_sort _
  have capacity := nonce_expand_layout.2.2.2.2
  constructor
  · rintro ⟨enough, whole, admitted⟩
    have size : input.proof.length = 560 * (input.positions.sort (· ≤ ·)).length +
        32 * nonceExpandFooter input.positions.card input.proof.length := by
      rw [sortedLength]; unfold nonceExpandFooter; omega
    have expanded := nonce_expand_records_length _ _ _ size
    refine ⟨enough, whole, ?_⟩
    change (s6ExpandRecords _ input.proof).length ≤ _ at admitted
    rw [expanded, sortedLength, capacity] at admitted
    exact admitted
  · rintro ⟨enough, whole, small⟩
    have size : input.proof.length = 560 * (input.positions.sort (· ≤ ·)).length +
        32 * nonceExpandFooter input.positions.card input.proof.length := by
      rw [sortedLength]; unfold nonceExpandFooter; omega
    have expanded := nonce_expand_records_length _ _ _ size
    refine ⟨enough, whole, ?_⟩
    change (s6ExpandRecords _ input.proof).length ≤ _
    rw [expanded, sortedLength, capacity]
    exact small

/-- The state at the first expansion word. -/
abbrev nonceExpandStart (input : CheckInput) : MachineState :=
  (capProgram.initialState .check input).setPC (BitVec.ofNat 64 (4096 + 4 * 445))

theorem nonce_expand_entry_facts (input : CheckInput)
    (admitted : input.proof.length ≤ capProgram.sizes.proof) :
    NonceExpandEntry (nonceExpandStart input) capProgram.layout.proof input.positions.card
      input.proof.length capProgram.layout.indices := by
  obtain ⟨aligned, indicesAligned, below, window, capacity⟩ := nonce_expand_layout
  have cardinal : input.positions.card ≤ 2 ^ 24 := by
    have bound : input.positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ input.positions
    have length : LENGTH = 2 ^ 24 := rfl
    omega
  exact ⟨rfl, rfl, rfl, rfl, rfl, by rw [← capacity]; exact admitted, cardinal, window, aligned,
    indicesAligned, by omega⟩

theorem nonce_expand_invalid (input : CheckInput) (admitted : input.proof.length ≤ capProgram.sizes.proof)
    (invalid : ¬NonceCheckValid input) :
    ∃ next steps, steps ≤ 24 ∧ NonceExpandRuns (capProgram.initialState .check input) steps next ∧
      next.pc = 4808 := by
  obtain ⟨next, regs, steps, bounded, run, here, _⟩ :=
    nonce_expand_guards _ _ _ _ _ (nonce_expand_entry_facts input admitted)
  have rejected : ¬NonceExpandAccepts input.positions.card input.proof.length :=
    fun accepted => invalid ((nonce_check_accepts input).mpr accepted)
  rw [if_neg rejected] at here
  exact ⟨next, 1 + steps, by omega, (nonce_expand_entry _ rfl).trans run, here.pc⟩

/-- The bytes of the expanded proof, by absolute address. -/
def nonceExpandTarget (input : CheckInput) (address : Nat) : Byte :=
  (nonceExpandedInput input).proof[address - capProgram.layout.proof]?.getD 0

theorem nonce_expand_valid (input : CheckInput) (valid : NonceCheckValid input) :
    ∃ next steps, steps ≤ capProgram.steps .check ∧
      NonceExpandRuns (capProgram.initialState .check input) steps next ∧
      NonceStateEquiv (nonceOldCheckTailState (nonceExpandedInput input)) next := by
  obtain ⟨aligned, indicesAligned, below, window, capacity⟩ := nonce_expand_layout
  have accepted := (nonce_check_accepts input).mp valid
  have admittedExpanded := valid.2.2
  have memoryBound : MEMORY_BYTES = 2 ^ 36 := rfl
  set P := capProgram.layout.proof with hP
  set I := capProgram.layout.indices with hI
  set c := input.positions.card with hc
  set L := input.proof.length with hL
  set f := nonceExpandFooter c L with hf
  set E := nonceExpandLength c L with hE
  set sorted := input.positions.sort (· ≤ ·) with hsorted
  set T := nonceExpandTarget input with hT
  have sortedLength : sorted.length = c := Finset.length_sort _
  obtain ⟨enough, whole, small⟩ := accepted
  have lengthEq : L = 560 * c + 32 * f := by
    rw [hf]; unfold nonceExpandFooter; omega
  have size : input.proof.length = 560 * sorted.length + 32 * f := by rw [sortedLength]; exact lengthEq
  have expandedEq : (nonceExpandedInput input).proof = s6ExpandRecords sorted input.proof := rfl
  have expandedLength : (nonceExpandedInput input).proof.length = E := by
    rw [expandedEq, nonce_expand_records_length _ _ _ size, sortedLength]; rfl
  have admitted : L ≤ capProgram.sizes.proof := by
    rw [capacity]; unfold nonceExpandLength at small; omega
  have cardinal : c ≤ 2 ^ 24 := by
    have bound : input.positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ input.positions
    have length : LENGTH = 2 ^ 24 := rfl
    omega
  have eBound : E = 576 * c + 32 * f := rfl
  -- bytes of the target and of the delivered proof
  have targetByte : ∀ k, T (P + k) = (s6ExpandRecords sorted input.proof)[k]?.getD 0 := by
    intro k
    simp only [hT, nonceExpandTarget, expandedEq]
    rw [show P + k - capProgram.layout.proof = k by rw [← hP]; omega]
  have sourceByte : ∀ k < L, (nonceExpandStart input).getByte (BitVec.ofNat 64 (P + k)) =
      input.proof[k]?.getD 0 := fun k inside => cap_check_input_proof_byte input k admitted inside
  -- footer and records of the target
  have footerFacts : NonceFooterTarget (nonceExpandStart input) T (P + 560 * c) (P + 576 * c) f := by
    constructor
    · intro j bounded o inside
      rw [show P + 576 * c + 32 * j + o = P + (576 * sorted.length + 32 * j + o) by rw [sortedLength]; ring,
        targetByte, nonce_expand_footer_byte _ _ _ size j o bounded (by omega),
        show P + 560 * c + 32 * j + o = P + (560 * sorted.length + 32 * j + o) by rw [sortedLength]; ring,
        sourceByte _ (by rw [sortedLength]; omega)]
  have recordsFacts : NonceRecordsTarget (nonceExpandStart input) T P I c := by
    intro r bounded
    have hr : r < sorted.length := by rw [sortedLength]; exact bounded
    refine ⟨(sorted[r]'hr).val, (sorted[r]'hr).isLt, cap_check_input_index input r bounded, ?_⟩
    have recordSource : ∀ k, 560 * r + k < 560 * c → (nonceExpandStart input).getByte
        (BitVec.ofNat 64 (P + 560 * r + k)) = input.proof[560 * r + k]?.getD 0 := by
      intro k inside
      rw [Nat.add_assoc]
      exact sourceByte _ (by omega)
    refine ⟨⟨?_⟩, ?_, ?_, ?_, ?_⟩
    · intro s hs o inside
      rw [show P + 576 * r + 160 + 32 * s + o = P + (576 * r + 160 + 32 * s + o) by ring, targetByte,
        nonce_expand_sibling_byte _ _ _ size r hr s o hs (by omega),
        show P + 560 * r + 144 + 32 * s + o = P + 560 * r + (144 + 32 * s + o) by ring,
        recordSource _ (by omega)]
      congr 2
      ring
    · intro m inside
      rw [show P + 576 * r + 32 + m = P + (576 * r + 32 + m) by ring, targetByte,
        nonce_expand_middle_byte _ _ _ size r hr m inside,
        show P + 560 * r + 16 + m = P + 560 * r + (16 + m) by ring, recordSource _ (by omega)]
      congr 2
      ring
    · intro m inside
      rw [show P + 576 * r + 24 + m = P + (576 * r + 24 + m) by ring, targetByte,
        nonce_expand_zero_byte _ _ _ size r hr m inside]
      rfl
    · intro m inside
      rw [show P + 576 * r + 16 + m = P + (576 * r + 16 + m) by ring, targetByte,
        nonce_expand_tag_byte _ _ _ size r hr m inside, Option.getD_some,
        nonce_extract_byte _ _ (by have := (sorted[r]'hr).isLt; simp only [LENGTH, LOG_LENGTH] at this; omega)
          inside]
      rfl
    · intro m inside
      rw [show P + 576 * r + m = P + (576 * r + m) by ring, targetByte,
        nonce_expand_nonce_byte _ _ _ size r hr m inside, recordSource _ (by omega)]
  have highBound : P + E ≤ MEMORY_BYTES := by
    have : E ≤ nonceExpandCapacity := small
    omega
  have stepsValue : capProgram.steps .check = 214748365824 := rfl
  -- guards
  obtain ⟨n1, r1, steps1, _, run1, at1, facts1⟩ :=
    nonce_expand_guards _ _ _ _ _ (nonce_expand_entry_facts input admitted)
  have acc : NonceExpandAccepts input.positions.card input.proof.length := ⟨enough, whole, small⟩
  rw [if_pos acc] at at1
  obtain ⟨hsteps1, mem1, x26₁, x18₁, x23₁, x25₁, x24₁, x29₁, _, frame1⟩ := facts1 acc
  -- footer
  have mem1' : NonceExpandMem (nonceExpandStart input) n1 (P + 576 * c + 32 * f) (P + E) T := by
    have m := (NonceExpandMem.start (nonceExpandStart input) (P + E) (by omega) T).same_mem mem1
    rw [show P + 576 * c + 32 * f = P + E by rw [eBound]; ring]
    exact m
  obtain ⟨n2, r2, run2, at2, x23₂, x25₂, frame2, mem2⟩ :=
    nonce_footer_loop (nonceExpandStart input) T (P + 560 * c) (P + 576 * c) f (P + E) footerFacts
      (by omega) (by omega) (by omega) (by rw [eBound]; omega) highBound f le_rfl n1 r1 at1 x29₁
      (by rw [x23₁]; congr 1; omega) (by rw [x25₁]; congr 1; show P + E = _; rw [eBound]; ring) mem1'
  -- records
  have zero2 := nonce_reg_zero at2
  have count2 : r2 .x24 = BitVec.ofNat 64 c := by rw [frame2 .x24 (by simp), x24₁]
  obtain ⟨run3, at3⟩ := nonce_step_beq at2 .x24 .x0 84 492 (by omega) (by omega) rfl (by decide)
  rw [count2, zero2] at at3
  have mem3 := mem2.same_mem (nonce_beq_mem _ .x24 .x0 84)
  obtain ⟨n4, r4, steps4, hsteps4, run4, at4, frame4, mem4⟩ : ∃ n4 r4 steps4, steps4 = 945 * c ∧
      NonceExpandRuns (execInstrBr n2 (.BEQ .x24 .x0 84)) steps4 n4 ∧ NonceAt n4 492 r4 ∧
      (∀ reg, reg ∉ [Reg.x1, .x6, .x23, .x24, .x25, .x28, .x29] → r4 reg = r2 reg) ∧
      NonceExpandMem (nonceExpandStart input) n4 P (P + E) T := by
    by_cases empty : c = 0
    · rw [if_pos ((nonce_ofNat_eq_zero c (by omega)).mpr empty)] at at3
      refine ⟨_, r2, 0, by omega, NonceExpandRuns.refl _, at3, fun _ _ => rfl, ?_⟩
      have collapse : P + 576 * c = P := by omega
      rw [collapse] at mem3
      exact mem3
    · rw [if_neg (fun same => empty ((nonce_ofNat_eq_zero c (by omega)).mp same))] at at3
      obtain ⟨n4, r4, run4, at4, _, _, frame4, mem4⟩ :=
        nonce_records_loop (nonceExpandStart input) T P I c (P + E) recordsFacts indicesAligned
          (by omega) cardinal aligned (by rw [eBound]; omega) highBound (c - 1) (by omega) _ r2 at3
          (by rw [count2]; congr 1; omega)
          (by rw [frame2 .x13 (by simp), frame1 .x13 (by simp)]; rfl)
          (by rw [x23₂]; congr 1; rw [Nat.sub_add_cancel (by omega)])
          (by rw [x25₂]; congr 1; rw [Nat.sub_add_cancel (by omega)])
          (by rw [Nat.sub_add_cancel (by omega)]; exact mem3)
      exact ⟨n4, r4, 945 * (c - 1 + 1), by rw [Nat.sub_add_cancel (by omega)], run4, at4, frame4, mem4⟩
  -- finish
  obtain ⟨n5, r5, run5, at5, x17₅, zeros5, frame5, mem5eq⟩ := nonce_expand_done n4 r4 at4
  have mem5 := mem4.same_mem mem5eq
  have footerBound : f ≤ L := by rw [hf]; unfold nonceExpandFooter; omega
  refine ⟨n5, 1 + steps1 + (39 * f + 1) + 1 + steps4 + 13, ?_,
    (nonce_expand_entry _ rfl).trans (run1.trans (run2.trans (run3.trans (run4.trans run5)))) |>.cast
      (by ring), ?_, ?_, ?_⟩
  · rw [hsteps1, hsteps4, stepsValue]
    have : L ≤ nonceExpandCapacity := by rw [← capacity]; exact admitted
    omega
  · rw [at5.pc]
    rfl
  · intro reg
    rw [at5.regs]
    unfold nonceOldCheckTailState
    by_cases r26 : reg = .x26
    · subst r26
      show (capProgram.initialState .check (nonceExpandedInput input)).getReg .x11 + signExtend12 0 = _
      rw [nonce_add_zero, frame5 _ (by simp), frame4 _ (by simp), frame2 _ (by simp), x26₁]
      exact nonce_expanded_register input .x11 (by decide)
    · show ((capProgram.initialState .check (nonceExpandedInput input)).setReg .x26 _).getReg reg = _
      rw [MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm r26)]
      by_cases r17 : reg = .x17
      · subst r17
        rw [x17₅, frame4 _ (by simp), frame2 _ (by simp), x18₁]
        show BitVec.ofNat 64 (nonceExpandedInput input).proof.length = _
        rw [expandedLength]
      · by_cases scratch : reg ∈ [Reg.x1, .x6, .x7, .x18, .x19, .x23, .x24, .x25, .x28, .x29, .x30]
        · rw [zeros5 reg scratch, nonce_expanded_register input reg r17,
            nonce_initial_scratch input reg scratch]
        · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at scratch
          obtain ⟨n1', n6, n7, n18, n19, n23, n24, n25, n28, n29, n30⟩ := scratch
          rw [frame5 reg (by simp [n1', n6, n7, r17, n18, n19, n23, n24, n25, n28, n29, n30]),
            frame4 reg (by simp [n1', n6, n23, n24, n25, n28, n29]),
            frame2 reg (by simp [n1', n6, n23, n25, n29]),
            frame1 reg (by simp [n6, n7, n18, n19, n23, n24, n25, r26, n28, n29, n30]),
            nonce_expanded_register input reg r17]
          rfl
  · intro address addressAligned
    have addressSmall := address.isLt
    have addressEq : BitVec.ofNat 64 address.toNat = address := by simp
    rw [← addressEq]
    show (capProgram.initialState .check (nonceExpandedInput input)).getMem _ = _
    apply nonce_expand_word_eq _ _ address.toNat addressAligned
    intro byte bounded
    have qSmall : address.toNat + byte < 2 ^ 64 := by omega
    by_cases inside : P ≤ address.toNat + byte ∧ address.toNat + byte < P + E
    · rw [mem5.inside _ inside.1 inside.2,
        show address.toNat + byte = P + (address.toNat + byte - P) by omega, targetByte,
        cap_check_input_proof_byte (nonceExpandedInput input) _ admittedExpanded
          (by rw [expandedLength]; omega)]
      rfl
    · rw [mem5.outside _ (by rw [NonceExpandMem.address_toNat _ qSmall]; omega)]
      show _ = (capProgram.initialState .check input).getByte _
      rw [initial_input_byte capProgram .check (nonceExpandedInput input) _ qSmall,
        initial_input_byte capProgram .check input _ qSmall]
      have lengthRaw : (s6ExpandRecords (input.positions.sort (· ≤ ·)) input.proof).length = E :=
        expandedLength
      exact nonce_expand_loader_byte input _ _ (by omega) (by rw [lengthRaw]; omega)

end CommitGolfCandidate
