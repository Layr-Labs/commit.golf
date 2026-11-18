import CommitGolfCandidate.NonceExpandNode

/-! The halfword routine (words 505..511): x28 halfwords end at x23 and are copied, from the top
down, to the halfwords ending at x25. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

theorem nonce_reg_zero {state : MachineState} {word : Nat} {regs : Reg → Word}
    (here : NonceAt state word regs) : regs .x0 = 0 := (here.regs .x0).symm

theorem nonce_ofNat_eq_zero (m : Nat) (small : m < 2 ^ 64) : (BitVec.ofNat 64 m = 0) ↔ m = 0 := by
  constructor
  · intro equal
    have numeric := congrArg BitVec.toNat equal
    rw [NonceExpandMem.address_toNat _ small] at numeric
    exact numeric
  · intro equal
    rw [equal]
    rfl

theorem nonce_halves_iteration (start : MachineState) (a b high m : Nat) (target : Nat → Byte)
    (order : a ≤ b) (evenA : a % 2 = 0) (evenB : b % 2 = 0) (range : high ≤ MEMORY_BYTES)
    (state : MachineState) (regs : Reg → Word) (here : NonceAt state 505 regs)
    (source : regs .x23 = BitVec.ofNat 64 (a + 2 * (m + 1)))
    (dest : regs .x25 = BitVec.ofNat 64 (b + 2 * (m + 1)))
    (counter : regs .x28 = BitVec.ofNat 64 (m + 1)) (within : b + 2 * (m + 1) ≤ high)
    (copies : target (b + 2 * m) = start.getByte (BitVec.ofNat 64 (a + 2 * m)) ∧
      target (b + 2 * m + 1) = start.getByte (BitVec.ofNat 64 (a + 2 * m + 1)))
    (mem : NonceExpandMem start state (b + 2 * (m + 1)) high target) :
    ∃ next later, NonceExpandRuns state 6 next ∧ NonceAt next (if m = 0 then 511 else 505) later ∧
      later .x23 = BitVec.ofNat 64 (a + 2 * m) ∧ later .x25 = BitVec.ofNat 64 (b + 2 * m) ∧
      later .x28 = BitVec.ofNat 64 m ∧
      (∀ reg, reg ≠ .x6 → reg ≠ .x23 → reg ≠ .x25 → reg ≠ .x28 → later reg = regs reg) ∧
      NonceExpandMem start next (b + 2 * m) high target := by
  have memoryBound : MEMORY_BYTES < 2 ^ 64 := by decide
  have zero := nonce_reg_zero here
  obtain ⟨run1, at1⟩ := nonce_step_addi here .x23 .x23 4094 (by decide) (by omega) (by omega) rfl
  have source1 : regs .x23 + signExtend12 4094 = BitVec.ofNat 64 (a + 2 * m) := by
    rw [source, nonce_address_sub _ 2 _ (by decide) (by omega) (by omega) (by omega)]
    congr 1
  rw [source1] at at1
  obtain ⟨run2, at2⟩ := nonce_step_addi at1 .x25 .x25 4094 (by decide) (by omega) (by omega) rfl
  have dest2 : (Function.update regs .x23 (BitVec.ofNat 64 (a + 2 * m))) .x25 + signExtend12 4094 =
      BitVec.ofNat 64 (b + 2 * m) := by
    rw [Function.update_of_ne (by decide), dest,
      nonce_address_sub _ 2 _ (by decide) (by omega) (by omega) (by omega)]
    congr 1
  rw [dest2] at at2
  set regs2 := Function.update (Function.update regs .x23 (BitVec.ofNat 64 (a + 2 * m))) .x25
    (BitVec.ofNat 64 (b + 2 * m)) with regs2Eq
  have load2 : regs2 .x23 + signExtend12 0 = BitVec.ofNat 64 (a + 2 * m) := by
    rw [regs2Eq, Function.update_of_ne (by decide), Function.update_self]
    exact nonce_address_add _ 0 _ rfl (by omega)
  obtain ⟨run3, at3⟩ := nonce_step_lhu at2 .x6 .x23 0 (by decide) (by omega) (by omega) rfl
    (by rw [load2]; exact nonce_access_valid _ _ (by omega) (by omega))
  rw [load2] at at3
  set state2 := execInstrBr (execInstrBr state (.ADDI .x23 .x23 4094)) (.ADDI .x25 .x25 4094)
    with state2Eq
  have store3 : ∀ value : Word, (Function.update regs2 .x6 value) .x25 + signExtend12 0 =
      BitVec.ofNat 64 (b + 2 * m) := by
    intro value
    rw [Function.update_of_ne (by decide), regs2Eq, Function.update_self]
    exact nonce_address_add _ 0 _ rfl (by omega)
  obtain ⟨run4, at4, effect4⟩ := nonce_step_sh at3 .x25 .x6 0 (by omega) (by omega) rfl
    (by rw [store3]; exact nonce_access_valid _ _ (by omega) (by omega))
  rw [store3, Function.update_self, nonce_half_roundtrip] at effect4
  have mem2 : NonceExpandMem start state2 (b + 2 * m + 2) high target :=
    @NonceExpandMem.same_mem start state _ _ _ _ (by rw [show b + 2 * m + 2 = b + 2 * (m + 1) by ring]; exact mem) rfl
  have mem3 : NonceExpandMem start (execInstrBr state2 (.LHU .x6 .x23 0)) (b + 2 * m + 2) high target :=
    @NonceExpandMem.same_mem start state2 _ _ _ _ mem2 rfl
  have read := mem3.read_half (a + 2 * m) (by omega) (by omega)
  have mem4 : NonceExpandMem start (execInstrBr (execInstrBr state2 (.LHU .x6 .x23 0)) (.SH .x25 .x6 0))
      (b + 2 * m) high target := by
    rw [effect4]
    have readSame : state2.getHalfword (BitVec.ofNat 64 (a + 2 * m)) =
        (execInstrBr state2 (.LHU .x6 .x23 0)).getHalfword (BitVec.ofNat 64 (a + 2 * m)) := rfl
    exact (mem3.half (by omega) (by omega) _ (by rw [readSame, read.1, copies.1])
      (by rw [readSame, read.2, copies.2])).set_pc _
  obtain ⟨run5, at5⟩ := nonce_step_addi at4 .x28 .x28 4095 (by decide) (by omega) (by omega) rfl
  have counter5 : (Function.update regs2 .x6 ((state2.getHalfword (BitVec.ofNat 64 (a + 2 * m))).zeroExtend 64))
      .x28 + signExtend12 4095 = BitVec.ofNat 64 m := by
    rw [Function.update_of_ne (by decide), regs2Eq, Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), counter,
      nonce_address_sub _ 1 _ (by decide) (by omega) (by omega) (by omega)]
    congr 1
  rw [counter5] at at5
  obtain ⟨run6, at6⟩ := nonce_step_bne at5 .x28 .x0 8172 505 (by omega) (by omega) rfl (by decide)
  have mem6 := (@NonceExpandMem.same_mem start _
    (execInstrBr (execInstrBr (execInstrBr state2 (.LHU .x6 .x23 0)) (.SH .x25 .x6 0)) (.ADDI .x28 .x28 4095))
    _ _ _ mem4 rfl).same_mem (nonce_bne_mem _ .x28 .x0 8172)
  refine ⟨_, Function.update (Function.update regs2 .x6
      ((state2.getHalfword (BitVec.ofNat 64 (a + 2 * m))).zeroExtend 64)) .x28 (BitVec.ofNat 64 m),
    (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans run6))))).cast (by omega),
    ?_, ?_, ?_, ?_, ?_, mem6⟩
  · have condition : (Function.update (Function.update regs2 .x6
        ((state2.getHalfword (BitVec.ofNat 64 (a + 2 * m))).zeroExtend 64)) .x28 (BitVec.ofNat 64 m)) .x28 =
        (Function.update (Function.update regs2 .x6
        ((state2.getHalfword (BitVec.ofNat 64 (a + 2 * m))).zeroExtend 64)) .x28 (BitVec.ofNat 64 m)) .x0 ↔
        m = 0 := by
      rw [Function.update_self, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        regs2Eq, Function.update_of_ne (by decide), Function.update_of_ne (by decide), zero]
      exact nonce_ofNat_eq_zero m (by omega)
    by_cases empty : m = 0
    · simpa only [if_pos (condition.mpr empty), if_pos empty] using at6
    · simpa only [if_neg (fun same => empty (condition.mp same)), if_neg empty] using at6
  · rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), regs2Eq,
      Function.update_of_ne (by decide), Function.update_self]
  · rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), regs2Eq, Function.update_self]
  · rw [Function.update_self]
  · intro reg six source' dest' count'
    rw [Function.update_of_ne count', Function.update_of_ne six, regs2Eq, Function.update_of_ne dest',
      Function.update_of_ne source']

theorem nonce_halves_loop (start : MachineState) (a b high : Nat) (target : Nat → Byte)
    (order : a ≤ b) (evenA : a % 2 = 0) (evenB : b % 2 = 0) (range : high ≤ MEMORY_BYTES) :
    ∀ m, ∀ (state : MachineState) (regs : Reg → Word), NonceAt state 505 regs →
      regs .x23 = BitVec.ofNat 64 (a + 2 * (m + 1)) → regs .x25 = BitVec.ofNat 64 (b + 2 * (m + 1)) →
      regs .x28 = BitVec.ofNat 64 (m + 1) → b + 2 * (m + 1) ≤ high →
      (∀ o < 2 * (m + 1), target (b + o) = start.getByte (BitVec.ofNat 64 (a + o))) →
      NonceExpandMem start state (b + 2 * (m + 1)) high target →
      ∃ next later, NonceExpandRuns state (6 * (m + 1)) next ∧ NonceAt next 511 later ∧
        later .x23 = BitVec.ofNat 64 a ∧ later .x25 = BitVec.ofNat 64 b ∧ later .x28 = 0 ∧
        (∀ reg, reg ≠ .x6 → reg ≠ .x23 → reg ≠ .x25 → reg ≠ .x28 → later reg = regs reg) ∧
        NonceExpandMem start next b high target := by
  intro m
  induction m with
  | zero =>
    intro state regs here source dest counter within copies mem
    obtain ⟨next, later, run, at1, source1, dest1, counter1, frame, mem1⟩ :=
      nonce_halves_iteration start a b high 0 target order evenA evenB range state regs here source dest
        counter within ⟨copies 0 (by omega), copies 1 (by omega)⟩ mem
    exact ⟨next, later, run, by simpa using at1, by simpa using source1, by simpa using dest1,
      by simpa using counter1, frame, by simpa using mem1⟩
  | succ m ih =>
    intro state regs here source dest counter within copies mem
    obtain ⟨next, later, run, at1, source1, dest1, counter1, frame, mem1⟩ :=
      nonce_halves_iteration start a b high (m + 1) target order evenA evenB range state regs here source
        dest counter within
        ⟨copies _ (by omega), by rw [Nat.add_assoc b, copies _ (by omega), Nat.add_assoc]⟩ mem
    rw [if_neg (by omega)] at at1
    obtain ⟨final, last, run', at2, source2, dest2, counter2, frame', mem2⟩ :=
      ih next later at1 source1 dest1 counter1 (by omega) (fun o inside => copies o (by omega)) mem1
    refine ⟨final, last, (run.trans run').cast (by ring), at2, source2, dest2, counter2, ?_, mem2⟩
    intro reg six source' dest' count'
    rw [frame' reg six source' dest' count', frame reg six source' dest' count']

/-- The whole halfword routine, entered at word 505 with `count ≥ 1` halfwords and return word `ret`. -/
theorem nonce_expand_halves (start state : MachineState) (regs : Reg → Word) (a b count high ret : Nat)
    (target : Nat → Byte) (here : NonceAt state 505 regs) (positive : 0 < count)
    (source : regs .x23 = BitVec.ofNat 64 (a + 2 * count))
    (dest : regs .x25 = BitVec.ofNat 64 (b + 2 * count))
    (counter : regs .x28 = BitVec.ofNat 64 count)
    (link : regs .x1 = BitVec.ofNat 64 (4096 + 4 * ret)) (retSmall : 4096 + 4 * ret < 2 ^ 64)
    (masked : (BitVec.ofNat 64 (4096 + 4 * ret) + signExtend12 0) &&& ~~~1#64 =
      BitVec.ofNat 64 (4096 + 4 * ret))
    (mem : NonceExpandMem start state (b + 2 * count) high target)
    (order : a ≤ b) (evenA : a % 2 = 0) (evenB : b % 2 = 0) (within : b + 2 * count ≤ high)
    (range : high ≤ MEMORY_BYTES)
    (copies : ∀ o < 2 * count, target (b + o) = start.getByte (BitVec.ofNat 64 (a + o))) :
    ∃ next later, NonceExpandRuns state (6 * count + 1) next ∧ NonceAt next ret later ∧
      later .x23 = BitVec.ofNat 64 a ∧ later .x25 = BitVec.ofNat 64 b ∧ later .x28 = 0 ∧
      (∀ reg, reg ≠ .x6 → reg ≠ .x23 → reg ≠ .x25 → reg ≠ .x28 → later reg = regs reg) ∧
      NonceExpandMem start next b high target := by
  obtain ⟨m, rfl⟩ : ∃ m, count = m + 1 := ⟨count - 1, by omega⟩
  obtain ⟨next, later, run, at1, source1, dest1, counter1, frame, mem1⟩ :=
    nonce_halves_loop start a b high target order evenA evenB range m state regs here source dest counter
      within copies mem
  obtain ⟨run2, at2⟩ := nonce_step_ret at1 ret retSmall (by omega) (by omega) rfl
    (by rw [frame .x1 (by decide) (by decide) (by decide) (by decide), link]) masked
  exact ⟨_, later, run.trans run2, at2, source1, dest1, counter1, frame, mem1.same_mem rfl⟩

end CommitGolfCandidate
