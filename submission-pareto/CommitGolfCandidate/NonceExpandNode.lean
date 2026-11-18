import CommitGolfCandidate.NonceExpandMem

/-! The node routine (words 512..545): the 30-byte field ending at x23 becomes the 32-byte node
ending at x25, its top two bytes zero; both pointers move down by the field. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

theorem nonce_node_words : ∀ half < 15,
    NonceDecoded (515 + 2 * (14 - half)) (.LHU .x6 .x23 (BitVec.ofNat 12 (2 * half))) ∧
      NonceDecoded (516 + 2 * (14 - half)) (.SH .x25 .x6 (BitVec.ofNat 12 (2 * half))) ∧
      (signExtend12 (BitVec.ofNat 12 (2 * half))).toNat = 2 * half := by
  intro half bounded
  interval_cases half <;> exact ⟨rfl, rfl, rfl⟩

/-- Copy halfwords `n - 1, ..., 0` of the field (words `515 + 2 (15 - n)` onward). -/
theorem nonce_node_halves (start : MachineState) (a b high : Nat) (target : Nat → Byte)
    (order : a ≤ b) (evenA : a % 2 = 0) (evenB : b % 2 = 0) (within : b + 32 ≤ high)
    (range : high ≤ MEMORY_BYTES)
    (copies : ∀ o < 30, target (b + o) = start.getByte (BitVec.ofNat 64 (a + o))) :
    ∀ n ≤ 15, ∀ (state : MachineState) (regs : Reg → Word),
      NonceAt state (515 + 2 * (15 - n)) regs → regs .x23 = BitVec.ofNat 64 a →
      regs .x25 = BitVec.ofNat 64 b → NonceExpandMem start state (b + 2 * n) high target →
      ∃ next later, NonceExpandRuns state (2 * n) next ∧ NonceAt next 545 later ∧
        (∀ reg, reg ≠ .x6 → later reg = regs reg) ∧ NonceExpandMem start next b high target := by
  intro n
  induction n with
  | zero =>
    intro _ state regs here _ _ mem
    exact ⟨state, regs, NonceExpandRuns.refl state, here, fun _ _ => rfl, by simpa using mem⟩
  | succ n ih =>
    intro bounded state regs here source dest mem
    obtain ⟨loadWord, storeWord, offsetValue⟩ := nonce_node_words n (by omega)
    have memoryBound : MEMORY_BYTES < 2 ^ 64 := by decide
    have word : 515 + 2 * (15 - (n + 1)) = 515 + 2 * (14 - n) := by omega
    rw [word] at here
    have loadAddress : regs .x23 + signExtend12 (BitVec.ofNat 12 (2 * n)) = BitVec.ofNat 64 (a + 2 * n) := by
      rw [source]; exact nonce_address_add _ _ _ offsetValue (by omega)
    obtain ⟨loadRun, loaded⟩ := nonce_step_lhu here .x6 .x23 _ (by decide) (by omega) (by omega) loadWord
      (by rw [loadAddress]; exact nonce_access_valid _ _ (by omega) (by omega))
    have loadedWord : 515 + 2 * (14 - n) + 1 = 516 + 2 * (14 - n) := by omega
    rw [loadedWord] at loaded
    have storeAddress : ∀ value : Word,
        (Function.update regs .x6 value) .x25 + signExtend12 (BitVec.ofNat 12 (2 * n)) =
          BitVec.ofNat 64 (b + 2 * n) := by
      intro value
      rw [Function.update_of_ne (by decide), dest]; exact nonce_address_add _ _ _ offsetValue (by omega)
    obtain ⟨storeRun, stored, storeEq⟩ := nonce_step_sh loaded .x25 .x6 _ (by omega) (by omega) storeWord
      (by rw [storeAddress]; exact nonce_access_valid _ _ (by omega) (by omega))
    rw [storeAddress, Function.update_self, loadAddress, nonce_half_roundtrip] at storeEq
    have loadedMem : NonceExpandMem start (execInstrBr state (.LHU .x6 .x23 (BitVec.ofNat 12 (2 * n))))
        (b + 2 * n + 2) high target :=
      @NonceExpandMem.same_mem start state _ _ _ _
        (by rw [show b + 2 * n + 2 = b + 2 * (n + 1) by ring]; exact mem) rfl
    have read := loadedMem.read_half (a + 2 * n) (by omega) (by omega)
    have readSame : state.getHalfword (BitVec.ofNat 64 (a + 2 * n)) =
        (execInstrBr state (.LHU .x6 .x23 (BitVec.ofNat 12 (2 * n)))).getHalfword (BitVec.ofNat 64 (a + 2 * n)) := rfl
    have storedMem := (loadedMem.half (by omega) (by omega)
      (state.getHalfword (BitVec.ofNat 64 (a + 2 * n)))
      (by rw [readSame, read.1, copies _ (by omega)])
      (by rw [readSame, read.2, show b + 2 * n + 1 = b + (2 * n + 1) by omega, copies _ (by omega),
        Nat.add_assoc])).set_pc
      ((execInstrBr state (.LHU .x6 .x23 (BitVec.ofNat 12 (2 * n)))).pc + 4)
    rw [← storeEq] at storedMem
    have nextWord : 516 + 2 * (14 - n) + 1 = 515 + 2 * (15 - n) := by omega
    rw [nextWord] at stored
    obtain ⟨next, later, run, final, frame, finalMem⟩ := ih (by omega) _ _ stored
      (by rw [Function.update_of_ne (by decide)]; exact source)
      (by rw [Function.update_of_ne (by decide)]; exact dest) storedMem
    refine ⟨next, later, (loadRun.trans (storeRun.trans run)).cast (by omega), final, ?_, finalMem⟩
    intro reg outside
    rw [frame reg outside, Function.update_of_ne outside]

/-- The whole node routine, entered at word 512 with return word `ret`. -/
theorem nonce_expand_node (start state : MachineState) (regs : Reg → Word) (a b high ret : Nat)
    (target : Nat → Byte) (here : NonceAt state 512 regs)
    (source : regs .x23 = BitVec.ofNat 64 (a + 30)) (dest : regs .x25 = BitVec.ofNat 64 (b + 32))
    (link : regs .x1 = BitVec.ofNat 64 (4096 + 4 * ret)) (retSmall : 4096 + 4 * ret < 2 ^ 64)
    (masked : (BitVec.ofNat 64 (4096 + 4 * ret) + signExtend12 0) &&& ~~~1#64 =
      BitVec.ofNat 64 (4096 + 4 * ret))
    (mem : NonceExpandMem start state (b + 32) high target)
    (order : a ≤ b) (evenA : a % 2 = 0) (evenB : b % 2 = 0) (within : b + 32 ≤ high)
    (range : high ≤ MEMORY_BYTES)
    (copies : ∀ o < 30, target (b + o) = start.getByte (BitVec.ofNat 64 (a + o)))
    (zeros : target (b + 30) = 0 ∧ target (b + 31) = 0) :
    ∃ next later, NonceExpandRuns state 34 next ∧ NonceAt next ret later ∧
      later .x23 = BitVec.ofNat 64 a ∧ later .x25 = BitVec.ofNat 64 b ∧
      (∀ reg, reg ≠ .x6 → reg ≠ .x23 → reg ≠ .x25 → later reg = regs reg) ∧
      NonceExpandMem start next b high target := by
  have memoryBound : MEMORY_BYTES < 2 ^ 64 := by decide
  obtain ⟨run1, at1⟩ := nonce_step_addi here .x25 .x25 4064 (by decide) (by omega) (by omega) rfl
  have dest1 : regs .x25 + signExtend12 4064 = BitVec.ofNat 64 b := by
    rw [dest, nonce_address_sub _ 32 _ (by decide) (by omega) (by omega) (by omega)]
    congr 1
  rw [dest1] at at1
  obtain ⟨run2, at2⟩ := nonce_step_addi at1 .x23 .x23 4066 (by decide) (by omega) (by omega) rfl
  have source2 : (Function.update regs .x25 (BitVec.ofNat 64 b)) .x23 + signExtend12 4066 =
      BitVec.ofNat 64 a := by
    rw [Function.update_of_ne (by decide), source,
      nonce_address_sub _ 30 _ (by decide) (by omega) (by omega) (by omega)]
    congr 1
  rw [source2] at at2
  have zeroAddress : (Function.update (Function.update regs .x25 (BitVec.ofNat 64 b)) .x23
      (BitVec.ofNat 64 a)) .x25 + signExtend12 30 = BitVec.ofNat 64 (b + 30) := by
    rw [Function.update_of_ne (by decide), Function.update_self]
    exact nonce_address_add _ _ _ (by decide) (by omega)
  obtain ⟨run3, at3, effect3⟩ := nonce_step_sh at2 .x25 .x0 30 (by omega) (by omega) rfl
    (by rw [zeroAddress]; exact nonce_access_valid _ _ (by omega) (by omega))
  rw [zeroAddress] at effect3
  have mem2 : NonceExpandMem start (execInstrBr (execInstrBr state (.ADDI .x25 .x25 4064))
      (.ADDI .x23 .x23 4066)) (b + 32) high target := mem.same_mem rfl
  have zeroValue : ((Function.update (Function.update regs .x25 (BitVec.ofNat 64 b)) .x23
      (BitVec.ofNat 64 a)) .x0).truncate 16 = 0 := by
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), ← here.regs]
    rfl
  rw [zeroValue] at effect3
  have mem3 : NonceExpandMem start (execInstrBr (execInstrBr (execInstrBr state (.ADDI .x25 .x25 4064))
      (.ADDI .x23 .x23 4066)) (.SH .x25 .x0 30)) (b + 30) high target := by
    rw [effect3]
    exact (mem2.half (by omega) (by omega) 0 (by rw [zeros.1]; rfl) (by rw [zeros.2]; rfl)).set_pc _
  obtain ⟨next, later, run4, at4, frame4, mem4⟩ := nonce_node_halves start a b high target order evenA evenB
    within range copies 15 (le_refl 15) _ _ at3
    (by rw [Function.update_self])
    (by rw [Function.update_of_ne (by decide), Function.update_self]) mem3
  obtain ⟨run5, at5⟩ := nonce_step_ret at4 ret retSmall (by omega) (by omega) rfl
    (by rw [frame4 .x1 (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      link]) masked
  refine ⟨_, later, (run1.trans (run2.trans (run3.trans (run4.trans run5)))).cast (by omega), at5,
    ?_, ?_, ?_, mem4.same_mem rfl⟩
  · rw [frame4 .x23 (by decide), Function.update_self]
  · rw [frame4 .x25 (by decide), Function.update_of_ne (by decide), Function.update_self]
  · intro reg six source' dest'
    rw [frame4 reg six, Function.update_of_ne source', Function.update_of_ne dest']

end CommitGolfCandidate
