import CommitGolfCandidate.NonceExpandStep
import CommitGolfCandidate.NonceCompactHalfword
import CommitGolfCandidate.Memory

/-! Byte-level memory of the in-place expansion. `NonceExpandMem start state low high target`:
the bytes at addresses `[low, high)` already hold `target`, every other byte still holds its value
in `start`. The expansion writes downward, so `low` only decreases; a source byte below `low` is
still the delivered one. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

structure NonceExpandMem (start state : MachineState) (low high : Nat) (target : Nat → Byte) : Prop where
  bounded : high < 2 ^ 64
  ordered : low ≤ high
  inside : ∀ q, low ≤ q → q < high → state.getByte (BitVec.ofNat 64 q) = target q
  outside : ∀ q : Word, (q.toNat < low ∨ high ≤ q.toNat) → state.getByte q = start.getByte q

theorem nonce_word_bytes_ext {first second : Word}
    (same : ∀ byte, byte < 8 → extractByte first byte = extractByte second byte) : first = second := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit bounded
  have remainder : bit % 8 < 8 := by omega
  have position : bit / 8 * 8 + bit % 8 = bit := by omega
  have equal := congrArg (fun value : Byte => value.getLsbD (bit % 8)) (same (bit / 8) (by omega))
  simp only [extractByte, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, position, remainder,
    decide_true, Bool.true_and] at equal
  exact equal

/-- The eight bytes of an aligned doubleword determine it. -/
theorem nonce_expand_word_eq (before after : MachineState) (location : Nat) (aligned : location % 8 = 0)
    (same : ∀ byte < 8, before.getByte (BitVec.ofNat 64 (location + byte)) =
      after.getByte (BitVec.ofNat 64 (location + byte))) :
    before.getMem (BitVec.ofNat 64 location) = after.getMem (BitVec.ofNat 64 location) := by
  apply nonce_word_bytes_ext
  intro byte bounded
  have observed := same byte bounded
  have split : location + byte = 8 * (location / 8) + byte := by omega
  rw [split, aligned_byte before (location / 8) byte (by omega), aligned_byte after (location / 8) byte (by omega),
    Nat.div_eq_of_lt bounded, Nat.mod_eq_of_lt bounded, Nat.mul_zero, Nat.add_zero,
    show 8 * (location / 8) = location by omega] at observed
  exact observed

namespace NonceExpandMem

theorem start (state : MachineState) (high : Nat) (bounded : high < 2 ^ 64) (target : Nat → Byte) :
    NonceExpandMem state state high high target :=
  ⟨bounded, le_refl high, fun _ low high' => absurd high' (by omega), fun _ _ => rfl⟩

theorem same_mem {start state next : MachineState} {low high : Nat} {target : Nat → Byte}
    (inv : NonceExpandMem start state low high target) (same : next.mem = state.mem) :
    NonceExpandMem start next low high target := by
  have bytes : ∀ q, next.getByte q = state.getByte q := by
    intro q
    simp only [MachineState.getByte, MachineState.getMem, same]
  exact ⟨inv.bounded, inv.ordered, fun q l h => (bytes _).trans (inv.inside q l h),
    fun q out => (bytes q).trans (inv.outside q out)⟩

theorem set_pc {start state : MachineState} {low high : Nat} {target : Nat → Byte}
    (inv : NonceExpandMem start state low high target) (pc : Word) :
    NonceExpandMem start (state.setPC pc) low high target := inv.same_mem rfl

/-- The address of a byte, as a natural number. -/
theorem address_toNat (q : Nat) (small : q < 2 ^ 64) : (BitVec.ofNat 64 q).toNat = q := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]

/-- A halfword store just below `low` extends the written region by two bytes. -/
theorem half {start state : MachineState} {q high : Nat} {target : Nat → Byte}
    (inv : NonceExpandMem start state (q + 2) high target) (even : q % 2 = 0)
    (within : q + 2 ≤ high) (value : BitVec 16)
    (lowByte : value.extractLsb' 0 8 = target q) (highByte : value.extractLsb' 8 8 = target (q + 1)) :
    NonceExpandMem start (state.setHalfword (BitVec.ofNat 64 q) value) q high target := by
  have small := inv.bounded
  have addressEven : (BitVec.ofNat 64 q).toNat % 2 = 0 := by rw [address_toNat q (by omega)]; exact even
  have successor : BitVec.ofNat 64 q + 1 = BitVec.ofNat 64 (q + 1) := by
    rw [BitVec.ofNat_add]; rfl
  refine ⟨inv.bounded, by omega, ?_, ?_⟩
  · intro r low high'
    rw [half_set_read _ _ _ _ addressEven]
    by_cases first : r = q
    · subst first
      rw [if_pos rfl, lowByte]
    · have firstNe : BitVec.ofNat 64 r ≠ BitVec.ofNat 64 q := by
        intro equal
        have numeric := congrArg BitVec.toNat equal
        rw [address_toNat r (by omega), address_toNat q (by omega)] at numeric
        exact first numeric
      rw [if_neg firstNe]
      by_cases second : r = q + 1
      · subst second
        rw [if_pos successor.symm, highByte]
      · have secondNe : BitVec.ofNat 64 r ≠ BitVec.ofNat 64 q + 1 := by
          rw [successor]
          intro equal
          have numeric := congrArg BitVec.toNat equal
          rw [address_toNat r (by omega), address_toNat (q + 1) (by omega)] at numeric
          exact second numeric
        rw [if_neg secondNe]
        exact inv.inside r (by omega) high'
  · intro r out
    rw [half_set_read _ _ _ _ addressEven]
    have firstNe : r ≠ BitVec.ofNat 64 q := by
      intro equal
      rw [equal, address_toNat q (by omega)] at out
      omega
    have secondNe : r ≠ BitVec.ofNat 64 q + 1 := by
      intro equal
      rw [equal, successor, address_toNat (q + 1) (by omega)] at out
      omega
    rw [if_neg firstNe, if_neg secondNe]
    exact inv.outside r (by omega)

theorem align_of_aligned (q m : Nat) (aligned : q % 8 = 0) (byte : m < 8) (small : q + 8 ≤ 2 ^ 64) :
    alignToDword (BitVec.ofNat 64 (q + m)) = BitVec.ofNat 64 q ∧
      byteOffset (BitVec.ofNat 64 (q + m)) = m := by
  have offset : byteOffset (BitVec.ofNat 64 (q + m)) = m := by
    rw [half_offset_mod, address_toNat _ (by omega)]
    omega
  refine ⟨?_, offset⟩
  rw [half_align_eq, offset]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, address_toNat _ (by omega), address_toNat _ (by omega), address_toNat _ (by omega)]
  omega

theorem align_split (r : Word) :
    r.toNat = (alignToDword r).toNat + byteOffset r ∧ (alignToDword r).toNat % 8 = 0 ∧
      byteOffset r < 8 := by
  have parts := half_address_parts r
  have offset := half_offset_mod r
  have alignEq := half_align_eq r
  have bound := r.isLt
  have alignNat : (alignToDword r).toNat = r.toNat - r.toNat % 8 := by
    rw [alignEq, BitVec.toNat_sub, offset, address_toNat _ (by omega)]
    omega
  refine ⟨?_, ?_, ?_⟩
  · rw [alignNat, offset]; omega
  · rw [alignNat]; omega
  · rw [offset]; omega

/-- A doubleword store at an aligned address just below `low` extends the written region by
eight bytes. -/
theorem word {start state : MachineState} {q high : Nat} {target : Nat → Byte}
    (inv : NonceExpandMem start state (q + 8) high target) (aligned : q % 8 = 0)
    (within : q + 8 ≤ high) (value : Word) (bytes : ∀ m < 8, extractByte value m = target (q + m)) :
    NonceExpandMem start (state.setMem (BitVec.ofNat 64 q) value) q high target := by
  have small := inv.bounded
  have read : ∀ r : Word, (state.setMem (BitVec.ofNat 64 q) value).getByte r =
      if alignToDword r = BitVec.ofNat 64 q then extractByte value (byteOffset r) else state.getByte r := by
    intro r
    by_cases same : alignToDword r = BitVec.ofNat 64 q
    · simp only [MachineState.getByte, same, MachineState.getMem_setMem_eq, if_true]
    · simp only [MachineState.getByte, MachineState.getMem_setMem_ne same, same, if_false]
  refine ⟨inv.bounded, by omega, ?_, ?_⟩
  · intro r low high'
    rw [read]
    by_cases near : r < q + 8
    · obtain ⟨alignEq, offsetEq⟩ := align_of_aligned q (r - q) aligned (by omega) (by omega)
      rw [show q + (r - q) = r by omega] at alignEq offsetEq
      rw [if_pos alignEq, offsetEq, bytes _ (by omega), show q + (r - q) = r by omega]
    · have far : alignToDword (BitVec.ofNat 64 r) ≠ BitVec.ofNat 64 q := by
        intro equal
        obtain ⟨split, _, offsetBound⟩ := align_split (BitVec.ofNat 64 r)
        rw [equal, address_toNat _ (by omega), address_toNat _ (by omega)] at split
        omega
      rw [if_neg far]
      exact inv.inside r (by omega) high'
  · intro r out
    rw [read]
    have far : alignToDword r ≠ BitVec.ofNat 64 q := by
      intro equal
      obtain ⟨split, _, offsetBound⟩ := align_split r
      rw [equal, address_toNat _ (by omega)] at split
      omega
    rw [if_neg far]
    exact inv.outside r (by omega)

/-- A halfword below `low` is still the one of `start`. -/
theorem read_half {start state : MachineState} {low high : Nat} {target : Nat → Byte}
    (inv : NonceExpandMem start state low high target) (a : Nat) (even : a % 2 = 0) (below : a + 1 < low) :
    (state.getHalfword (BitVec.ofNat 64 a)).extractLsb' 0 8 = start.getByte (BitVec.ofNat 64 a) ∧
      (state.getHalfword (BitVec.ofNat 64 a)).extractLsb' 8 8 = start.getByte (BitVec.ofNat 64 (a + 1)) := by
  have small := inv.bounded
  have ordered := inv.ordered
  have addressEven : (BitVec.ofNat 64 a).toNat % 2 = 0 := by rw [address_toNat a (by omega)]; exact even
  have successor : BitVec.ofNat 64 a + 1 = BitVec.ofNat 64 (a + 1) := by
    rw [BitVec.ofNat_add]; rfl
  refine ⟨?_, ?_⟩
  · rw [half_get_low _ _ addressEven]
    exact inv.outside _ (Or.inl (by rw [address_toNat a (by omega)]; omega))
  · rw [half_get_high _ _ addressEven, successor]
    exact inv.outside _ (Or.inl (by rw [address_toNat (a + 1) (by omega)]; omega))

/-- An aligned doubleword outside the written region is still the one of `start`. -/
theorem read_word {start state : MachineState} {low high : Nat} {target : Nat → Byte}
    (inv : NonceExpandMem start state low high target) (a : Nat) (aligned : a % 8 = 0)
    (outsideRegion : a + 8 ≤ low ∨ high ≤ a) (small : a + 8 ≤ 2 ^ 64) :
    state.getMem (BitVec.ofNat 64 a) = start.getMem (BitVec.ofNat 64 a) := by
  apply nonce_expand_word_eq _ _ a aligned
  intro byte bounded
  apply inv.outside
  rw [address_toNat _ (by omega)]
  omega

end NonceExpandMem

/-- Store of the halfword loaded by `lhu`. -/
theorem nonce_half_roundtrip (value : BitVec 16) : (value.zeroExtend 64).truncate 16 = value := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit bounded
  simp [bounded]

/-- Address arithmetic with a nonnegative offset. -/
theorem nonce_address_add (base offset : Nat) (value : Word) (value_eq : value.toNat = offset)
    (small : base + offset < 2 ^ 64) :
    BitVec.ofNat 64 base + value = BitVec.ofNat 64 (base + offset) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, value_eq, NonceExpandMem.address_toNat _ small,
    NonceExpandMem.address_toNat _ (by omega)]
  exact Nat.mod_eq_of_lt small

/-- Address arithmetic with a negative offset. -/
theorem nonce_address_sub (base offset : Nat) (value : Word) (value_eq : value.toNat = 2 ^ 64 - offset)
    (positive : 0 < offset) (enough : offset ≤ base) (small : base < 2 ^ 64) :
    BitVec.ofNat 64 base + value = BitVec.ofNat 64 (base - offset) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, value_eq, NonceExpandMem.address_toNat _ small,
    NonceExpandMem.address_toNat _ (by omega)]
  omega

/-- An access of `width` bytes at an aligned in-range address is valid. -/
theorem nonce_access_valid (address width : Nat) (aligned : address % width = 0)
    (range : address + width ≤ MEMORY_BYTES) :
    accessValid (BitVec.ofNat 64 address) width = true := by
  have small : address < 2 ^ 64 := by
    unfold MEMORY_BYTES at range
    omega
  simp only [accessValid, rangeValid, NonceExpandMem.address_toNat _ small, Bool.and_eq_true,
    decide_eq_true_eq]
  exact ⟨range, aligned⟩

theorem nonce_word_of_toNat (value : Word) (n : Nat) (equal : value.toNat = n) :
    value = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  rw [equal, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rw [← equal]; exact value.isLt)]

theorem nonce_toNat_ofNat (n : Nat) (small : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n :=
  NonceExpandMem.address_toNat n small

/-- `sd` at an aligned address just below `low`: the written region grows by eight bytes. -/
theorem nonce_step_sd_mem {start state : MachineState} {word : Nat} {regs : Reg → Word}
    {q high : Nat} {target : Nat → Byte}
    (here : NonceAt state word regs) (base source : Reg) (offset : BitVec 12)
    (above : 445 ≤ word) (inside : word < 547) (decoded : NonceDecoded word (.SD base source offset))
    (address : regs base + signExtend12 offset = BitVec.ofNat 64 q)
    (inv : NonceExpandMem start state (q + 8) high target) (aligned : q % 8 = 0)
    (within : q + 8 ≤ high) (range : high ≤ MEMORY_BYTES)
    (bytes : ∀ m < 8, extractByte (regs source) m = target (q + m)) :
    NonceExpandRuns state 1 (execInstrBr state (.SD base source offset)) ∧
      NonceAt (execInstrBr state (.SD base source offset)) (word + 1) regs ∧
      NonceExpandMem start (execInstrBr state (.SD base source offset)) q high target := by
  obtain ⟨run, next, effect⟩ := nonce_step_sd here base source offset above inside decoded
    (by rw [address]; exact nonce_access_valid _ _ (by omega) (by omega))
  refine ⟨run, next, ?_⟩
  rw [effect, address]
  exact (inv.word aligned within _ bytes).set_pc _

end CommitGolfCandidate
