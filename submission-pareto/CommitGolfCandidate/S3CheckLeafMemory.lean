import CommitGolfCandidate.S3CheckLeafRun
import CommitGolfCandidate.CapMemoryFrame
import CommitGolfCandidate.CheckEvaluation
import CommitGolfCandidate.S3Leaf

/-! Memory toolkit for the checker leaf: little-endian reads as natural
numbers, word-to-byte transport, and the exact effect of the load/store copy
blocks. No oracle property is used. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

/-- The natural number a little-endian read denotes. -/
def s3ReadNat (state : MachineState) (address count : Nat) : Nat :=
  ∑ i ∈ Finset.range count,
    (state.getByte (BitVec.ofNat 64 (address + i))).toNat * 2 ^ (8 * i)

theorem s3_read_buffer (state : MachineState) (address count : Nat) :
    readBuffer state address count =
      BitVec.ofNat (8 * count) (s3ReadNat state address count) := rfl

theorem s3_read_nat_add (state : MachineState) (address left right : Nat) :
    s3ReadNat state address (left + right) = s3ReadNat state address left +
      2 ^ (8 * left) * s3ReadNat state (address + left) right := by
  unfold s3ReadNat
  rw [Finset.sum_range_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Nat.mul_add, Nat.pow_add, Nat.add_assoc]
  ring

theorem s3_read_nat_bound (state : MachineState) (address count : Nat) :
    s3ReadNat state address count < 2 ^ (8 * count) := by
  induction count with
  | zero => simp [s3ReadNat]
  | succ count ih =>
    have byteBound := (state.getByte (BitVec.ofNat 64 (address + count))).isLt
    have termBound := Nat.mul_le_mul_right (2 ^ (8 * count))
      (show (state.getByte (BitVec.ofNat 64 (address + count))).toNat ≤ 255 by omega)
    rw [s3ReadNat, Finset.sum_range_succ]
    change s3ReadNat state address count + _ < _
    rw [Nat.mul_succ, Nat.pow_add]
    norm_num only [Nat.reducePow]
    omega

theorem s3_read_buffer_nat (state : MachineState) (address count : Nat) :
    (readBuffer state address count).toNat = s3ReadNat state address count := by
  rw [s3_read_buffer, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (s3_read_nat_bound state address count)]

/-- Every byte is a byte of its aligned word. -/
theorem s3_check_byte_word (state : MachineState) (address i : Nat) (aligned : address % 8 = 0) :
    state.getByte (BitVec.ofNat 64 (address + i)) =
      extractByte (state.getMem (BitVec.ofNat 64 (address + 8 * (i / 8)))) (i % 8) := by
  have byte := aligned_byte state (address / 8 + i / 8) (i % 8) (by omega)
  rw [show 8 * (address / 8 + i / 8) + i % 8 = address + i by omega,
    show 8 * (address / 8 + i / 8) + 8 * (i % 8 / 8) = address + 8 * (i / 8) by omega,
    show i % 8 % 8 = i % 8 by omega] at byte
  exact byte

/-- Equal words give equal reads, at possibly different addresses and states. -/
theorem s3_read_nat_words (left right : MachineState) (leftAddress rightAddress words : Nat)
    (leftAligned : leftAddress % 8 = 0) (rightAligned : rightAddress % 8 = 0)
    (same : ∀ word < words, left.getMem (BitVec.ofNat 64 (leftAddress + 8 * word)) =
      right.getMem (BitVec.ofNat 64 (rightAddress + 8 * word))) :
    s3ReadNat left leftAddress (8 * words) = s3ReadNat right rightAddress (8 * words) := by
  unfold s3ReadNat
  apply Finset.sum_congr rfl
  intro i hi
  have inside := Finset.mem_range.mp hi
  rw [s3_check_byte_word left leftAddress i leftAligned,
    s3_check_byte_word right rightAddress i rightAligned, same (i / 8) (by omega)]

theorem s3_read_nat_zero (state : MachineState) (address words : Nat)
    (aligned : address % 8 = 0)
    (zero : ∀ word < words, state.getMem (BitVec.ofNat 64 (address + 8 * word)) = 0) :
    s3ReadNat state address (8 * words) = 0 := by
  unfold s3ReadNat
  apply Finset.sum_eq_zero
  intro i hi
  have inside := Finset.mem_range.mp hi
  rw [s3_check_byte_word state address i aligned, zero (i / 8) (by omega)]
  simp [extractByte]

/-! ### Copy blocks -/


theorem s3_store_memory (state : MachineState) (address value query : Word) :
    (state.setMem address value).getMem query =
      if query = address then value else state.getMem query := by
  simp [MachineState.getMem, MachineState.setMem]

theorem s3_zero_register (state : MachineState) : state.getReg .x0 = 0#64 := rfl

theorem s3_word_offset (offset : Nat) (aligned : offset % 8 = 0) (small : offset < 288) :
    signExtend12 (BitVec.ofNat 12 offset) = BitVec.ofNat 64 offset := by
  obtain ⟨word, rfl⟩ : ∃ word, offset = 8 * word := ⟨offset / 8, by omega⟩
  have bound : word < 36 := by omega
  interval_cases word <;> rfl

/-- All offsets are word offsets below 288. -/
abbrev S3Small (pairs : List (Nat × Nat)) : Prop :=
  ∀ pair ∈ pairs, (pair.1 % 8 = 0 ∧ pair.1 < 288) ∧ (pair.2 % 8 = 0 ∧ pair.2 < 288)



theorem s3_copy_step_memory (base : Reg) (pair : Nat × Nat) (state : MachineState)
    (small : (pair.1 % 8 = 0 ∧ pair.1 < 288) ∧ (pair.2 % 8 = 0 ∧ pair.2 < 288))
    (address : Word) :
    (s3CopyStep base pair state).getMem address =
      if address = BitVec.ofNat 64 pair.2 then
        state.getMem (state.getReg base + BitVec.ofNat 64 pair.1)
      else state.getMem address := by
  simp only [s3CopyStep, execInstrBr, MachineState.getMem_setPC, s3_store_memory,
    MachineState.getMem_setReg, MachineState.getReg_setPC,
    MachineState.getReg_setReg_eq (by decide : Reg.x6 ≠ .x0), s3_zero_register,
    BitVec.zero_add, s3_word_offset pair.1 small.1.1 small.1.2,
    s3_word_offset pair.2 small.2.1 small.2.2]



/-- A copy block changes only its destination words. -/
theorem s3_copy_memory_outside (base : Reg) (pairs : List (Nat × Nat)) (state : MachineState)
    (small : S3Small pairs) (address : Word)
    (outside : ∀ pair ∈ pairs, address ≠ BitVec.ofNat 64 pair.2) :
    (s3Run (s3Copy base pairs) state).getMem address = state.getMem address := by
  induction pairs generalizing state with
  | nil => rfl
  | cons pair rest ih =>
    rw [s3_copy_cons, ih _ (fun other inside => small other (List.mem_cons_of_mem _ inside))
        (fun other inside => outside other (List.mem_cons_of_mem _ inside)),
      s3_copy_step_memory base pair state (small pair List.mem_cons_self),
      if_neg (outside pair List.mem_cons_self)]

theorem s3_low_distinct (left right : Nat) (leftSmall : left < 288) (rightSmall : right < 288)
    (different : left ≠ right) : BitVec.ofNat 64 left ≠ BitVec.ofNat 64 right := by
  intro equal
  have numeric := congrArg BitVec.toNat equal
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)] at numeric
  exact different numeric

/-- With distinct destinations and sources outside them, each destination word
receives its source word of the initial state. -/
theorem s3_copy_memory_inside (base : Reg) (pairs : List (Nat × Nat)) (state : MachineState)
    (baseStable : base ≠ .x6) (small : S3Small pairs)
    (distinct : pairs.Pairwise fun left right => left.2 ≠ right.2)
    (separate : ∀ source ∈ pairs, ∀ destination ∈ pairs,
      state.getReg base + BitVec.ofNat 64 source.1 ≠ BitVec.ofNat 64 destination.2)
    (pair : Nat × Nat) (inside : pair ∈ pairs) :
    (s3Run (s3Copy base pairs) state).getMem (BitVec.ofNat 64 pair.2) =
      state.getMem (state.getReg base + BitVec.ofNat 64 pair.1) := by
  induction pairs generalizing state with
  | nil => cases inside
  | cons head rest ih =>
    have headSmall := small head List.mem_cons_self
    have restSmall : S3Small rest :=
      fun other member => small other (List.mem_cons_of_mem _ member)
    have stepBase := s3_copy_step_register base head state base baseStable
    rw [List.pairwise_cons] at distinct
    rw [s3_copy_cons]
    rcases List.mem_cons.mp inside with equal | member
    · rw [equal, s3_copy_memory_outside base rest _ restSmall _ (fun other otherMember =>
          s3_low_distinct _ _ headSmall.2.2 (restSmall other otherMember).2.2
            (distinct.1 other otherMember)),
        s3_copy_step_memory base head state headSmall, if_pos rfl]
    · rw [ih (s3CopyStep base head state) restSmall distinct.2 (by
          intro source sourceMember destination destinationMember
          rw [stepBase]
          exact separate source (List.mem_cons_of_mem _ sourceMember) destination
            (List.mem_cons_of_mem _ destinationMember)) member,
        stepBase, s3_copy_step_memory base head state headSmall,
        if_neg (separate pair (List.mem_cons_of_mem _ member) head List.mem_cons_self)]

/-- Copies run in order: a destination word receives its source word of the
initial state as long as no earlier destination is a later source. -/
theorem s3_copy_memory_ordered (base : Reg) (pairs : List (Nat × Nat)) (state : MachineState)
    (baseStable : base ≠ .x6) (small : S3Small pairs)
    (distinct : pairs.Pairwise fun left right => left.2 ≠ right.2)
    (ordered : pairs.Pairwise fun earlier later =>
      state.getReg base + BitVec.ofNat 64 later.1 ≠ BitVec.ofNat 64 earlier.2)
    (pair : Nat × Nat) (inside : pair ∈ pairs) :
    (s3Run (s3Copy base pairs) state).getMem (BitVec.ofNat 64 pair.2) =
      state.getMem (state.getReg base + BitVec.ofNat 64 pair.1) := by
  induction pairs generalizing state with
  | nil => cases inside
  | cons head rest ih =>
    have headSmall := small head List.mem_cons_self
    have restSmall : S3Small rest :=
      fun other member => small other (List.mem_cons_of_mem _ member)
    have stepBase := s3_copy_step_register base head state base baseStable
    rw [List.pairwise_cons] at distinct ordered
    rw [s3_copy_cons]
    rcases List.mem_cons.mp inside with equal | member
    · rw [equal, s3_copy_memory_outside base rest _ restSmall _ (fun other otherMember =>
          s3_low_distinct _ _ headSmall.2.2 (restSmall other otherMember).2.2
            (distinct.1 other otherMember)),
        s3_copy_step_memory base head state headSmall, if_pos rfl]
    · rw [ih (s3CopyStep base head state) restSmall distinct.2
          (by simpa only [stepBase] using ordered.2) member,
        stepBase, s3_copy_step_memory base head state headSmall,
        if_neg (ordered.1 pair member)]

/-! ### Copies to a register-relative destination -/

def s6CopyAtStep (base target : Reg) (pair : Nat × Nat) (state : MachineState) :
    MachineState :=
  execInstrBr (execInstrBr state (.LD .x6 base (BitVec.ofNat 12 pair.1)))
    (.SD target .x6 (BitVec.ofNat 12 pair.2))

theorem s6_copy_at_cons (base target : Reg) (pair : Nat × Nat) (rest : List (Nat × Nat))
    (state : MachineState) :
    s3Run (s6CopyAt base target (pair :: rest)) state =
      s3Run (s6CopyAt base target rest) (s6CopyAtStep base target pair state) := rfl

theorem s6_copy_at_step_register (base target : Reg) (pair : Nat × Nat) (state : MachineState)
    (reg : Reg) (outside : reg ≠ .x6) :
    (s6CopyAtStep base target pair state).getReg reg = state.getReg reg := by
  simp only [s6CopyAtStep, execInstrBr, MachineState.getReg_setPC, s3_store_register,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside)]

theorem s6_copy_at_register (base target : Reg) (pairs : List (Nat × Nat))
    (state : MachineState) (reg : Reg) (outside : reg ≠ .x6) :
    (s3Run (s6CopyAt base target pairs) state).getReg reg = state.getReg reg := by
  induction pairs generalizing state with
  | nil => rfl
  | cons pair rest ih => rw [s6_copy_at_cons, ih, s6_copy_at_step_register _ _ _ _ _ outside]

theorem s6_copy_at_step_memory (base target : Reg) (pair : Nat × Nat) (state : MachineState)
    (small : (pair.1 % 8 = 0 ∧ pair.1 < 288) ∧ (pair.2 % 8 = 0 ∧ pair.2 < 288))
    (targetStable : target ≠ .x6) (address : Word) :
    (s6CopyAtStep base target pair state).getMem address =
      if address = state.getReg target + BitVec.ofNat 64 pair.2 then
        state.getMem (state.getReg base + BitVec.ofNat 64 pair.1)
      else state.getMem address := by
  simp only [s6CopyAtStep, execInstrBr, MachineState.getMem_setPC, s3_store_memory,
    MachineState.getMem_setReg, MachineState.getReg_setPC,
    MachineState.getReg_setReg_eq (by decide : Reg.x6 ≠ .x0),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm targetStable),
    s3_word_offset pair.1 small.1.1 small.1.2, s3_word_offset pair.2 small.2.1 small.2.2]

theorem s6_copy_at_outside (base target : Reg) (pairs : List (Nat × Nat))
    (state : MachineState) (small : S3Small pairs) (targetStable : target ≠ .x6)
    (address : Word)
    (outside : ∀ pair ∈ pairs, address ≠ state.getReg target + BitVec.ofNat 64 pair.2) :
    (s3Run (s6CopyAt base target pairs) state).getMem address = state.getMem address := by
  induction pairs generalizing state with
  | nil => rfl
  | cons pair rest ih =>
    have stepTarget := s6_copy_at_step_register base target pair state target targetStable
    rw [s6_copy_at_cons, ih _ (fun other inside => small other (List.mem_cons_of_mem _ inside))
        (fun other inside => by
          rw [stepTarget]
          exact outside other (List.mem_cons_of_mem _ inside)),
      s6_copy_at_step_memory base target pair state (small pair List.mem_cons_self)
        targetStable, if_neg (outside pair List.mem_cons_self)]

theorem s6_copy_at_inside (base target : Reg) (pairs : List (Nat × Nat))
    (state : MachineState) (small : S3Small pairs) (baseStable : base ≠ .x6)
    (targetStable : target ≠ .x6)
    (distinct : pairs.Pairwise fun left right =>
      state.getReg target + BitVec.ofNat 64 left.2 ≠
        state.getReg target + BitVec.ofNat 64 right.2)
    (separate : ∀ source ∈ pairs, ∀ destination ∈ pairs,
      state.getReg base + BitVec.ofNat 64 source.1 ≠
        state.getReg target + BitVec.ofNat 64 destination.2)
    (pair : Nat × Nat) (inside : pair ∈ pairs) :
    (s3Run (s6CopyAt base target pairs) state).getMem
        (state.getReg target + BitVec.ofNat 64 pair.2) =
      state.getMem (state.getReg base + BitVec.ofNat 64 pair.1) := by
  induction pairs generalizing state with
  | nil => cases inside
  | cons head rest ih =>
    have headSmall := small head List.mem_cons_self
    have restSmall : S3Small rest :=
      fun other member => small other (List.mem_cons_of_mem _ member)
    have stepBase := s6_copy_at_step_register base target head state base baseStable
    have stepTarget := s6_copy_at_step_register base target head state target targetStable
    rw [List.pairwise_cons] at distinct
    rw [s6_copy_at_cons]
    rcases List.mem_cons.mp inside with equal | member
    · subst equal
      rw [← stepTarget, s6_copy_at_outside base target rest _ restSmall targetStable _
          (fun other otherMember => by
            rw [stepTarget]
            exact distinct.1 other otherMember),
        stepTarget, s6_copy_at_step_memory base target pair state headSmall targetStable,
        if_pos rfl]
    · have shifted := ih (s6CopyAtStep base target head state) restSmall
        (by simpa only [stepTarget] using distinct.2)
        (by
          intro source sourceMember destination destinationMember
          rw [stepBase, stepTarget]
          exact separate source (List.mem_cons_of_mem _ sourceMember) destination
            (List.mem_cons_of_mem _ destinationMember)) member
      rw [stepTarget, stepBase] at shifted
      rw [shifted, s6_copy_at_step_memory base target head state headSmall targetStable,
        if_neg (separate pair (List.mem_cons_of_mem _ member) head List.mem_cons_self)]

end CommitGolfCandidate
