import CommitGolfCandidate.S3Exec

/-! One unrolled leaf and one group call on the actual interpreter. A leaf is eleven fetched
instructions, 25 cycles and two forward permutation queries; a group call is three instructions,
ten cycles and one query; both for every reply. Register and PC facts are stated over a variable
state, so the kernel never unfolds a 200-byte reply write to check them. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem s3_nonce_imm (l w : Nat) (hl : l < 64) (hw : w < 2) :
    signExtend12 (BitVec.ofNat 12 (16 * l + 8 * w)) = BitVec.ofNat 64 (16 * l + 8 * w) := by
  interval_cases l <;> interval_cases w <;> rfl

theorem s3_pc_next (pc : Word) (start k target : Nat) (h : pc = BitVec.ofNat 64 start)
    (sum : start + k = target) : pc + BitVec.ofNat 64 k = BitVec.ofNat 64 target := by
  rw [h, ← sum, BitVec.ofNat_add]

theorem s3_pointer_nat (register : Word) (address : Nat)
    (value : register = BitVec.ofNat 64 address) (bounded : address ≤ MEMORY_BYTES) :
    register.toNat = address := by
  rw [value, BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  dsimp [MEMORY_BYTES] at bounded
  omega

theorem s3_perm_reply_register (state : MachineState) (answer : BitVec PERMUTATION_WIDTH)
    (reg : Reg) : (s3PermReply state answer).getReg reg = state.getReg reg :=
  writeBits_register _ _ _ reg

theorem s3_perm_reply_pc (state : MachineState) (answer : BitVec PERMUTATION_WIDTH) :
    (s3PermReply state answer).pc = state.pc + 4 := rfl

/-! ### Cells -/

theorem s6_cell_register_ne (c : Nat) : s6CellRegister c ≠ .x10 ∧ s6CellRegister c ≠ .x0 := by
  unfold s6CellRegister
  split
  · decide
  · split <;> decide

theorem s6_cell_imm (c : Nat) (hc : c < 16) :
    signExtend12 (BitVec.ofNat 12 (s6CellOffset c)) = BitVec.ofNat 64 (s6CellOffset c) := by
  interval_cases c <;> rfl

theorem s6_slot_imm (c u : Nat) (hc : c < 16) (hu : u < 4) :
    signExtend12 (BitVec.ofNat 12 (s6CellOffset c + (72 + 32 * u))) =
      BitVec.ofNat 64 (s6CellOffset c + (72 + 32 * u)) := by
  interval_cases c <;> interval_cases u <;> rfl

/-- The cell base register plus a small offset, for the three cell-base registers of a block. -/
theorem s6_cell_address (state : MachineState) (cell c k : Nat) (hc : c < 16)
    (imm : signExtend12 (BitVec.ofNat 12 (s6CellOffset c + k)) = BitVec.ofNat 64 (s6CellOffset c + k))
    (r23 : state.getReg .x23 = BitVec.ofNat 64 cell)
    (r25 : state.getReg .x25 = BitVec.ofNat 64 (cell + 1840))
    (r27 : state.getReg .x27 = BitVec.ofNat 64 (cell + 3680)) :
    state.getReg (s6CellRegister c) + signExtend12 (BitVec.ofNat 12 (s6CellOffset c + k)) =
      BitVec.ofNat 64 (cell + 368 * c + k) := by
  rw [imm]
  unfold s6CellRegister s6CellOffset
  by_cases first : c < 5
  · rw [if_pos first, if_pos first, r23, ← BitVec.ofNat_add]
    congr 1
    omega
  · by_cases second : c < 10
    · rw [if_neg first, if_neg first, if_pos second, if_pos second, r25, ← BitVec.ofNat_add]
      congr 1
      omega
    · rw [if_neg first, if_neg first, if_neg second, if_neg second, r27, ← BitVec.ofNat_add]
      congr 1
      omega

theorem s6_cell_offset_bound (c : Nat) (hc : c < 16) : s6CellOffset c ≤ 1840 := by
  unfold s6CellOffset
  split
  · omega
  · split <;> omega

/-! ### Leaf pieces over a variable state -/

theorem s3_leaf_head_register (l : Nat) (state : MachineState) (reg : Reg)
    (h6 : reg ≠ .x6) (h12 : reg ≠ .x12) :
    (s3LeafHead l state).getReg reg = state.getReg reg := by
  cases reg <;> first | exact absurd rfl h6 | exact absurd rfl h12 | rfl

theorem s3_sd_register (state : MachineState) (base source : Reg) (offset : BitVec 12) (reg : Reg) :
    (execInstrBr state (.SD base source offset)).getReg reg = state.getReg reg := by
  cases reg <;> rfl

theorem s3_ld_register (state : MachineState) (destination base : Reg) (offset : BitVec 12) (reg : Reg)
    (different : destination ≠ reg) :
    (execInstrBr state (.LD destination base offset)).getReg reg = state.getReg reg := by
  show ((state.setReg destination _).setPC _).getReg reg = _
  rw [MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ different]

theorem s3_addi_value (state : MachineState) (destination source : Reg) (offset : BitVec 12)
    (nonzero : destination ≠ .x0) :
    (execInstrBr state (.ADDI destination source offset)).getReg destination =
      state.getReg source + signExtend12 offset := by
  show ((state.setReg destination _).setPC _).getReg destination = _
  rw [MachineState.getReg_setPC, MachineState.getReg_setReg_eq nonzero]

/-- The first reply pointer, by rewriting through the head (no kernel unfolding of the whole
head state). -/
theorem s3_leaf_head_output (l : Nat) (state : MachineState) :
    (s3LeafHead l state).getReg .x12 = state.getReg .x10 + signExtend12 (BitVec.ofNat 12 4040) := by
  simp only [s3LeafHead, s3LeafHeadInstructions, List.foldl_cons, List.foldl_nil]
  rw [s3_addi_value _ .x12 .x10 _ (by decide), s3_sd_register, s3_sd_register,
    s3_ld_register _ .x6 .x18 _ .x10 (by decide), s3_sd_register,
    s3_ld_register _ .x6 .x18 _ .x10 (by decide)]

theorem s3_leaf_mid_register (l : Nat) (state : MachineState) (reg : Reg)
    (h10 : reg ≠ .x10) (h12 : reg ≠ .x12) :
    (s3LeafMid l state).getReg reg = state.getReg reg := by
  cases reg <;> first | exact absurd rfl h10 | exact absurd rfl h12 | rfl

theorem s3_leaf_mid_input (l : Nat) (state : MachineState) :
    (s3LeafMid l state).getReg .x10 = state.getReg .x10 + signExtend12 80 := rfl

theorem s3_leaf_mid_output (l : Nat) (state : MachineState) :
    (s3LeafMid l state).getReg .x12 = state.getReg (s6CellRegister (l / 4)) +
      signExtend12 (BitVec.ofNat 12 (s6CellOffset (l / 4) + 72 + 32 * (l % 4))) := by
  show (((state.setReg .x10 (state.getReg .x10 + signExtend12 80)).setPC (state.pc + 4)).getReg
    (s6CellRegister (l / 4)) + _) = _
  rw [MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (s6_cell_register_ne (l / 4)).1.symm]

theorem s3_leaf_tail_register (l : Nat) (state : MachineState) (reg : Reg)
    (h : reg ≠ s3LeafNextRegister l) :
    (s3LeafTail l state).getReg reg = state.getReg reg := by
  show ((state.setReg (s3LeafNextRegister l) _).setPC _).getReg reg = _
  rw [MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h)]

theorem s3_leaf_tail_next (l : Nat) (state : MachineState) :
    (s3LeafTail l state).getReg (s3LeafNextRegister l) = state.getReg .x10 + signExtend12 176 := by
  unfold s3LeafTail s3LeafTailInstruction s3LeafNextRegister
  split <;> rfl

theorem s3_leaf_tail_pc (l : Nat) (state : MachineState) :
    (s3LeafTail l state).pc = state.pc + 4 := rfl

/-- Final state of leaf `l` for the two replies. -/
def s3LeafResult (l : Nat) (state : MachineState) (first second : BitVec PERMUTATION_WIDTH) :
    MachineState :=
  s3LeafTail l (s3PermReply (s3LeafMid l (s3PermReply (s3LeafHead l state) first)) second)

theorem s3_leaf_support (l : Nat) (state next : MachineState)
    (reachable : next ∈ support (s3Leaf l state)) :
    ∃ first second, next = s3LeafResult l state first second := by
  simp only [s3Leaf, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reachable
  obtain ⟨first, _, second, _, rfl⟩ := reachable
  exact ⟨first, second, rfl⟩

/-- Every register outside the scratch word, the window, the reply pointer and the parking
register survives a leaf. -/
theorem s3_leaf_result_register (l : Nat) (state : MachineState)
    (first second : BitVec PERMUTATION_WIDTH) (reg : Reg)
    (h6 : reg ≠ .x6) (h10 : reg ≠ .x10) (h12 : reg ≠ .x12) (h21 : reg ≠ .x21) :
    (s3LeafResult l state first second).getReg reg = state.getReg reg := by
  have next : reg ≠ s3LeafNextRegister l := by
    unfold s3LeafNextRegister
    split
    · exact h21
    · exact h10
  rw [s3LeafResult, s3_leaf_tail_register _ _ _ next, s3_perm_reply_register,
    s3_leaf_mid_register _ _ _ h10 h12, s3_perm_reply_register,
    s3_leaf_head_register _ _ _ h6 h12]

/-! ### One leaf -/

set_option maxHeartbeats 8000000 in
/-- Slots 0..5 of leaf `l`: the nonce copy, the tag store and the first reply pointer. -/
theorem s3_leaf_head_block (l : Nat) (hl : l < 64) (state : MachineState) (window nonce : Nat)
    (pc : state.pc = BitVec.ofNat 64 (1012276 + 44 * l))
    (input : state.getReg .x10 = BitVec.ofNat 64 window)
    (nonces : state.getReg .x18 = BitVec.ofNat 64 nonce)
    (windowAligned : window % 8 = 0) (nonceAligned : nonce % 8 = 0)
    (windowBound : window + 24 ≤ MEMORY_BYTES) (nonceBound : nonce + 16 * l + 16 ≤ MEMORY_BYTES)
    (fuel : Nat) :
    execute (submission.image .commit) (6 + fuel) state true =
      (do let result ← execute (submission.image .commit) fuel (s3LeafHead l state) true
          return result.charge 6 0) ∧
    (s3LeafHead l state).pc = BitVec.ofNat 64 (1012276 + 44 * l + 4 * 6) :=
  s3_straight_execute (submission.image .commit) (s3LeafHeadInstructions l) 6
    (1012276 + 44 * l) state fuel true rfl pc
    (by
      intro instruction member
      simp only [s3LeafHeadInstructions, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
    (fun k bound current currentPC => by
      have fetched := s3_image_leaf l k hl (by omega) current currentPC
      interval_cases k <;> exact fetched)
    (fun k bound => by
      interval_cases k
      · exact s3_access_valid _ _ nonce (16 * l + 8 * 0) nonces
          (s3_nonce_imm l 0 hl (by decide)) nonceAligned (by omega) (by omega)
      · exact s3_access_valid _ _ window 0 input rfl windowAligned (by decide) (by omega)
      · exact s3_access_valid _ _ nonce (16 * l + 8 * 1) nonces
          (s3_nonce_imm l 1 hl (by decide)) nonceAligned (by omega) (by omega)
      · exact s3_access_valid _ _ window 8 input rfl windowAligned (by decide) (by omega)
      · exact s3_access_valid _ _ window 16 input rfl windowAligned (by decide) (by omega)
      · rfl)

/-- Slots 7..8 of leaf `l`: window up by 80, second reply pointer at the digest slot. -/
theorem s3_leaf_mid_block (l : Nat) (hl : l < 64) (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (1012276 + 44 * l + 28)) (fuel : Nat) :
    execute (submission.image .commit) (2 + fuel) state true =
      (do let result ← execute (submission.image .commit) fuel (s3LeafMid l state) true
          return result.charge 2 0) ∧
    (s3LeafMid l state).pc = BitVec.ofNat 64 (1012276 + 44 * l + 28 + 4 * 2) :=
  s3_straight_execute (submission.image .commit) (s3LeafMidInstructions l) 2
    (1012276 + 44 * l + 28) state fuel true rfl pc
    (by
      intro instruction member
      simp only [s3LeafMidInstructions, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> rfl)
    (fun k bound current currentPC => by
      have fetched := s3_image_leaf l (7 + k) hl (by omega) current
        (by rw [currentPC]; congr 1; omega)
      interval_cases k <;> exact fetched)
    (fun k bound => by interval_cases k <;> rfl)

/-- Slot 10 of leaf `l`: the next window. -/
theorem s3_leaf_tail_block (l : Nat) (hl : l < 64) (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (1012276 + 44 * l + 40)) (fuel : Nat) :
    execute (submission.image .commit) (1 + fuel) state true =
      (do let result ← execute (submission.image .commit) fuel (s3LeafTail l state) true
          return result.charge 1 0) ∧
    (s3LeafTail l state).pc = BitVec.ofNat 64 (1012276 + 44 * (l + 1)) := by
  have tail := s3_straight_execute (submission.image .commit) [s3LeafTailInstruction l] 1
    (1012276 + 44 * l + 40) state fuel true rfl pc (by intro _ member; simp at member; subst member; rfl)
    (fun k bound current currentPC => by
      have fetched := s3_image_leaf l (10 + k) hl (by omega) current
        (by rw [currentPC]; congr 1; omega)
      interval_cases k
      exact fetched)
    (fun k bound => by interval_cases k; rfl)
  refine ⟨tail.1, ?_⟩
  rw [show 1012276 + 44 * (l + 1) = 1012276 + 44 * l + 40 + 4 * 1 by omega]
  exact tail.2

/-- Pointers and fixed syscall arguments at leaf `l` of a block: window, nonce block and the
three cell-base registers. -/
structure S6LeafState (state : MachineState) (l window nonce cell : Nat) : Prop where
  pc : state.pc = BitVec.ofNat 64 (1012276 + 44 * l)
  ready : S3PermReady state
  input : state.getReg .x10 = BitVec.ofNat 64 window
  nonces : state.getReg .x18 = BitVec.ofNat 64 nonce
  cell23 : state.getReg .x23 = BitVec.ofNat 64 cell
  cell25 : state.getReg .x25 = BitVec.ofNat 64 (cell + 1840)
  cell27 : state.getReg .x27 = BitVec.ofNat 64 (cell + 3680)

set_option maxHeartbeats 8000000 in
/-- Leaf `l` of a block (x10 = leaf address - 24): nonce copy and tag, first call on
`[x10, x10 + 200)` with the reply at `x10 - 56`, second call on `[x10 + 80, x10 + 280)` with the
reply at the digest slot `cell + 368 (l / 4) + 72 + 32 (l % 4)`, next window. -/
theorem s3_leaf_execute (l : Nat) (hl : l < 64) (state : MachineState) (window nonce cell : Nat)
    (invariant : S6LeafState state l window nonce cell)
    (windowAligned : window % 8 = 0) (nonceAligned : nonce % 8 = 0) (cellAligned : cell % 8 = 0)
    (windowLow : 56 ≤ window)
    (windowBound : window + 280 ≤ MEMORY_BYTES) (nonceBound : nonce + 16 * l + 16 ≤ MEMORY_BYTES)
    (cellBound : cell + 5888 ≤ MEMORY_BYTES) (fuel : Nat) :
    execute (submission.image .commit) (11 + fuel) state true =
      (do let next ← s3Leaf l state
          let result ← execute (submission.image .commit) fuel next true
          return result.charge 25 2) ∧
    (∀ first second, (s3LeafResult l state first second).pc =
      BitVec.ofNat 64 (1012276 + 44 * (l + 1))) ∧
    (∀ first second, (s3LeafResult l state first second).getReg (s3LeafNextRegister l) =
      BitVec.ofNat 64 (window + 256)) ∧
    (∀ first second, (s3LeafResult l state first second).getReg .x10 =
      BitVec.ofNat 64 (if l = 63 then window + 80 else window + 256)) := by
  have head := s3_leaf_head_block l hl state window nonce invariant.pc invariant.input
    invariant.nonces windowAligned nonceAligned (by omega) nonceBound (1 + (2 + (1 + (1 + fuel))))
  have headKept (reg : Reg) (h6 : reg ≠ .x6 := by decide) (h12 : reg ≠ .x12 := by decide) :
      (s3LeafHead l state).getReg reg = state.getReg reg :=
    s3_leaf_head_register l state reg h6 h12
  have headInput : (s3LeafHead l state).getReg .x10 = BitVec.ofNat 64 window :=
    (headKept .x10).trans invariant.input
  have headOutput : (s3LeafHead l state).getReg .x12 = BitVec.ofNat 64 (window - 56) := by
    rw [s3_leaf_head_output, invariant.input,
      show signExtend12 (BitVec.ofNat 12 4040) = BitVec.ofNat 64 (2 ^ 64 - 56) from rfl,
      ← BitVec.ofNat_add]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    omega
  have headReady : S3PermReady (s3LeafHead l state) :=
    ⟨(headKept .x5).trans invariant.ready.1, (headKept .x11).trans invariant.ready.2.1,
      (headKept .x13).trans invariant.ready.2.2⟩
  have firstCall := s3_perm_call (submission.image .commit) (s3LeafHead l state)
    (2 + (1 + (1 + fuel))) true
    (s3_image_leaf l 6 hl (by decide) (s3LeafHead l state) head.2) headReady
    (by rw [s3_pointer_nat _ window headInput (by omega)]; exact windowAligned)
    (by rw [s3_pointer_nat _ (window - 56) headOutput (by omega)]; omega)
    (by rw [s3_pointer_nat _ window headInput (by omega)]; omega)
    (by rw [s3_pointer_nat _ (window - 56) headOutput (by omega)]; omega)
  have replied (first : BitVec PERMUTATION_WIDTH) (reg : Reg) (h6 : reg ≠ .x6 := by decide)
      (h12 : reg ≠ .x12 := by decide) :
      (s3PermReply (s3LeafHead l state) first).getReg reg = state.getReg reg := by
    rw [s3_perm_reply_register, headKept reg h6 h12]
  have repliedPC (first : BitVec PERMUTATION_WIDTH) :
      (s3PermReply (s3LeafHead l state) first).pc = BitVec.ofNat 64 (1012276 + 44 * l + 28) := by
    rw [s3_perm_reply_pc]
    exact s3_pc_next _ _ 4 _ head.2 (by omega)
  have mid (first : BitVec PERMUTATION_WIDTH) :=
    s3_leaf_mid_block l hl (s3PermReply (s3LeafHead l state) first) (repliedPC first) (1 + (1 + fuel))
  have midKept (first : BitVec PERMUTATION_WIDTH) (reg : Reg) (h6 : reg ≠ .x6 := by decide)
      (h10 : reg ≠ .x10 := by decide) (h12 : reg ≠ .x12 := by decide) :
      (s3LeafMid l (s3PermReply (s3LeafHead l state) first)).getReg reg = state.getReg reg :=
    (s3_leaf_mid_register l _ reg h10 h12).trans (replied first reg h6 h12)
  have midInput (first : BitVec PERMUTATION_WIDTH) :
      (s3LeafMid l (s3PermReply (s3LeafHead l state) first)).getReg .x10 =
        BitVec.ofNat 64 (window + 80) := by
    rw [s3_leaf_mid_input, replied first .x10, invariant.input,
      show signExtend12 (80 : BitVec 12) = BitVec.ofNat 64 80 from rfl, ← BitVec.ofNat_add]
  have slot : cell + 368 * (l / 4) + (72 + 32 * (l % 4)) + 200 ≤ MEMORY_BYTES := by omega
  have midOutput (first : BitVec PERMUTATION_WIDTH) :
      (s3LeafMid l (s3PermReply (s3LeafHead l state) first)).getReg .x12 =
        BitVec.ofNat 64 (cell + 368 * (l / 4) + (72 + 32 * (l % 4))) := by
    rw [s3_leaf_mid_output, Nat.add_assoc (s6CellOffset (l / 4))]
    have cells := s6_cell_address (s3PermReply (s3LeafHead l state) first) cell (l / 4)
      (72 + 32 * (l % 4)) (by omega) (s6_slot_imm (l / 4) (l % 4) (by omega) (by omega))
      ((replied first .x23).trans invariant.cell23) ((replied first .x25).trans invariant.cell25)
      ((replied first .x27).trans invariant.cell27)
    exact cells
  have midReady (first : BitVec PERMUTATION_WIDTH) :
      S3PermReady (s3LeafMid l (s3PermReply (s3LeafHead l state) first)) :=
    ⟨(midKept first .x5).trans invariant.ready.1, (midKept first .x11).trans invariant.ready.2.1,
      (midKept first .x13).trans invariant.ready.2.2⟩
  have secondCall (first : BitVec PERMUTATION_WIDTH) :=
    s3_perm_call (submission.image .commit) (s3LeafMid l (s3PermReply (s3LeafHead l state) first))
      (1 + fuel) true
      (s3_image_leaf l 9 hl (by decide) _ (by
        rw [(mid first).2, show 1012276 + 44 * l + 28 + 4 * 2 = 1012276 + 44 * l + 4 * 9 by omega]))
      (midReady first)
      (by rw [s3_pointer_nat _ _ (midInput first) (by omega)]; omega)
      (by rw [s3_pointer_nat _ _ (midOutput first) (by omega)]; omega)
      (by rw [s3_pointer_nat _ _ (midInput first) (by omega)]; omega)
      (by rw [s3_pointer_nat _ _ (midOutput first) (by omega)]; omega)
  have tail (first second : BitVec PERMUTATION_WIDTH) :=
    s3_leaf_tail_block l hl
      (s3PermReply (s3LeafMid l (s3PermReply (s3LeafHead l state) first)) second)
      (by
        rw [s3_perm_reply_pc]
        exact s3_pc_next _ _ 4 _ (mid first).2 (by omega)) fuel
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show 11 + fuel = 6 + (1 + (2 + (1 + (1 + fuel)))) by omega, head.1, firstCall]
    simp only [s3Leaf, bind_assoc, pure_bind]
    refine bind_congr fun first => ?_
    rw [(mid first).1, secondCall first]
    simp only [bind_assoc, pure_bind]
    refine bind_congr fun second => ?_
    rw [(tail first second).1]
    simp only [bind_assoc, pure_bind]
    refine bind_congr fun result => ?_
    simp [Execution.charge]
    omega
  · intro first second
    rw [s3LeafResult]
    exact (tail first second).2
  · intro first second
    rw [s3LeafResult, s3_leaf_tail_next, s3_perm_reply_register, midInput first,
      show signExtend12 (176 : BitVec 12) = BitVec.ofNat 64 176 from rfl, ← BitVec.ofNat_add]
    all_goals first | rfl | (congr 1; omega)
  · intro first second
    by_cases last : l = 63
    · have kept : (s3LeafResult l state first second).getReg .x10 =
          (s3LeafMid l (s3PermReply (s3LeafHead l state) first)).getReg .x10 := by
        have parked : Reg.x10 ≠ s3LeafNextRegister l := by
          unfold s3LeafNextRegister
          rw [if_pos last]
          decide
        rw [s3LeafResult, s3_leaf_tail_register l _ .x10 parked,
          s3_perm_reply_register]
      rw [kept, midInput first, if_pos last]
    · have next : s3LeafNextRegister l = .x10 := by unfold s3LeafNextRegister; rw [if_neg last]
      rw [if_neg last, s3LeafResult, ← next, s3_leaf_tail_next, s3_perm_reply_register, midInput first,
        show signExtend12 (176 : BitVec 12) = BitVec.ofNat 64 176 from rfl, ← BitVec.ofNat_add]
      all_goals first | rfl | (congr 1; omega)

/-! ### One group call -/

theorem s6_group_call_head_register (c : Nat) (state : MachineState) (reg : Reg)
    (h10 : reg ≠ .x10) (h12 : reg ≠ .x12) :
    (s6GroupCallHead c state).getReg reg = state.getReg reg := by
  cases reg <;> first | exact absurd rfl h10 | exact absurd rfl h12 | rfl

theorem s6_group_call_head_input (c : Nat) (state : MachineState) :
    (s6GroupCallHead c state).getReg .x10 =
      state.getReg (s6CellRegister c) + signExtend12 (BitVec.ofNat 12 (s6CellOffset c)) := by
  show ((((state.setReg .x10 _).setPC _).setReg .x12 _).setPC _).getReg .x10 = _
  rw [MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ .x12 .x10 _ (by decide),
    MachineState.getReg_setPC]
  rfl

theorem s6_group_call_head_output (c : Nat) (state : MachineState) :
    (s6GroupCallHead c state).getReg .x12 =
      (state.setReg .x10 (state.getReg (s6CellRegister c) +
        signExtend12 (BitVec.ofNat 12 (s6CellOffset c)))).getReg .x24 +
        signExtend12 (BitVec.ofNat 12 (32 * c)) := rfl

/-- Final state of group call `c` for its reply. -/
def s6GroupCallResult (c : Nat) (state : MachineState) (answer : BitVec PERMUTATION_WIDTH) :
    MachineState :=
  s3PermReply (s6GroupCallHead c state) answer

theorem s6_group_call_support (c : Nat) (state next : MachineState)
    (reachable : next ∈ support (s6GroupCall c state)) :
    ∃ answer, next = s6GroupCallResult c state answer := by
  simp only [s6GroupCall, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reachable
  obtain ⟨answer, _, rfl⟩ := reachable
  exact ⟨answer, rfl⟩

theorem s6_group_call_result_register (c : Nat) (state : MachineState)
    (answer : BitVec PERMUTATION_WIDTH) (reg : Reg) (h10 : reg ≠ .x10) (h12 : reg ≠ .x12) :
    (s6GroupCallResult c state answer).getReg reg = state.getReg reg := by
  rw [s6GroupCallResult, s3_perm_reply_register, s6_group_call_head_register c state reg h10 h12]

theorem s32_imm (c : Nat) (hc : c < 16) :
    signExtend12 (BitVec.ofNat 12 (32 * c)) = BitVec.ofNat 64 (32 * c) := by
  interval_cases c <;> rfl

set_option maxHeartbeats 8000000 in
/-- Group call `c` of a block: window = cell `c`, reply at the group node `x24 + 32 c`. Three
instructions, ten cycles, one query. -/
theorem s6_group_call_execute (c : Nat) (hc : c < 16) (state : MachineState) (cell group : Nat)
    (pc : state.pc = BitVec.ofNat 64 (1015092 + 12 * c)) (ready : S3PermReady state)
    (r23 : state.getReg .x23 = BitVec.ofNat 64 cell)
    (r25 : state.getReg .x25 = BitVec.ofNat 64 (cell + 1840))
    (r27 : state.getReg .x27 = BitVec.ofNat 64 (cell + 3680))
    (r24 : state.getReg .x24 = BitVec.ofNat 64 group)
    (cellAligned : cell % 8 = 0) (groupAligned : group % 8 = 0)
    (cellBound : cell + 5888 ≤ MEMORY_BYTES) (groupBound : group + 680 ≤ MEMORY_BYTES)
    (fuel : Nat) :
    execute (submission.image .commit) (3 + fuel) state true =
      (do let next ← s6GroupCall c state
          let result ← execute (submission.image .commit) fuel next true
          return result.charge 10 1) ∧
    (∀ answer, (s6GroupCallResult c state answer).pc = BitVec.ofNat 64 (1015092 + 12 * (c + 1))) ∧
    (s6GroupCallHead c state).getReg .x10 = BitVec.ofNat 64 (cell + 368 * c) ∧
    (s6GroupCallHead c state).getReg .x12 = BitVec.ofNat 64 (group + 32 * c) := by
  have head := s3_straight_execute (submission.image .commit) (s6GroupCallInstructions c) 2
    (1015092 + 12 * c) state (1 + fuel) true rfl pc
    (by
      intro instruction member
      simp only [s6GroupCallInstructions, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> rfl)
    (fun k bound current currentPC => by
      have fetched := s6_image_group_call c k hc (by omega) current currentPC
      interval_cases k <;> exact fetched)
    (fun k bound => by interval_cases k <;> rfl)
  have headRun : execute (submission.image .commit) (2 + (1 + fuel)) state true =
      (do let result ← execute (submission.image .commit) (1 + fuel) (s6GroupCallHead c state) true
          return result.charge 2 0) := head.1
  have input : (s6GroupCallHead c state).getReg .x10 = BitVec.ofNat 64 (cell + 368 * c) := by
    rw [s6_group_call_head_input]
    have := s6_cell_address state cell c 0 hc (by simpa using s6_cell_imm c hc) r23 r25 r27
    simpa using this
  have output : (s6GroupCallHead c state).getReg .x12 = BitVec.ofNat 64 (group + 32 * c) := by
    rw [s6_group_call_head_output, MachineState.getReg_setReg_ne _ .x10 .x24 _ (by decide), r24,
      s32_imm c hc, ← BitVec.ofNat_add]
  have kept (reg : Reg) (h10 : reg ≠ .x10 := by decide) (h12 : reg ≠ .x12 := by decide) :
      (s6GroupCallHead c state).getReg reg = state.getReg reg :=
    s6_group_call_head_register c state reg h10 h12
  have call := s3_perm_call (submission.image .commit) (s6GroupCallHead c state) fuel true
    (s6_image_group_call c 2 hc (by decide) _ head.2)
    ⟨(kept .x5).trans ready.1, (kept .x11).trans ready.2.1, (kept .x13).trans ready.2.2⟩
    (by rw [s3_pointer_nat _ _ input (by omega)]; omega)
    (by rw [s3_pointer_nat _ _ output (by omega)]; omega)
    (by rw [s3_pointer_nat _ _ input (by omega)]; omega)
    (by rw [s3_pointer_nat _ _ output (by omega)]; omega)
  refine ⟨?_, fun answer => ?_, input, output⟩
  · rw [show 3 + fuel = 2 + (1 + fuel) by omega, headRun, call]
    simp only [s6GroupCall, bind_assoc, pure_bind]
    refine bind_congr fun answer => ?_
    refine bind_congr fun result => ?_
    simp [Execution.charge]
    omega
  · have headPC : (s6GroupCallHead c state).pc = BitVec.ofNat 64 (1015092 + 12 * c + 4 * 2) := head.2
    rw [s6GroupCallResult, s3_perm_reply_pc, headPC]
    exact s3_pc_next _ _ 4 _ rfl (by omega)

end CommitGolfCandidate
