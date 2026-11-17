import CommitGolfCandidate.S3Exec

/-! One unrolled stage-3 leaf on the actual interpreter: twelve fetched instructions,
26 cycles, two forward permutation queries, for every pair of replies. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem s3_nonce_imm (u w : Nat) (hu : u < 64) (hw : w < 3) :
    signExtend12 (BitVec.ofNat 12 (24 * u + 8 * w)) = BitVec.ofNat 64 (24 * u + 8 * w) := by
  interval_cases u <;> interval_cases w <;> rfl

theorem s3_heap_imm (u : Nat) (hu : u < 64) :
    signExtend12 (BitVec.ofNat 12 (32 * u)) = BitVec.ofNat 64 (32 * u) := by
  interval_cases u <;> rfl

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

theorem s3_leaf_head_register (state : MachineState) (reg : Reg) (h12 : reg ≠ .x12) :
    (s3LeafHead state).getReg reg = state.getReg reg := by
  cases reg <;> first | exact absurd rfl h12 | rfl

theorem s3_leaf_mid_register (u : Nat) (state : MachineState) (reg : Reg)
    (h6 : reg ≠ .x6) (h10 : reg ≠ .x10) (h12 : reg ≠ .x12) :
    (s3LeafMid u state).getReg reg = state.getReg reg := by
  cases reg <;> first | rfl | exact absurd rfl h6 | exact absurd rfl h10 | exact absurd rfl h12

theorem s3_leaf_tail_register (state : MachineState) (reg : Reg) (h10 : reg ≠ .x10) :
    (s3LeafTail state).getReg reg = state.getReg reg := by
  cases reg <;> first | rfl | exact absurd rfl h10

theorem s3_perm_reply_register (state : MachineState) (answer : BitVec PERMUTATION_WIDTH)
    (reg : Reg) : (s3PermReply state answer).getReg reg = state.getReg reg :=
  writeBits_register _ _ _ reg

/-- Final state of leaf `u` for the two replies. -/
def s3LeafResult (u : Nat) (state : MachineState) (first second : BitVec PERMUTATION_WIDTH) :
    MachineState :=
  s3LeafTail (s3PermReply (s3LeafMid u (s3PermReply (s3LeafHead state) first)) second)

/-- Every register outside the scratch word, the input pointer and the reply pointer survives. -/
theorem s3_leaf_result_register (u : Nat) (state : MachineState)
    (first second : BitVec PERMUTATION_WIDTH) (reg : Reg)
    (h6 : reg ≠ .x6) (h10 : reg ≠ .x10) (h12 : reg ≠ .x12) :
    (s3LeafResult u state first second).getReg reg = state.getReg reg := by
  rw [s3LeafResult, s3_leaf_tail_register _ _ h10, s3_perm_reply_register,
    s3_leaf_mid_register _ _ _ h6 h10 h12, s3_perm_reply_register,
    s3_leaf_head_register _ _ h12]

theorem s3_leaf_support (u : Nat) (state next : MachineState)
    (reachable : next ∈ support (s3Leaf u state)) :
    ∃ first second, next = s3LeafResult u state first second := by
  simp only [s3Leaf, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reachable
  obtain ⟨first, _, second, _, rfl⟩ := reachable
  exact ⟨first, second, rfl⟩

/-- The immediate -64 of the head instruction. -/
theorem s3_reply_below (cursor : Nat) (low : 64 ≤ cursor) :
    BitVec.ofNat 64 cursor + signExtend12 (4032 : BitVec 12) = BitVec.ofNat 64 (cursor - 64) := by
  rw [show signExtend12 (4032 : BitVec 12) = -(64 : Word) by decide]
  have equation : cursor = cursor - 64 + 64 := by omega
  conv_lhs => rw [equation]
  rw [BitVec.ofNat_add, BitVec.add_assoc]
  simp

/-- The head instruction aims the first reply 64 bytes below the leaf. -/
theorem s3_leaf_head_output (state : MachineState) (cursor : Nat)
    (input : state.getReg .x10 = BitVec.ofNat 64 cursor) (low : 64 ≤ cursor) :
    (s3LeafHead state).getReg .x12 = BitVec.ofNat 64 (cursor - 64) := by
  have step : (s3LeafHead state).getReg .x12 = state.getReg .x10 + signExtend12 4032 := rfl
  rw [step, input]
  exact s3_reply_below cursor low

theorem s3_leaf_head_valid (state : MachineState) :
    memoryArgumentsValid state (.ADDI .x12 .x10 4032) = true := rfl

theorem s3_leaf_head_ready (state : MachineState) (ready : S3PermReady state) :
    S3PermReady (s3LeafHead state) :=
  ⟨(s3_leaf_head_register state .x5 (by decide)).trans ready.1,
    (s3_leaf_head_register state .x11 (by decide)).trans ready.2.1,
    (s3_leaf_head_register state .x13 (by decide)).trans ready.2.2⟩

set_option maxHeartbeats 8000000 in
theorem s3_leaf_head_execute (u : Nat) (hu : u < 64) (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (1011424 + 48 * u)) (fuel : Nat) :
    execute (submission.image .commit) (1 + fuel) state true =
      (do let result ← execute (submission.image .commit) fuel (s3LeafHead state) true
          return result.charge 1 0) ∧
    (s3LeafHead state).pc = BitVec.ofNat 64 (1011424 + 48 * u + 4 * 1) :=
  s3_straight_execute (submission.image .commit) s3LeafHeadInstructions 1
    (1011424 + 48 * u) state fuel true rfl pc (by decide)
    (fun k bound current currentPC => by
      have fetched := s3_image_leaf u k hu (by omega) current currentPC
      interval_cases k <;> exact fetched)
    (fun k bound => by
      interval_cases k
      exact s3_leaf_head_valid state)

set_option maxHeartbeats 8000000 in
theorem s3_leaf_mid_execute (u : Nat) (hu : u < 64) (state : MachineState) (cursor nonce : Nat)
    (pc : state.pc = BitVec.ofNat 64 (1011424 + 48 * u + 8))
    (input : state.getReg .x10 = BitVec.ofNat 64 cursor)
    (nonces : state.getReg .x18 = BitVec.ofNat 64 nonce)
    (cursorAligned : cursor % 8 = 0) (nonceAligned : nonce % 8 = 0)
    (cursorBound : cursor + 256 ≤ MEMORY_BYTES) (nonceBound : nonce + 24 * u + 24 ≤ MEMORY_BYTES)
    (fuel : Nat) :
    execute (submission.image .commit) (8 + fuel) state true =
      (do let result ← execute (submission.image .commit) fuel (s3LeafMid u state) true
          return result.charge 8 0) ∧
    (s3LeafMid u state).pc = BitVec.ofNat 64 (1011424 + 48 * u + 8 + 4 * 8) :=
  s3_straight_execute (submission.image .commit) (s3LeafMidInstructions u) 8
    (1011424 + 48 * u + 8) state fuel true rfl pc
    (by
      intro instruction member
      simp only [s3LeafMidInstructions, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
    (fun k bound current currentPC => by
      have fetched := s3_image_leaf u (2 + k) hu (by omega) current
        (by rw [currentPC]; congr 1; omega)
      interval_cases k <;> exact fetched)
    (fun k bound => by
      interval_cases k
      · exact s3_access_valid _ _ nonce (24 * u + 8 * 0) nonces
          (s3_nonce_imm u 0 hu (by decide)) nonceAligned (by omega) (by omega)
      · exact s3_access_valid _ _ cursor 112 input rfl cursorAligned (by decide) (by omega)
      · exact s3_access_valid _ _ nonce (24 * u + 8 * 1) nonces
          (s3_nonce_imm u 1 hu (by decide)) nonceAligned (by omega) (by omega)
      · exact s3_access_valid _ _ cursor 120 input rfl cursorAligned (by decide) (by omega)
      · exact s3_access_valid _ _ nonce (24 * u + 8 * 2) nonces
          (s3_nonce_imm u 2 hu (by decide)) nonceAligned (by omega) (by omega)
      · exact s3_access_valid _ _ cursor 128 input rfl cursorAligned (by decide) (by omega)
      · rfl
      · rfl)

set_option maxHeartbeats 8000000 in
theorem s3_leaf_tail_execute (u : Nat) (hu : u < 64) (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (1011424 + 48 * u + 44)) (fuel : Nat) :
    execute (submission.image .commit) (1 + fuel) state true =
      (do let result ← execute (submission.image .commit) fuel (s3LeafTail state) true
          return result.charge 1 0) ∧
    (s3LeafTail state).pc = BitVec.ofNat 64 (1011424 + 48 * u + 44 + 4 * 1) :=
  s3_straight_execute (submission.image .commit) [.ADDI .x10 .x10 200] 1
    (1011424 + 48 * u + 44) state fuel true rfl pc (by decide)
    (fun k bound current currentPC => by
      have fetched := s3_image_leaf u (11 + k) hu (by omega) current
        (by rw [currentPC]; congr 1; omega)
      interval_cases k <;> exact fetched)
    (fun k bound => by interval_cases k; rfl)

/-! Register and PC effects for an arbitrary state. They are stated for a variable state so
that the kernel never has to look inside a 200-byte syscall reply. -/

theorem s3_leaf_mid_input (u : Nat) (state : MachineState) :
    (s3LeafMid u state).getReg .x10 = state.getReg .x10 + signExtend12 56 := rfl

theorem s3_leaf_mid_output (u : Nat) (state : MachineState) :
    (s3LeafMid u state).getReg .x12 =
      state.getReg .x23 + signExtend12 (BitVec.ofNat 12 (32 * u)) := rfl

theorem s3_leaf_tail_input (state : MachineState) :
    (s3LeafTail state).getReg .x10 = state.getReg .x10 + signExtend12 200 := rfl

theorem s3_perm_reply_pc (state : MachineState) (answer : BitVec PERMUTATION_WIDTH) :
    (s3PermReply state answer).pc = state.pc + 4 := rfl

set_option maxHeartbeats 8000000 in
/-- Leaf `u` of a group: reply pointer, first call, nonce copy, heap call, cursor advance. -/
theorem s3_leaf_execute (u : Nat) (hu : u < 64) (state : MachineState) (cursor nonce heap : Nat)
    (pc : state.pc = BitVec.ofNat 64 (1011424 + 48 * u))
    (ready : S3PermReady state)
    (input : state.getReg .x10 = BitVec.ofNat 64 cursor)
    (nonces : state.getReg .x18 = BitVec.ofNat 64 nonce)
    (slots : state.getReg .x23 = BitVec.ofNat 64 heap)
    (cursorAligned : cursor % 8 = 0) (nonceAligned : nonce % 8 = 0) (heapAligned : heap % 8 = 0)
    (cursorLow : 64 ≤ cursor)
    (cursorBound : cursor + 256 ≤ MEMORY_BYTES) (nonceBound : nonce + 24 * u + 24 ≤ MEMORY_BYTES)
    (heapBound : heap + 32 * u + 200 ≤ MEMORY_BYTES) (fuel : Nat) :
    execute (submission.image .commit) (12 + fuel) state true =
      (do let next ← s3Leaf u state
          let result ← execute (submission.image .commit) fuel next true
          return result.charge 26 2) ∧
    (∀ first second, (s3LeafResult u state first second).pc =
      BitVec.ofNat 64 (1011424 + 48 * (u + 1))) ∧
    (∀ first second, (s3LeafResult u state first second).getReg .x10 =
      BitVec.ofNat 64 (cursor + 256)) := by
  have head := s3_leaf_head_execute u hu state pc (1 + (8 + (1 + (1 + fuel))))
  have headPC := head.2
  have headInput : (s3LeafHead state).getReg .x10 = BitVec.ofNat 64 cursor :=
    (s3_leaf_head_register state .x10 (by decide)).trans input
  have headOutput := s3_leaf_head_output state cursor input cursorLow
  have headReady := s3_leaf_head_ready state ready
  have firstCall := s3_perm_call (submission.image .commit) (s3LeafHead state)
    (8 + (1 + (1 + fuel))) true
    (s3_image_leaf u 1 hu (by decide) (s3LeafHead state) headPC) headReady
    (by rw [s3_pointer_nat _ cursor headInput (by omega)]; exact cursorAligned)
    (by rw [s3_pointer_nat _ (cursor - 64) headOutput (by omega)]; omega)
    (by rw [s3_pointer_nat _ cursor headInput (by omega)]; omega)
    (by rw [s3_pointer_nat _ (cursor - 64) headOutput (by omega)]; omega)
  have replied (first : BitVec PERMUTATION_WIDTH) (reg : Reg) (h12 : reg ≠ .x12 := by decide) :
      (s3PermReply (s3LeafHead state) first).getReg reg = state.getReg reg := by
    rw [s3_perm_reply_register, s3_leaf_head_register _ _ h12]
  have repliedPC (first : BitVec PERMUTATION_WIDTH) :
      (s3PermReply (s3LeafHead state) first).pc = BitVec.ofNat 64 (1011424 + 48 * u + 8) := by
    rw [s3_perm_reply_pc]
    exact s3_pc_next _ _ 4 _ headPC (by omega)
  have mid (first : BitVec PERMUTATION_WIDTH) :=
    s3_leaf_mid_execute u hu (s3PermReply (s3LeafHead state) first) cursor nonce
      (repliedPC first) ((replied first .x10).trans input) ((replied first .x18).trans nonces)
      cursorAligned nonceAligned cursorBound nonceBound (1 + (1 + fuel))
  have midPC (first : BitVec PERMUTATION_WIDTH) := (mid first).2
  have midInput (first : BitVec PERMUTATION_WIDTH) :
      (s3LeafMid u (s3PermReply (s3LeafHead state) first)).getReg .x10 =
        BitVec.ofNat 64 (cursor + 56) := by
    rw [s3_leaf_mid_input, replied first .x10, input,
      show signExtend12 (56 : BitVec 12) = BitVec.ofNat 64 56 from rfl, ← BitVec.ofNat_add]
  have midOutput (first : BitVec PERMUTATION_WIDTH) :
      (s3LeafMid u (s3PermReply (s3LeafHead state) first)).getReg .x12 =
        BitVec.ofNat 64 (heap + 32 * u) := by
    rw [s3_leaf_mid_output, replied first .x23, slots, s3_heap_imm u hu, ← BitVec.ofNat_add]
  have midReady (first : BitVec PERMUTATION_WIDTH) :
      S3PermReady (s3LeafMid u (s3PermReply (s3LeafHead state) first)) :=
    ⟨(s3_leaf_mid_register u _ .x5 (by decide) (by decide) (by decide)).trans
        ((replied first .x5).trans ready.1),
      (s3_leaf_mid_register u _ .x11 (by decide) (by decide) (by decide)).trans
        ((replied first .x11).trans ready.2.1),
      (s3_leaf_mid_register u _ .x13 (by decide) (by decide) (by decide)).trans
        ((replied first .x13).trans ready.2.2)⟩
  have secondPC (first : BitVec PERMUTATION_WIDTH) :
      (s3LeafMid u (s3PermReply (s3LeafHead state) first)).pc =
        BitVec.ofNat 64 (1011424 + 48 * u + 4 * 10) := by
    rw [midPC first]
  have secondCall (first : BitVec PERMUTATION_WIDTH) :=
    s3_perm_call (submission.image .commit) (s3LeafMid u (s3PermReply (s3LeafHead state) first))
      (1 + fuel) true
      (s3_image_leaf u 10 hu (by decide) _ (secondPC first))
      (midReady first)
      (by rw [s3_pointer_nat _ _ (midInput first) (by omega)]; omega)
      (by rw [s3_pointer_nat _ _ (midOutput first) (by omega)]; omega)
      (by rw [s3_pointer_nat _ _ (midInput first) (by omega)]; omega)
      (by rw [s3_pointer_nat _ _ (midOutput first) (by omega)]; omega)
  have tail (first second : BitVec PERMUTATION_WIDTH) :=
    s3_leaf_tail_execute u hu
      (s3PermReply (s3LeafMid u (s3PermReply (s3LeafHead state) first)) second)
      (by
        rw [s3_perm_reply_pc]
        exact s3_pc_next _ _ 4 _ (midPC first) (by omega)) fuel
  refine ⟨?_, ?_, ?_⟩
  · rw [show 12 + fuel = 1 + (1 + (8 + (1 + (1 + fuel)))) by omega, head.1, firstCall]
    simp only [s3Leaf, bind_assoc, pure_bind]
    refine bind_congr fun first => ?_
    rw [(mid first).1, secondCall first]
    simp only [bind_assoc, pure_bind]
    refine bind_congr fun second => ?_
    rw [(tail first second).1]
    simp only [bind_assoc, pure_bind]
    refine bind_congr fun result => ?_
    simp [Execution.charge]
    try omega
  · intro first second
    have final := (tail first second).2
    rw [show 1011424 + 48 * (u + 1) = 1011424 + 48 * u + 44 + 4 * 1 by omega]
    exact final
  · intro first second
    rw [s3LeafResult, s3_leaf_tail_input, s3_perm_reply_register, midInput first,
      show signExtend12 (200 : BitVec 12) = BitVec.ofNat 64 200 from rfl, ← BitVec.ofNat_add]

end CommitGolfCandidate
