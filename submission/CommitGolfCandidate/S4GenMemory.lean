import CommitGolfCandidate.S3LeafBytes
import CommitGolfCandidate.S4Gen

/-! Nonce generator: fixed-oracle memory refinement.

The input block is `[seed - 168, seed + 32)`: the counter word, 160 zero bytes and the 32-byte seed.
Call `k` (from `S4_GEN_CALLS - 1` down to `0`) stores its reply address as the counter, permutes the
block and writes the reply at `nonce - 24 + 176 k`. Reply bytes `24..200` are the nonces `11k .. 11k+10`
at `nonce + 176 k`; later calls write lower and only cover the first 24 bytes of an earlier reply.
Afterwards five stores clear the counter word and the seed. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option exponentiation.threshold 4096
set_option maxRecDepth 100000

/-! ### Fixed-oracle evaluation -/

private theorem gen_evaluation_state (oracle : Oracle) {α β : Type}
    (computation : OracleComp World α) (continuation : α → OracleComp World β) :
    (checkEvaluation oracle (computation >>= continuation)).1 =
      (checkEvaluation oracle (continuation (checkEvaluation oracle computation).1)).1 := by
  rw [check_evaluation_bind]

private theorem gen_evaluation_calls (oracle : Oracle) {α β : Type}
    (computation : OracleComp World α) (continuation : α → OracleComp World β) :
    (checkEvaluation oracle (computation >>= continuation)).2 =
      (checkEvaluation oracle computation).2 +
        (checkEvaluation oracle (continuation (checkEvaluation oracle computation).1)).2 := by
  rw [check_evaluation_bind]

private theorem gen_evaluation_pure_state (oracle : Oracle) {α : Type} (value : α) :
    (checkEvaluation oracle (pure value : OracleComp World α)).1 = value := by
  rw [check_evaluation_pure]

private theorem gen_evaluation_pure_calls (oracle : Oracle) {α : Type} (value : α) :
    (checkEvaluation oracle (pure value : OracleComp World α)).2 = 0 := by
  rw [check_evaluation_pure]

/-! ### Words -/

private theorem gen_extract_byte (word : Word) (j : Nat) :
    extractByte word j = word.extractLsb' (8*j) 8 := by
  apply BitVec.eq_of_toNat_eq
  simp only [extractByte, BitVec.truncate, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    BitVec.extractLsb'_toNat, Nat.mul_comm]

private theorem gen_minus (value : Nat) (low : 168 ≤ value) :
    BitVec.ofNat 64 value + signExtend12 (BitVec.ofNat 12 3928) = BitVec.ofNat 64 (value - 168) := by
  rw [show signExtend12 (BitVec.ofNat 12 3928) = BitVec.ofNat 64 (2^64 - 168) by decide,
    ← BitVec.ofNat_add]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  rw [show value + (2^64 - 168) = (value - 168) + 2^64 by omega, Nat.add_mod_right]

private theorem gen_step (value : Nat) (low : 176 ≤ value) :
    BitVec.ofNat 64 value + signExtend12 (BitVec.ofNat 12 3920) = BitVec.ofNat 64 (value - 176) := by
  rw [show signExtend12 (BitVec.ofNat 12 3920) = BitVec.ofNat 64 (2^64 - 176) by decide,
    ← BitVec.ofNat_add]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  rw [show value + (2^64 - 176) = (value - 176) + 2^64 by omega, Nat.add_mod_right]

private theorem gen_branch_memory (state : MachineState) (left right : Reg) (offset : BitVec 13) :
    (execInstrBr state (.BGEU left right offset)).mem = state.mem := by
  simp only [execInstrBr]
  split <;> rfl

private theorem gen_branch_register (state : MachineState) (left right : Reg) (offset : BitVec 13)
    (reg : Reg) : (execInstrBr state (.BGEU left right offset)).getReg reg = state.getReg reg := by
  simp only [execInstrBr]
  split <;> rfl

private theorem gen_addi_register (state : MachineState) (target source : Reg) (immediate : BitVec 12)
    (reg : Reg) (other : reg ≠ target) :
    (execInstrBr state (.ADDI target source immediate)).getReg reg = state.getReg reg := by
  show ((state.setReg target (state.getReg source + signExtend12 immediate)).setPC (state.pc + 4)).getReg
    reg = _
  rw [MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm other)]

private theorem gen_read_zero (state : MachineState) (address count : Nat)
    (zero : ∀ i < count, state.getByte (BitVec.ofNat 64 (address+i)) = 0) :
    (readBuffer state address count).toNat = 0 := by
  unfold readBuffer
  rw [Finset.sum_eq_zero (fun i hi => by simp [zero i (Finset.mem_range.mp hi)])]
  simp

/-! ### Setup -/

theorem s4_gen_setup_memory (state : MachineState) : (s4GenSetup state).mem = state.mem := rfl

theorem s4_gen_setup_input (state : MachineState) :
    (s4GenSetup state).getReg .x10 = state.getReg .x18 + signExtend12 (BitVec.ofNat 12 3928) := rfl

private theorem gen_setup_output (state : MachineState) :
    (s4GenSetup state).getReg .x12 =
      BitVec.ofNat 64 2080382976 + state.getReg .x9 + signExtend12 (56 : BitVec 12) := by
  have lui : ((507906 : BitVec 20).zeroExtend 32 <<< 12).signExtend 64 = BitVec.ofNat 64 2080382976 := by
    decide
  rw [← lui]
  rfl

private theorem gen_setup_bound (state : MachineState) :
    (s4GenSetup state).getReg .x6 =
      BitVec.ofNat 64 1811939328 + state.getReg .x9 + signExtend12 (232 : BitVec 12) := by
  have lui : ((442368 : BitVec 20).zeroExtend 32 <<< 12).signExtend 64 = BitVec.ofNat 64 1811939328 := by
    decide
  rw [← lui]
  rfl

private theorem gen_setup_register (state : MachineState) (reg : Reg) (h6 : reg ≠ .x6) (h10 : reg ≠ .x10)
    (h11 : reg ≠ .x11) (h12 : reg ≠ .x12) (h13 : reg ≠ .x13) :
    (s4GenSetup state).getReg reg = state.getReg reg := by
  cases reg <;> first | exact absurd rfl h6 | exact absurd rfl h10 | exact absurd rfl h11 |
    exact absurd rfl h12 | exact absurd rfl h13 | rfl

/-- The loop bound of the generator: the nonce base minus 24. -/
theorem s4_gen_setup_limit (state : MachineState) (heap : Nat)
    (base : state.getReg .x9 = BitVec.ofNat 64 heap) :
    (s4GenSetup state).getReg .x6 = BitVec.ofNat 64 (heap + 1811939560) := by
  rw [gen_setup_bound, base, show signExtend12 (232 : BitVec 12) = BitVec.ofNat 64 232 by decide,
    ← BitVec.ofNat_add, ← BitVec.ofNat_add]
  congr 1
  omega

/-! ### One call -/

/-- State at the permutation call: the counter (x12) stored at x10. -/
def s4GenStored (state : MachineState) : MachineState := execInstrBr state (.SD .x10 .x12 0)

/-- Reply of the generator call made from `state`. -/
def s4GenReply (oracle : Oracle) (state : MachineState) : BitVec PERMUTATION_WIDTH :=
  oracle.permutation (s3PermInput (s4GenStored state))

/-- State after one generator call. -/
def s4GenNext (oracle : Oracle) (state : MachineState) : MachineState :=
  execInstrBr (s3PermReply (s4GenStored state) (s4GenReply oracle state))
    (.ADDI .x12 .x12 (BitVec.ofNat 12 3920))

theorem s4_gen_call_evaluation (oracle : Oracle) (state : MachineState) :
    checkEvaluation oracle (s4GenCall state) = (s4GenNext oracle state, 1) := by
  unfold s4GenCall
  simp only [check_evaluation_public_bind, check_evaluation_pure]
  rfl

theorem s4_gen_call_state (oracle : Oracle) (state : MachineState) :
    (checkEvaluation oracle (s4GenCall state)).1 = s4GenNext oracle state := by
  rw [s4_gen_call_evaluation]

theorem s4_gen_call_queries (oracle : Oracle) (state : MachineState) :
    (checkEvaluation oracle (s4GenCall state)).2 = 1 := by
  rw [s4_gen_call_evaluation]

theorem s4_gen_stored_memory (state : MachineState) :
    (s4GenStored state).mem =
      (state.setMem (state.getReg .x10 + signExtend12 0) (state.getReg .x12)).mem := rfl

theorem s4_gen_stored_register (state : MachineState) (reg : Reg) :
    (s4GenStored state).getReg reg = state.getReg reg := by
  cases reg <;> rfl

theorem s4_gen_stored_byte (state : MachineState) (low query : Nat)
    (input : state.getReg .x10 = BitVec.ofNat 64 low) (aligned : low % 8 = 0)
    (bound : low + 8 ≤ 2^64) (queryBound : query < 2^64) :
    (s4GenStored state).getByte (BitVec.ofNat 64 query) =
      if low ≤ query ∧ query < low + 8 then extractByte (state.getReg .x12) (query - low)
      else state.getByte (BitVec.ofNat 64 query) := by
  rw [s3_byte_memory _ _ (s4_gen_stored_memory state), s3_address _ low 0 0 input rfl]
  have stored := s3_store_byte state (low + 0) (state.getReg .x12) query (by omega) (by omega)
    queryBound
  rw [Nat.add_zero] at stored
  exact stored

theorem s4_gen_next_memory (oracle : Oracle) (state : MachineState) :
    (s4GenNext oracle state).mem = (s3PermReply (s4GenStored state) (s4GenReply oracle state)).mem := rfl

theorem s4_gen_next_register (oracle : Oracle) (state : MachineState) (reg : Reg)
    (other : reg ≠ .x12) : (s4GenNext oracle state).getReg reg = state.getReg reg := by
  unfold s4GenNext
  rw [gen_addi_register _ _ _ _ reg other, s3_reply_register, s4_gen_stored_register]

theorem s4_gen_next_output (oracle : Oracle) (state : MachineState) :
    (s4GenNext oracle state).getReg .x12 = state.getReg .x12 + signExtend12 (BitVec.ofNat 12 3920) := by
  unfold s4GenNext
  show (s3PermReply (s4GenStored state) (s4GenReply oracle state)).getReg .x12 +
    signExtend12 (BitVec.ofNat 12 3920) = _
  rw [s3_reply_register, s4_gen_stored_register]

/-- Bytes after one call: the reply at x12, the counter at x10, otherwise unchanged. -/
theorem s4_gen_next_byte (oracle : Oracle) (state : MachineState) (low destination query : Nat)
    (input : state.getReg .x10 = BitVec.ofNat 64 low)
    (output : state.getReg .x12 = BitVec.ofNat 64 destination)
    (aligned : low % 8 = 0) (lowBound : low + 8 ≤ 2^64) (bound : destination + 200 ≤ 2^64)
    (queryBound : query < 2^64) :
    (s4GenNext oracle state).getByte (BitVec.ofNat 64 query) =
      if destination ≤ query ∧ query < destination + 200 then
        (s4GenReply oracle state).extractLsb' (8*(query-destination)) 8
      else if low ≤ query ∧ query < low + 8 then
        extractByte (BitVec.ofNat 64 destination) (query - low)
      else state.getByte (BitVec.ofNat 64 query) := by
  rw [s3_byte_memory _ _ (s4_gen_next_memory oracle state),
    s3_reply_byte (s4GenStored state) destination query _
      ((s4_gen_stored_register state .x12).trans output) bound queryBound,
    s4_gen_stored_byte state low query input aligned lowBound queryBound, output]

/-- The permutation input of a call: the counter, then the 192 bytes above it. -/
theorem s4_gen_input (state : MachineState) (low destination : Nat)
    (input : state.getReg .x10 = BitVec.ofNat 64 low)
    (output : state.getReg .x12 = BitVec.ofNat 64 destination)
    (aligned : low % 8 = 0) (lowBound : low + 200 ≤ 2^64) (small : destination < 2^64) :
    (s3PermInput (s4GenStored state)).toNat =
      destination + 2^64 * (readBuffer state (low+8) 192).toNat := by
  have pointer : ((s4GenStored state).getReg .x10).toNat = low := by
    rw [s4_gen_stored_register, input, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have bytes (q : Nat) (hq : q < 2^64) :=
    s4_gen_stored_byte state low q input aligned (by omega) hq
  have counter : readBuffer (s4GenStored state) low 8 =
      (BitVec.ofNat 64 destination).extractLsb' (8*0) (8*8) :=
    read_serialized_slice _ _ low 0 8 (fun j hj => by
      rw [bytes _ (by omega), if_pos (by omega), output, show low + j - low = j by omega,
        Nat.zero_add]
      exact gen_extract_byte _ j)
  have counterNat : (readBuffer (s4GenStored state) low 8).toNat = destination := by
    rw [counter, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.mul_zero, Nat.shiftRight_zero,
      Nat.mod_eq_of_lt small]
    exact Nat.mod_eq_of_lt small
  have rest : readBuffer (s4GenStored state) (low+8) 192 = readBuffer state (low+8) 192 :=
    s3_read_congr _ _ _ _ 192 (fun i hi => by rw [bytes _ (by omega), if_neg (by omega)])
  have whole := s3_read_append (s4GenStored state) low 8 192 200 (low+8) rfl rfl
  rw [counterNat, rest] at whole
  unfold s3PermInput
  rw [pointer]
  exact whole

/-! ### Loop invariant -/

/-- Input of the call that writes its reply at `nonce - 24 + 176 k`, when the 192 bytes above the
counter hold `window`. -/
def s4GenBlock (nonce window k : Nat) : BitVec PERMUTATION_WIDTH :=
  BitVec.ofNat PERMUTATION_WIDTH ((nonce - 24 + 176 * k) + 2^64 * window)

/-- Memory and pointers when the calls `k ≥ remaining` are done: bytes outside the counter word
and the reply region are as at `start`; each done call's reply bytes `24..200` are in place. -/
structure S4GenProgress (oracle : Oracle) (low nonce total : Nat) (start state : MachineState)
    (remaining : Nat) : Prop where
  input : state.getReg .x10 = BitVec.ofNat 64 low
  output : 0 < remaining → state.getReg .x12 = BitVec.ofNat 64 (nonce - 24 + 176 * (remaining - 1))
  outside : ∀ q, q < 2^64 → (q < low ∨ low + 8 ≤ q) → (q < nonce - 24 ∨ nonce + 176 * total ≤ q) →
    state.getByte (BitVec.ofNat 64 q) = start.getByte (BitVec.ofNat 64 q)
  done : ∀ q, nonce + 176 * remaining ≤ q → q < nonce + 176 * total →
    state.getByte (BitVec.ofNat 64 q) =
      (oracle.permutation (s4GenBlock nonce (readBuffer start (low + 8) 192).toNat
        ((q - nonce) / 176))).extractLsb' (8 * (24 + (q - nonce) % 176)) 8

theorem s4_gen_progress_transport (oracle : Oracle) (low nonce total : Nat)
    (start left right : MachineState) (remaining : Nat) (memory : right.mem = left.mem)
    (input : right.getReg .x10 = left.getReg .x10) (output : right.getReg .x12 = left.getReg .x12)
    (progress : S4GenProgress oracle low nonce total start left remaining) :
    S4GenProgress oracle low nonce total start right remaining :=
  ⟨input.trans progress.input, fun positive => output.trans (progress.output positive),
    fun q hq counter side => (s3_byte_memory right left memory _).trans
      (progress.outside q hq counter side),
    fun q lowq highq => (s3_byte_memory right left memory _).trans (progress.done q lowq highq)⟩

set_option maxHeartbeats 4000000 in
/-- One call extends the invariant by one block. -/
theorem s4_gen_progress_call (oracle : Oracle) (low nonce total : Nat) (start state : MachineState)
    (remaining : Nat) (aligned : low % 8 = 0) (window : low + 200 ≤ nonce - 24)
    (bound : nonce + 176 * total ≤ 2^64) (more : remaining + 1 ≤ total)
    (progress : S4GenProgress oracle low nonce total start state (remaining + 1)) :
    S4GenProgress oracle low nonce total start (s4GenNext oracle state) remaining := by
  obtain ⟨input, output, outside, done⟩ := progress
  have pointer : state.getReg .x12 = BitVec.ofNat 64 (nonce - 24 + 176 * remaining) := by
    have current := output (by omega)
    rwa [show remaining + 1 - 1 = remaining by omega] at current
  have bytes (q : Nat) (hq : q < 2^64) :=
    s4_gen_next_byte oracle state low (nonce - 24 + 176 * remaining) q input pointer
      aligned (by omega) (by omega) hq
  have sameWindow : readBuffer state (low + 8) 192 = readBuffer start (low + 8) 192 :=
    s3_read_congr _ _ _ _ 192 (fun i hi => outside _ (by omega) (Or.inr (by omega)) (Or.inl (by omega)))
  have block : s3PermInput (s4GenStored state) =
      s4GenBlock nonce (readBuffer start (low + 8) 192).toNat remaining := by
    apply BitVec.eq_of_toNat_eq
    unfold s4GenBlock
    rw [BitVec.toNat_ofNat, ← sameWindow,
      ← s4_gen_input state low (nonce - 24 + 176 * remaining) input pointer aligned (by omega)
        (by omega)]
    exact (Nat.mod_eq_of_lt (s3PermInput (s4GenStored state)).isLt).symm
  have reply : s4GenReply oracle state =
      oracle.permutation (s4GenBlock nonce (readBuffer start (low + 8) 192).toNat remaining) := by
    unfold s4GenReply
    rw [block]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (s4_gen_next_register oracle state .x10 (by decide)).trans input
  · intro positive
    rw [s4_gen_next_output, pointer, gen_step _ (by omega),
      show nonce - 24 + 176 * remaining - 176 = nonce - 24 + 176 * (remaining - 1) by omega]
  · intro q hq counter side
    rw [bytes q hq, if_neg (by omega), if_neg (by omega)]
    exact outside q hq counter side
  · intro q lowq highq
    by_cases fresh : q < nonce + 176 * (remaining + 1)
    · rw [bytes q (by omega), if_pos (by omega), reply,
        show (q - nonce) / 176 = remaining by omega,
        show 8 * (q - (nonce - 24 + 176 * remaining)) = 8 * (24 + (q - nonce) % 176) by omega]
    · rw [bytes q (by omega), if_neg (by omega), if_neg (by omega)]
      exact done q (by omega) highq

theorem s4_gen_calls_state (oracle : Oracle) (state : MachineState) (count : Nat) :
    (checkEvaluation oracle (s4GenCalls state (count + 1))).1 =
      (checkEvaluation oracle (s4GenCalls (s4GenNext oracle state) count)).1 := by
  rw [s4GenCalls, gen_evaluation_state, s4_gen_call_state]

theorem s4_gen_progress_calls (oracle : Oracle) (low nonce total : Nat) (start : MachineState)
    (aligned : low % 8 = 0) (window : low + 200 ≤ nonce - 24) (bound : nonce + 176 * total ≤ 2^64)
    (count : Nat) : ∀ (state : MachineState) (remaining : Nat), remaining + count ≤ total →
      S4GenProgress oracle low nonce total start state (remaining + count) →
      S4GenProgress oracle low nonce total start (checkEvaluation oracle (s4GenCalls state count)).1
        remaining := by
  induction count with
  | zero =>
    intro state remaining _ progress
    rw [s4GenCalls, gen_evaluation_pure_state]
    exact progress
  | succ count ih =>
    intro state remaining fits progress
    rw [s4_gen_calls_state]
    apply ih _ remaining (by omega)
    apply s4_gen_progress_call oracle low nonce total start state (remaining + count) aligned window
      bound (by omega)
    rwa [show remaining + count + 1 = remaining + (count + 1) by omega]

theorem s4_gen_pass_state (oracle : Oracle) (state : MachineState) :
    (checkEvaluation oracle (s4GenPass state)).1 =
      execInstrBr (checkEvaluation oracle (s4GenCalls state 64)).1
        (.BGEU .x12 .x6 (BitVec.ofNat 13 7424)) := by
  rw [s4GenPass, gen_evaluation_state, gen_evaluation_pure_state]

theorem s4_gen_progress_passes (oracle : Oracle) (low nonce total : Nat) (start : MachineState)
    (aligned : low % 8 = 0) (window : low + 200 ≤ nonce - 24) (bound : nonce + 176 * total ≤ 2^64)
    (passes : Nat) : ∀ (state : MachineState) (remaining : Nat), remaining + 64 * passes ≤ total →
      S4GenProgress oracle low nonce total start state (remaining + 64 * passes) →
      S4GenProgress oracle low nonce total start (checkEvaluation oracle (s4GenPasses state passes)).1
        remaining := by
  induction passes with
  | zero =>
    intro state remaining _ progress
    rw [s4GenPasses, gen_evaluation_pure_state]
    exact progress
  | succ passes ih =>
    intro state remaining fits progress
    rw [s4GenPasses, gen_evaluation_state]
    apply ih _ remaining (by omega)
    rw [s4_gen_pass_state]
    apply s4_gen_progress_transport oracle low nonce total start _ _ (remaining + 64 * passes)
      (gen_branch_memory _ _ _ _) (gen_branch_register _ _ _ _ _) (gen_branch_register _ _ _ _ _)
    apply s4_gen_progress_calls oracle low nonce total start aligned window bound 64 state
      (remaining + 64 * passes) (by omega)
    rwa [show remaining + 64 * passes + 64 = remaining + 64 * (passes + 1) by omega]

/-- The whole generator: 23,832 passes of 64 calls, from the seed address in x18 and the trapdoor
base in x9 (nonce base `heap + 1811939584`). -/
theorem s4_generator_progress (oracle : Oracle) (state : MachineState) (seed heap : Nat)
    (seeds : state.getReg .x18 = BitVec.ofNat 64 seed) (base : state.getReg .x9 = BitVec.ofNat 64 heap)
    (aligned : seed % 8 = 0) (low : 168 ≤ seed) (window : seed + 32 ≤ heap + 1811939560)
    (bound : heap + 1811939584 + 268443648 ≤ 2^64) :
    S4GenProgress oracle (seed - 168) (heap + 1811939584) 1525248 state
      (checkEvaluation oracle (s4Generator state 23832)).1 0 := by
  unfold s4Generator
  apply s4_gen_progress_passes oracle (seed - 168) (heap + 1811939584) 1525248 state (by omega)
    (by omega) (by omega) 23832 _ 0 (by norm_num)
  rw [show 0 + 64 * 23832 = 1525248 by norm_num]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [s4_gen_setup_input, seeds, gen_minus seed low]
  · intro _
    rw [gen_setup_output, base, show signExtend12 (56 : BitVec 12) = BitVec.ofNat 64 56 by decide,
      ← BitVec.ofNat_add, ← BitVec.ofNat_add]
    congr 1
    omega
  · intro q _ _ _
    exact s3_byte_memory _ _ (s4_gen_setup_memory state) _
  · intro q lowq highq
    exfalso
    omega

/-! ### Published statements -/

theorem s4_gen_calls_register (oracle : Oracle) (count : Nat) :
    ∀ (state : MachineState) (reg : Reg), reg ≠ .x12 →
      (checkEvaluation oracle (s4GenCalls state count)).1.getReg reg = state.getReg reg := by
  induction count with
  | zero =>
    intro state reg _
    rw [s4GenCalls, gen_evaluation_pure_state]
  | succ count ih =>
    intro state reg other
    rw [s4_gen_calls_state, ih _ reg other, s4_gen_next_register oracle state reg other]

theorem s4_gen_passes_register (oracle : Oracle) (passes : Nat) :
    ∀ (state : MachineState) (reg : Reg), reg ≠ .x12 →
      (checkEvaluation oracle (s4GenPasses state passes)).1.getReg reg = state.getReg reg := by
  induction passes with
  | zero =>
    intro state reg _
    rw [s4GenPasses, gen_evaluation_pure_state]
  | succ passes ih =>
    intro state reg other
    rw [s4GenPasses, gen_evaluation_state, ih _ reg other, s4_gen_pass_state, gen_branch_register,
      s4_gen_calls_register oracle 64 state reg other]

/-- The generator changes only x6, x10, x11, x12 and x13 among the registers. -/
theorem s4_generator_register (oracle : Oracle) (state : MachineState) (passes : Nat) (reg : Reg)
    (h6 : reg ≠ .x6) (h10 : reg ≠ .x10) (h11 : reg ≠ .x11) (h12 : reg ≠ .x12) (h13 : reg ≠ .x13) :
    (checkEvaluation oracle (s4Generator state passes)).1.getReg reg = state.getReg reg := by
  unfold s4Generator
  rw [s4_gen_passes_register oracle passes _ reg h12, gen_setup_register state reg h6 h10 h11 h12 h13]

/-- After the generator, x6 holds the nonce base minus 24 and x10 the input block. -/
theorem s4_generator_pointers (oracle : Oracle) (state : MachineState) (passes seed heap : Nat)
    (seeds : state.getReg .x18 = BitVec.ofNat 64 seed) (base : state.getReg .x9 = BitVec.ofNat 64 heap)
    (low : 168 ≤ seed) :
    (checkEvaluation oracle (s4Generator state passes)).1.getReg .x6 =
      BitVec.ofNat 64 (heap + 1811939560) ∧
    (checkEvaluation oracle (s4Generator state passes)).1.getReg .x10 =
      BitVec.ofNat 64 (seed - 168) := by
  unfold s4Generator
  rw [s4_gen_passes_register oracle passes _ .x6 (by decide),
    s4_gen_passes_register oracle passes _ .x10 (by decide)]
  exact ⟨s4_gen_setup_limit state heap base, by rw [s4_gen_setup_input, seeds, gen_minus seed low]⟩

theorem s4_gen_calls_queries (oracle : Oracle) (count : Nat) :
    ∀ state : MachineState, (checkEvaluation oracle (s4GenCalls state count)).2 = count := by
  induction count with
  | zero =>
    intro state
    rw [s4GenCalls, gen_evaluation_pure_calls]
  | succ count ih =>
    intro state
    rw [s4GenCalls, gen_evaluation_calls, s4_gen_call_queries, s4_gen_call_state, ih]
    omega

theorem s4_gen_passes_queries (oracle : Oracle) (passes : Nat) :
    ∀ state : MachineState, (checkEvaluation oracle (s4GenPasses state passes)).2 = 64 * passes := by
  induction passes with
  | zero =>
    intro state
    rw [s4GenPasses, gen_evaluation_pure_calls]
  | succ passes ih =>
    intro state
    rw [s4GenPasses, gen_evaluation_calls, ih, s4GenPass, gen_evaluation_calls,
      s4_gen_calls_queries, gen_evaluation_pure_calls]
    omega

/-- One permutation query per generator call. -/
theorem s4_generator_queries (oracle : Oracle) (state : MachineState) :
    (checkEvaluation oracle (s4Generator state 23832)).2 = 1525248 := by
  unfold s4Generator
  rw [s4_gen_passes_queries]

/-- Memory after the generator, for a fixed oracle: only the counter word and the reply region
`[heap + 1811939560, heap + 2080383208)` change. -/
theorem s4_generator_preserves (oracle : Oracle) (state : MachineState) (seed heap address count : Nat)
    (seeds : state.getReg .x18 = BitVec.ofNat 64 seed) (base : state.getReg .x9 = BitVec.ofNat 64 heap)
    (aligned : seed % 8 = 0) (low : 168 ≤ seed) (window : seed + 32 ≤ heap + 1811939560)
    (bound : heap + 1811939584 + 268443648 ≤ 2^64) (fits : address + count ≤ 2^64)
    (counter : address + count ≤ seed - 168 ∨ seed - 160 ≤ address)
    (outside : address + count ≤ heap + 1811939560 ∨ heap + 2080383232 ≤ address) :
    readBuffer (checkEvaluation oracle (s4Generator state 23832)).1 address count =
      readBuffer state address count :=
  s3_read_congr _ _ _ _ count (fun i hi =>
    (s4_generator_progress oracle state seed heap seeds base aligned low window bound).outside _
      (by omega) (by omega) (by omega))

/-- The input window of the actual generator: 160 zero bytes, then the seed. -/
private theorem gen_window (state : MachineState) (seedAddress : Nat) (seed : BitVec 256)
    (low : 168 ≤ seedAddress)
    (seeded : readBuffer state seedAddress 32 = seed)
    (clean : ∀ i < 168, state.getByte (BitVec.ofNat 64 (seedAddress - 168 + i)) = 0) :
    (readBuffer state (seedAddress - 168 + 8) 192).toNat = 2^(8*160) * seed.toNat := by
  have split := s3_read_append state (seedAddress - 168 + 8) 160 32 192 seedAddress rfl (by omega)
  have zero : (readBuffer state (seedAddress - 168 + 8) 160).toNat = 0 :=
    gen_read_zero state _ 160 (fun i hi => by
      have byte := clean (8 + i) (by omega)
      rw [show seedAddress - 168 + (8 + i) = seedAddress - 168 + 8 + i by omega] at byte
      exact byte)
  rw [split, zero, seeded, Nat.zero_add]

private theorem gen_block_input (seed : BitVec 256) (window k : Nat)
    (same : window = 2^(8*160) * seed.toNat) :
    s4GenBlock 6106911008 window k = s4GenInput seed k := by
  unfold s4GenBlock s4GenInput
  rw [same, show 6106911008 - 24 + 176 * k = 6106910984 + 176 * k by omega]
  congr 1
  ring

/-- Memory after the generator, for a fixed oracle: every nonce slot holds its generated nonce. -/
theorem s4_generator_nonce (oracle : Oracle) (state : MachineState) (seed : BitVec 256)
    (seeds : state.getReg .x18 = BitVec.ofNat 64 5368713248)
    (base : state.getReg .x9 = BitVec.ofNat 64 4294971424)
    (seeded : readBuffer state 5368713248 32 = seed)
    (clean : ∀ i < 168, state.getByte (BitVec.ofNat 64 (5368713248 - 168 + i)) = 0) (index : Index) :
    readBuffer (checkEvaluation oracle (s4Generator state 23832)).1 (6106911008 + 16 * index.val) 16 =
      s4GenNonce oracle.permutation seed index := by
  have progress := s4_generator_progress oracle state 5368713248 4294971424 seeds base (by decide)
    (by decide) (by decide) (by decide)
  have window := gen_window state 5368713248 seed (by decide) seeded clean
  have indexBound : index.val < 2^24 := index.isLt
  have read := read_serialized_slice (checkEvaluation oracle (s4Generator state 23832)).1
    (oracle.permutation (s4GenBlock (4294971424 + 1811939584)
      (readBuffer state (5368713248 - 168 + 8) 192).toNat (index.val / 11)))
    (6106911008 + 16 * index.val) (24 + 16 * (index.val % 11)) 16 (fun j hj => by
      rw [progress.done _ (by omega) (by omega),
        show (6106911008 + 16 * index.val + j - (4294971424 + 1811939584)) / 176 = index.val / 11 by
          omega,
        show (6106911008 + 16 * index.val + j - (4294971424 + 1811939584)) % 176 =
          16 * (index.val % 11) + j by omega,
        Nat.add_assoc])
  rw [read, show 4294971424 + 1811939584 = 6106911008 by norm_num, gen_block_input seed _ _ window]
  unfold s4GenNonce
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    show 8 * (24 + 16 * (index.val % 11)) = 192 + 128 * (index.val % 11) by omega]

/-! ### Clearing the seed block -/

theorem s6_gen_clear_register_mem (state : MachineState) (reg : Reg) :
    (s6GenClear state).getReg reg = state.getReg reg := by
  cases reg <;> rfl

private theorem clear_store (state : MachineState) (offset : BitVec 12) :
    (execInstrBr state (.SD .x10 .x0 offset)).mem =
      (state.setMem (state.getReg .x10 + signExtend12 offset) 0).mem := rfl

private theorem clear_store_register (state : MachineState) (offset : BitVec 12) (reg : Reg) :
    (execInstrBr state (.SD .x10 .x0 offset)).getReg reg = state.getReg reg := by
  cases reg <;> rfl

private theorem clear_store_byte (state : MachineState) (low offset query : Nat)
    (input : state.getReg .x10 = BitVec.ofNat 64 low) (aligned : (low + offset) % 8 = 0)
    (small : offset < 2048) (bound : low + offset + 8 ≤ 2^64) (queryBound : query < 2^64) :
    (execInstrBr state (.SD .x10 .x0 (BitVec.ofNat 12 offset))).getByte (BitVec.ofNat 64 query) =
      if low + offset ≤ query ∧ query < low + offset + 8 then 0
      else state.getByte (BitVec.ofNat 64 query) := by
  rw [s3_byte_memory _ _ (clear_store state _), s3_address _ low offset _ input
    (s3_offset_extend offset small),
    s3_store_byte state (low + offset) 0 query aligned bound queryBound]
  by_cases inside : low + offset ≤ query ∧ query < low + offset + 8
  · rw [if_pos inside, if_pos inside]
    apply BitVec.eq_of_toNat_eq
    simp [extractByte]
  · rw [if_neg inside, if_neg inside]

/-- The five clearing stores zero the counter word and the seed (`[low, low + 8)` and
`[low + 168, low + 200)`) and keep every other byte. -/
theorem s6_gen_clear_byte (state : MachineState) (low query : Nat)
    (input : state.getReg .x10 = BitVec.ofNat 64 low) (aligned : low % 8 = 0)
    (bound : low + 200 ≤ 2^64) (queryBound : query < 2^64) :
    (s6GenClear state).getByte (BitVec.ofNat 64 query) =
      if (low ≤ query ∧ query < low + 8) ∨ (low + 168 ≤ query ∧ query < low + 200) then 0
      else state.getByte (BitVec.ofNat 64 query) := by
  let s1 := execInstrBr state (.SD .x10 .x0 0)
  let s2 := execInstrBr s1 (.SD .x10 .x0 168)
  let s3 := execInstrBr s2 (.SD .x10 .x0 176)
  let s4 := execInstrBr s3 (.SD .x10 .x0 184)
  have p1 : s1.getReg .x10 = BitVec.ofNat 64 low := (clear_store_register _ _ _).trans input
  have p2 : s2.getReg .x10 = BitVec.ofNat 64 low := (clear_store_register _ _ _).trans p1
  have p3 : s3.getReg .x10 = BitVec.ofNat 64 low := (clear_store_register _ _ _).trans p2
  have p4 : s4.getReg .x10 = BitVec.ofNat 64 low := (clear_store_register _ _ _).trans p3
  have b0 (q : Nat) (hq : q < 2^64) := clear_store_byte state low 0 q input (by omega) (by omega)
    (by omega) hq
  have b1 (q : Nat) (hq : q < 2^64) := clear_store_byte s1 low 168 q p1 (by omega) (by omega)
    (by omega) hq
  have b2 (q : Nat) (hq : q < 2^64) := clear_store_byte s2 low 176 q p2 (by omega) (by omega)
    (by omega) hq
  have b3 (q : Nat) (hq : q < 2^64) := clear_store_byte s3 low 184 q p3 (by omega) (by omega)
    (by omega) hq
  have b4 (q : Nat) (hq : q < 2^64) := clear_store_byte s4 low 192 q p4 (by omega) (by omega)
    (by omega) hq
  change (execInstrBr s4 (.SD .x10 .x0 (BitVec.ofNat 12 192))).getByte _ = _
  rw [b4 query queryBound]
  by_cases h4 : low + 192 ≤ query ∧ query < low + 192 + 8
  · rw [if_pos h4, if_pos (Or.inr (by omega))]
  rw [if_neg h4]
  change (execInstrBr s3 (.SD .x10 .x0 (BitVec.ofNat 12 184))).getByte _ = _
  rw [b3 query queryBound]
  by_cases h3 : low + 184 ≤ query ∧ query < low + 184 + 8
  · rw [if_pos h3, if_pos (Or.inr (by omega))]
  rw [if_neg h3]
  change (execInstrBr s2 (.SD .x10 .x0 (BitVec.ofNat 12 176))).getByte _ = _
  rw [b2 query queryBound]
  by_cases h2 : low + 176 ≤ query ∧ query < low + 176 + 8
  · rw [if_pos h2, if_pos (Or.inr (by omega))]
  rw [if_neg h2]
  change (execInstrBr s1 (.SD .x10 .x0 (BitVec.ofNat 12 168))).getByte _ = _
  rw [b1 query queryBound]
  by_cases h1 : low + 168 ≤ query ∧ query < low + 168 + 8
  · rw [if_pos h1, if_pos (Or.inr (by omega))]
  rw [if_neg h1]
  change (execInstrBr state (.SD .x10 .x0 (BitVec.ofNat 12 0))).getByte _ = _
  rw [b0 query queryBound]
  by_cases h0 : low + 0 ≤ query ∧ query < low + 0 + 8
  · rw [if_pos h0, if_pos (Or.inl (by omega))]
  rw [if_neg h0, if_neg (by omega)]

end CommitGolfCandidate
