import CommitGolfCandidate.S3Exec

/-! The nonce generator on the actual interpreter. The appended code starts with nine setup
instructions (PC 1011404) and a loop of 64 unrolled calls `sd x12,0(x10); ecall;
addi x12,x12,-176` (PC 1011440 + 12j) closed by `bgeu x12,x6` (PC 1012208). The image runs
23,832 passes: `9 + 193 * 23832` instructions, `9 + 641 * 23832` cycles and 1,525,248 forward
permutation queries, for every sequence of replies. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-! ### Fetches -/

/-- The three instructions of one generator call; slot 1 is the permutation call. -/
def s4GenCallCode : List Instr :=
  [.SD .x10 .x12 0, .ECALL, .ADDI .x12 .x12 (BitVec.ofNat 12 3920)]

theorem s4_gen_setup_decoded (k : Nat) (hk : k < 9) :
    (s3AppendedWords[k]?).bind decodeInstruction =
      some (.base ((s4GenSetupInstructions[k]?).getD .EBREAK)) := by
  interval_cases k <;> rfl

theorem s4_gen_call_decoded (j i : Nat) (hj : j < 64) (hi : i < 3) :
    (s3AppendedWords[9 + 3 * j + i]?).bind decodeInstruction =
      some (.base ((s4GenCallCode[i]?).getD .EBREAK)) := by
  interval_cases j <;> interval_cases i <;> rfl

theorem s4_gen_branch_decoded :
    (s3AppendedWords[201]?).bind decodeInstruction =
      some (.base (.BGEU .x12 .x6 (BitVec.ofNat 13 7424))) := by
  rfl

theorem s4_image_gen_setup (k : Nat) (hk : k < 9) (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (1011404 + 4 * k)) :
    fetch (submission.image .commit) state =
      some (.base ((s4GenSetupInstructions[k]?).getD .EBREAK)) :=
  s3_image_word k _ state (by omega) pc (s4_gen_setup_decoded k hk)

theorem s4_image_gen_call (j i : Nat) (hj : j < 64) (hi : i < 3) (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (1011440 + 12 * j + 4 * i)) :
    fetch (submission.image .commit) state = some (.base ((s4GenCallCode[i]?).getD .EBREAK)) := by
  apply s3_image_word (9 + 3 * j + i) _ state (by omega) _ (s4_gen_call_decoded j i hj hi)
  rw [pc]
  congr 1
  omega

theorem s4_image_gen_branch (state : MachineState) (pc : state.pc = BitVec.ofNat 64 1012208) :
    fetch (submission.image .commit) state =
      some (.base (.BGEU .x12 .x6 (BitVec.ofNat 13 7424))) := by
  apply s3_image_word 201 _ state (by omega) _ s4_gen_branch_decoded
  rw [pc]

/-! ### Arithmetic and register frames -/

theorem s4_pc_next (pc : Word) (start k target : Nat) (h : pc = BitVec.ofNat 64 start)
    (sum : start + k = target) : pc + BitVec.ofNat 64 k = BitVec.ofNat 64 target := by
  rw [h, ← sum, BitVec.ofNat_add]

theorem s4_pointer_nat (register : Word) (address : Nat)
    (value : register = BitVec.ofNat 64 address) (bounded : address ≤ MEMORY_BYTES) :
    register.toNat = address := by
  rw [value, BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  dsimp [MEMORY_BYTES] at bounded
  omega

/-- Adding the sign-extended immediate `-offset`. -/
theorem s4_ofNat_sub (value offset : Nat) (low : offset ≤ value) (small : offset ≤ 4096) :
    BitVec.ofNat 64 value + BitVec.ofNat 64 (2 ^ 64 - offset) = BitVec.ofNat 64 (value - offset) := by
  rw [← BitVec.ofNat_add]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, Nat.reducePow]
  omega

theorem s4_sext_168 : signExtend12 (BitVec.ofNat 12 3928) = BitVec.ofNat 64 (2 ^ 64 - 168) := by
  decide

theorem s4_sext_176 : signExtend12 (BitVec.ofNat 12 3920) = BitVec.ofNat 64 (2 ^ 64 - 176) := by
  decide

theorem s4_lui_bound :
    (((442368 : BitVec 20).zeroExtend 32 <<< 12 : BitVec 32)).signExtend 64 =
      BitVec.ofNat 64 1811939328 := by
  decide

theorem s4_lui_top :
    (((507906 : BitVec 20).zeroExtend 32 <<< 12 : BitVec 32)).signExtend 64 =
      BitVec.ofNat 64 2080382976 := by
  decide

theorem s4_reply_register (state : MachineState) (answer : BitVec PERMUTATION_WIDTH) (reg : Reg) :
    (s3PermReply state answer).getReg reg = state.getReg reg :=
  writeBits_register _ _ _ reg

theorem s4_store_register (state : MachineState) (reg : Reg) :
    (execInstrBr state (.SD .x10 .x12 0)).getReg reg = state.getReg reg := by
  cases reg <;> rfl

theorem s4_step_register (state : MachineState) (reg : Reg) (h12 : reg ≠ .x12) :
    (execInstrBr state (.ADDI .x12 .x12 (BitVec.ofNat 12 3920))).getReg reg = state.getReg reg := by
  cases reg <;> first | exact absurd rfl h12 | rfl

theorem s4_branch_register (state : MachineState) (reg : Reg) :
    (execInstrBr state (.BGEU .x12 .x6 (BitVec.ofNat 13 7424))).getReg reg = state.getReg reg := by
  simp only [execInstrBr]
  split <;> simp only [MachineState.getReg_setPC]

/-! ### One call -/

/-- Final state of one generator call for its reply. -/
def s4GenCallResult (state : MachineState) (answer : BitVec PERMUTATION_WIDTH) : MachineState :=
  execInstrBr (s3PermReply (execInstrBr state (.SD .x10 .x12 0)) answer)
    (.ADDI .x12 .x12 (BitVec.ofNat 12 3920))

theorem s4_gen_call_support (state next : MachineState)
    (reachable : next ∈ support (s4GenCall state)) :
    ∃ answer, next = s4GenCallResult state answer := by
  simp only [s4GenCall, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reachable
  obtain ⟨answer, _, rfl⟩ := reachable
  exact ⟨answer, rfl⟩

theorem s4_gen_result_register (state : MachineState) (answer : BitVec PERMUTATION_WIDTH)
    (reg : Reg) (h12 : reg ≠ .x12) :
    (s4GenCallResult state answer).getReg reg = state.getReg reg := by
  rw [s4GenCallResult, s4_step_register _ _ h12, s4_reply_register, s4_store_register]

set_option maxHeartbeats 8000000 in
/-- Call `j` of a pass: counter store, forward query on `[x10, x10 + 200)` with the reply at x12,
step down by 176. Three instructions, ten cycles, one query. -/
theorem s4_gen_call_execute (j : Nat) (hj : j < 64) (state : MachineState) (input reply : Nat)
    (pc : state.pc = BitVec.ofNat 64 (1011440 + 12 * j)) (ready : S3PermReady state)
    (inputReg : state.getReg .x10 = BitVec.ofNat 64 input)
    (replyReg : state.getReg .x12 = BitVec.ofNat 64 reply)
    (inputAligned : input % 8 = 0) (replyAligned : reply % 8 = 0) (replyLow : 176 ≤ reply)
    (inputBound : input + 200 ≤ MEMORY_BYTES) (replyBound : reply + 200 ≤ MEMORY_BYTES)
    (fuel : Nat) :
    execute (submission.image .commit) (3 + fuel) state true =
      (do let next ← s4GenCall state
          let result ← execute (submission.image .commit) fuel next true
          return result.charge 10 1) ∧
    (∀ answer, (s4GenCallResult state answer).pc = BitVec.ofNat 64 (1011440 + 12 * (j + 1))) ∧
    (∀ answer, (s4GenCallResult state answer).getReg .x12 = BitVec.ofNat 64 (reply - 176)) := by
  have store := s3_straight_execute (submission.image .commit) [.SD .x10 .x12 0] 1
    (1011440 + 12 * j) state (1 + (1 + fuel)) true rfl pc (by decide)
    (fun k bound current currentPC => by
      have fetched := s4_image_gen_call j k hj (by omega) current currentPC
      interval_cases k <;> exact fetched)
    (fun k bound => by
      interval_cases k
      exact s3_access_valid _ _ input 0 inputReg rfl inputAligned (by decide) (by omega))
  have storeRun : execute (submission.image .commit) (1 + (1 + (1 + fuel))) state true =
      (do let result ← execute (submission.image .commit) (1 + (1 + fuel))
            (execInstrBr state (.SD .x10 .x12 0)) true
          return result.charge 1 0) := store.1
  have storePC : (execInstrBr state (.SD .x10 .x12 0)).pc =
      BitVec.ofNat 64 (1011440 + 12 * j + 4 * 1) := store.2
  have stored (reg : Reg) : (execInstrBr state (.SD .x10 .x12 0)).getReg reg = state.getReg reg :=
    s4_store_register state reg
  have storedReady : S3PermReady (execInstrBr state (.SD .x10 .x12 0)) :=
    ⟨(stored .x5).trans ready.1, (stored .x11).trans ready.2.1, (stored .x13).trans ready.2.2⟩
  have call := s3_perm_call (submission.image .commit) (execInstrBr state (.SD .x10 .x12 0))
    (1 + fuel) true (s4_image_gen_call j 1 hj (by decide) _ storePC) storedReady
    (by rw [s4_pointer_nat _ input ((stored .x10).trans inputReg) (by omega)]; exact inputAligned)
    (by rw [s4_pointer_nat _ reply ((stored .x12).trans replyReg) (by omega)]; exact replyAligned)
    (by rw [s4_pointer_nat _ input ((stored .x10).trans inputReg) (by omega)]; exact inputBound)
    (by rw [s4_pointer_nat _ reply ((stored .x12).trans replyReg) (by omega)]; exact replyBound)
  have repliedPC (answer : BitVec PERMUTATION_WIDTH) :
      (s3PermReply (execInstrBr state (.SD .x10 .x12 0)) answer).pc =
        BitVec.ofNat 64 (1011440 + 12 * j + 8) := by
    show (execInstrBr state (.SD .x10 .x12 0)).pc + 4 = _
    exact s4_pc_next _ _ 4 _ storePC (by omega)
  have step (answer : BitVec PERMUTATION_WIDTH) :=
    s3_straight_execute (submission.image .commit) [.ADDI .x12 .x12 (BitVec.ofNat 12 3920)] 1
      (1011440 + 12 * j + 8) (s3PermReply (execInstrBr state (.SD .x10 .x12 0)) answer) fuel true
      rfl (repliedPC answer) (by decide)
      (fun k bound current currentPC => by
        have fetched := s4_image_gen_call j (2 + k) hj (by omega) current
          (by rw [currentPC]; congr 1; omega)
        interval_cases k <;> exact fetched)
      (fun k bound => by interval_cases k; rfl)
  have stepRun (answer : BitVec PERMUTATION_WIDTH) :
      execute (submission.image .commit) (1 + fuel)
        (s3PermReply (execInstrBr state (.SD .x10 .x12 0)) answer) true =
      (do let result ← execute (submission.image .commit) fuel (s4GenCallResult state answer) true
          return result.charge 1 0) := (step answer).1
  refine ⟨?_, fun answer => ?_, fun answer => ?_⟩
  · rw [show 3 + fuel = 1 + (1 + (1 + fuel)) by omega, storeRun, call]
    simp only [s4GenCall, bind_assoc, pure_bind]
    refine bind_congr fun answer => ?_
    rw [stepRun answer]
    simp only [bind_assoc, pure_bind]
    refine bind_congr fun result => ?_
    simp [Execution.charge] <;> omega
  · rw [show 1011440 + 12 * (j + 1) = 1011440 + 12 * j + 8 + 4 * 1 by omega]
    exact (step answer).2
  · show (s3PermReply (execInstrBr state (.SD .x10 .x12 0)) answer).getReg .x12 +
      signExtend12 (BitVec.ofNat 12 3920) = _
    rw [s4_reply_register, stored, replyReg, s4_sext_176]
    exact s4_ofNat_sub reply 176 replyLow (by decide)

/-! ### Calls, passes and the whole generator -/

/-- Calls `j, j+1, ..., j+count-1` of a pass; the reply address drops by 176 per call. -/
theorem s4_gen_calls_execute (count : Nat) :
    ∀ (j : Nat) (state : MachineState) (input rest : Nat),
    j + count ≤ 64 →
    state.pc = BitVec.ofNat 64 (1011440 + 12 * j) → S3PermReady state →
    state.getReg .x10 = BitVec.ofNat 64 input →
    state.getReg .x12 = BitVec.ofNat 64 (rest + 176 * count) →
    input % 8 = 0 → rest % 8 = 0 → input + 200 ≤ MEMORY_BYTES →
    rest + 176 * count + 200 ≤ MEMORY_BYTES → ∀ fuel : Nat,
    execute (submission.image .commit) (3 * count + fuel) state true =
      (do let called ← s4GenCalls state count
          let result ← execute (submission.image .commit) fuel called true
          return result.charge (10 * count) count) ∧
    ∀ called ∈ support (s4GenCalls state count),
      called.pc = BitVec.ofNat 64 (1011440 + 12 * (j + count)) ∧
      called.getReg .x12 = BitVec.ofNat 64 rest ∧
      ∀ reg : Reg, reg ≠ .x12 → called.getReg reg = state.getReg reg := by
  induction count with
  | zero =>
    intro j state input rest _ pc _ _ reply _ _ _ _ fuel
    refine ⟨by simp [s4GenCalls, Execution.charge], ?_⟩
    intro called reachable
    simp only [s4GenCalls, support_pure, Set.mem_singleton_iff] at reachable
    subst reachable
    refine ⟨by rw [Nat.add_zero]; exact pc, by rw [reply, Nat.mul_zero, Nat.add_zero],
      fun _ _ => rfl⟩
  | succ count ih =>
    intro j state input rest inside pc ready inputReg reply inputAligned restAligned inputBound
      restBound fuel
    have call := s4_gen_call_execute j (by omega) state input (rest + 176 * (count + 1)) pc ready
      inputReg reply inputAligned (by omega) (by omega) inputBound (by omega) (3 * count + fuel)
    have kept (answer : BitVec PERMUTATION_WIDTH) (reg : Reg) (h12 : reg ≠ .x12 := by decide) :
        (s4GenCallResult state answer).getReg reg = state.getReg reg :=
      s4_gen_result_register state answer reg h12
    have continued (answer : BitVec PERMUTATION_WIDTH) :=
      ih (j + 1) (s4GenCallResult state answer) input rest (by omega) (call.2.1 answer)
        ⟨(kept answer .x5).trans ready.1, (kept answer .x11).trans ready.2.1,
          (kept answer .x13).trans ready.2.2⟩
        ((kept answer .x10).trans inputReg)
        (by rw [call.2.2 answer, show rest + 176 * (count + 1) - 176 = rest + 176 * count by omega])
        inputAligned restAligned inputBound (by omega) fuel
    constructor
    · rw [show 3 * (count + 1) + fuel = 3 + (3 * count + fuel) by omega, call.1]
      simp only [s4GenCalls, bind_assoc]
      refine bind_congr_of_forall_mem_support _ fun reached reachable => ?_
      obtain ⟨answer, rfl⟩ := s4_gen_call_support state reached reachable
      rw [(continued answer).1]
      simp only [bind_assoc, pure_bind]
      refine bind_congr fun called => ?_
      refine bind_congr fun result => ?_
      simp [Execution.charge] <;> omega
    · intro called reachable
      simp only [s4GenCalls, mem_support_bind_iff] at reachable
      obtain ⟨reached, reachedCall, remaining⟩ := reachable
      obtain ⟨answer, rfl⟩ := s4_gen_call_support state reached reachedCall
      have tail := (continued answer).2 called remaining
      refine ⟨by rw [tail.1, show j + 1 + count = j + (count + 1) by omega], tail.2.1,
        fun reg h12 => (tail.2.2 reg h12).trans (kept answer reg h12)⟩

/-- The loop branch: back to the first call exactly while the reply address is at least x6. -/
theorem s4_gen_branch_pc (state : MachineState) (rest limit : Nat)
    (pc : state.pc = BitVec.ofNat 64 1012208)
    (reply : state.getReg .x12 = BitVec.ofNat 64 rest)
    (bound : state.getReg .x6 = BitVec.ofNat 64 limit)
    (restSmall : rest < 2 ^ 64) (limitSmall : limit < 2 ^ 64) :
    (execInstrBr state (.BGEU .x12 .x6 (BitVec.ofNat 13 7424))).pc =
      BitVec.ofNat 64 (if limit ≤ rest then 1011440 else 1012212) := by
  have compared : BitVec.ult (state.getReg .x12) (state.getReg .x6) = decide (rest < limit) := by
    rw [reply, bound]
    simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt restSmall,
      Nat.mod_eq_of_lt limitSmall]
  simp only [execInstrBr, compared, pc]
  by_cases taken : limit ≤ rest
  · have notLess : ¬ rest < limit := by omega
    simp only [notLess, taken, decide_false, Bool.false_eq_true, not_false_eq_true, ↓reduceIte]
    rfl
  · have less : rest < limit := by omega
    simp only [less, taken, decide_true, not_true_eq_false, ↓reduceIte]
    rfl

set_option maxHeartbeats 8000000 in
/-- One pass: 64 calls and the branch, 193 instructions, 641 cycles, 64 queries. -/
theorem s4_gen_pass_execute (state : MachineState) (input limit rest : Nat)
    (pc : state.pc = BitVec.ofNat 64 1011440) (ready : S3PermReady state)
    (inputReg : state.getReg .x10 = BitVec.ofNat 64 input)
    (limitReg : state.getReg .x6 = BitVec.ofNat 64 limit)
    (reply : state.getReg .x12 = BitVec.ofNat 64 (rest + 11264))
    (inputAligned : input % 8 = 0) (restAligned : rest % 8 = 0)
    (inputBound : input + 200 ≤ MEMORY_BYTES) (limitBound : limit ≤ MEMORY_BYTES)
    (restBound : rest + 11464 ≤ MEMORY_BYTES)
    (fuel : Nat) :
    execute (submission.image .commit) (193 + fuel) state true =
      (do let next ← s4GenPass state
          let result ← execute (submission.image .commit) fuel next true
          return result.charge 641 64) ∧
    ∀ next ∈ support (s4GenPass state),
      next.pc = BitVec.ofNat 64 (if limit ≤ rest then 1011440 else 1012212) ∧
      next.getReg .x12 = BitVec.ofNat 64 rest ∧
      ∀ reg : Reg, reg ≠ .x12 → next.getReg reg = state.getReg reg := by
  have calls := s4_gen_calls_execute 64 0 state input rest (by decide) pc ready inputReg
    (by rw [reply]) inputAligned restAligned inputBound (by omega) (1 + fuel)
  have branch (called : MachineState) (reached : called ∈ support (s4GenCalls state 64)) :
      execute (submission.image .commit) (fuel + 1) called true =
        (do let result ← execute (submission.image .commit) fuel
              (execInstrBr called (.BGEU .x12 .x6 (BitVec.ofNat 13 7424))) true
            return result.charge 1 0) :=
    execute_ordinary_step (submission.image .commit) (.base (.BGEU .x12 .x6 (BitVec.ofNat 13 7424)))
      called _ fuel true (s4_image_gen_branch called (calls.2 called reached).1) rfl
  constructor
  · rw [show 193 + fuel = 3 * 64 + (1 + fuel) by omega, calls.1]
    simp only [s4GenPass, bind_assoc, pure_bind]
    refine bind_congr_of_forall_mem_support _ fun called reached => ?_
    rw [Nat.add_comm 1 fuel, branch called reached]
    simp only [bind_assoc, pure_bind]
    refine bind_congr fun result => ?_
    simp [Execution.charge] <;> omega
  · intro next reachable
    simp only [s4GenPass, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reachable
    obtain ⟨called, reached, rfl⟩ := reachable
    have known := calls.2 called reached
    refine ⟨?_, ?_, fun reg h12 => ?_⟩
    · exact s4_gen_branch_pc called rest limit known.1 known.2.1
        ((known.2.2 .x6 (by decide)).trans limitReg)
        (by dsimp [MEMORY_BYTES] at restBound; omega)
        (by dsimp [MEMORY_BYTES] at limitBound; omega)
    · rw [s4_branch_register]
      exact known.2.1
    · rw [s4_branch_register]
      exact known.2.2 reg h12

/-- `passes` passes from the loop head; the last one falls through to PC 1012212. -/
theorem s4_gen_passes_execute (passes : Nat) :
    ∀ (state : MachineState) (input limit : Nat), 0 < passes →
    state.pc = BitVec.ofNat 64 1011440 → S3PermReady state →
    state.getReg .x10 = BitVec.ofNat 64 input →
    state.getReg .x6 = BitVec.ofNat 64 limit →
    state.getReg .x12 = BitVec.ofNat 64 (limit - 176 + 11264 * passes) →
    input % 8 = 0 → limit % 8 = 0 → 176 ≤ limit → input + 200 ≤ MEMORY_BYTES →
    limit + 11264 * passes + 24 ≤ MEMORY_BYTES → ∀ fuel : Nat,
    execute (submission.image .commit) (193 * passes + fuel) state true =
      (do let filled ← s4GenPasses state passes
          let result ← execute (submission.image .commit) fuel filled true
          return result.charge (641 * passes) (64 * passes)) ∧
    ∀ filled ∈ support (s4GenPasses state passes),
      filled.pc = BitVec.ofNat 64 1012212 ∧
      ∀ reg : Reg, reg ≠ .x12 → filled.getReg reg = state.getReg reg := by
  induction passes with
  | zero => intro _ _ _ positive; omega
  | succ passes ih =>
    intro state input limit _ pc ready inputReg limitReg reply inputAligned limitAligned low
      inputBound bound fuel
    have pass (more : Nat) := s4_gen_pass_execute state input limit (limit - 176 + 11264 * passes)
      pc ready inputReg limitReg
      (by rw [reply, show limit - 176 + 11264 * (passes + 1) =
        limit - 176 + 11264 * passes + 11264 by omega]) inputAligned (by omega) inputBound
      (by omega) (by omega) more
    have kept (next : MachineState) (reached : next ∈ support (s4GenPass state)) (reg : Reg)
        (h12 : reg ≠ .x12 := by decide) : next.getReg reg = state.getReg reg :=
      ((pass 0).2 next reached).2.2 reg h12
    rcases Nat.eq_zero_or_pos passes with rfl | positive
    · constructor
      · rw [show 193 * (0 + 1) + fuel = 193 + fuel by omega, (pass fuel).1]
        simp only [s4GenPasses, bind_assoc, pure_bind]
      · intro filled reachable
        simp only [s4GenPasses, bind_pure] at reachable
        refine ⟨?_, ((pass 0).2 filled reachable).2.2⟩
        rw [((pass 0).2 filled reachable).1, if_neg (by omega)]
    · have continued (next : MachineState) (reached : next ∈ support (s4GenPass state)) :=
        ih next input limit positive
          (by rw [((pass 0).2 next reached).1, if_pos (by omega)])
          ⟨(kept next reached .x5).trans ready.1, (kept next reached .x11).trans ready.2.1,
            (kept next reached .x13).trans ready.2.2⟩
          ((kept next reached .x10).trans inputReg) ((kept next reached .x6).trans limitReg)
          ((pass 0).2 next reached).2.1 inputAligned limitAligned low inputBound (by omega) fuel
      constructor
      · rw [show 193 * (passes + 1) + fuel = 193 + (193 * passes + fuel) by omega,
          (pass (193 * passes + fuel)).1]
        simp only [s4GenPasses, bind_assoc]
        refine bind_congr_of_forall_mem_support _ fun next reached => ?_
        rw [(continued next reached).1]
        simp only [bind_assoc, pure_bind]
        refine bind_congr fun filled => ?_
        refine bind_congr fun result => ?_
        simp [Execution.charge] <;> omega
      · intro filled reachable
        rw [s4GenPasses] at reachable
        simp only [mem_support_bind_iff] at reachable
        obtain ⟨next, reached, remaining⟩ := reachable
        have tail := (continued next reached).2 filled remaining
        exact ⟨tail.1, fun reg h12 => (tail.2 reg h12).trans (kept next reached reg h12)⟩

theorem s4_gen_setup_register (state : MachineState) (reg : Reg)
    (h6 : reg ≠ .x6) (h10 : reg ≠ .x10) (h11 : reg ≠ .x11) (h12 : reg ≠ .x12) (h13 : reg ≠ .x13) :
    (s4GenSetup state).getReg reg = state.getReg reg := by
  cases reg <;> first | exact absurd rfl h6 | exact absurd rfl h10 | exact absurd rfl h11 |
    exact absurd rfl h12 | exact absurd rfl h13 | rfl

/-- Registers after the setup, for the seed address `seed` in x18 and the trapdoor base `heap` in
x9: input block `seed - 168`, loop bound `heap + 1811939560`, top reply address
`heap + 2080383032 = (heap + 1811939560) - 176 + 11264 * 23832`. -/
theorem s4_gen_setup_values (state : MachineState) (seed heap : Nat)
    (seedReg : state.getReg .x18 = BitVec.ofNat 64 seed)
    (base : state.getReg .x9 = BitVec.ofNat 64 heap) (low : 168 ≤ seed) :
    (s4GenSetup state).getReg .x11 = 200 ∧ (s4GenSetup state).getReg .x13 = 1 ∧
    (s4GenSetup state).getReg .x10 = BitVec.ofNat 64 (seed - 168) ∧
    (s4GenSetup state).getReg .x6 = BitVec.ofNat 64 (heap + 1811939560) ∧
    (s4GenSetup state).getReg .x12 =
      BitVec.ofNat 64 (heap + 1811939560 - 176 + 11264 * 23832) := by
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · show state.getReg .x18 + signExtend12 (BitVec.ofNat 12 3928) = _
    rw [seedReg, s4_sext_168]
    exact s4_ofNat_sub seed 168 low (by decide)
  · show (((442368 : BitVec 20).zeroExtend 32 <<< 12 : BitVec 32)).signExtend 64 +
      state.getReg .x9 + signExtend12 (232 : BitVec 12) = _
    rw [base, s4_lui_bound, show signExtend12 (232 : BitVec 12) = BitVec.ofNat 64 232 by decide,
      ← BitVec.ofNat_add, ← BitVec.ofNat_add]
    congr 1
    omega
  · show (((507906 : BitVec 20).zeroExtend 32 <<< 12 : BitVec 32)).signExtend 64 +
      state.getReg .x9 + signExtend12 (56 : BitVec 12) = _
    rw [base, s4_lui_top, show signExtend12 (56 : BitVec 12) = BitVec.ofNat 64 56 by decide,
      ← BitVec.ofNat_add, ← BitVec.ofNat_add]
    congr 1
    omega

set_option maxHeartbeats 8000000 in
/-- **The generator**: nine setup instructions and 23,832 passes, `9 + 193 * 23832`
instructions, `9 + 641 * 23832` cycles, 1,525,248 forward permutation queries; it ends at the
seed-block clearing (PC 1012212) with the permutation width and selector set, x10 at the seed
block and x6 at the loop bound. -/
theorem s4_generator_execute (state : MachineState) (seed heap : Nat) (fuel : Nat)
    (pc : state.pc = BitVec.ofNat 64 1011404) (selector : state.getReg .x5 = 0)
    (seedReg : state.getReg .x18 = BitVec.ofNat 64 seed)
    (base : state.getReg .x9 = BitVec.ofNat 64 heap)
    (seedAligned : seed % 8 = 0) (heapAligned : heap % 8 = 0) (low : 168 ≤ seed)
    (seedBound : seed + 32 ≤ MEMORY_BYTES) (bound : heap + 2080383232 ≤ MEMORY_BYTES) :
    execute (submission.image .commit) (9 + 193 * 23832 + fuel) state true =
      (do let filled ← s4Generator state 23832
          let result ← execute (submission.image .commit) fuel filled true
          return result.charge (9 + 641 * 23832) 1525248) ∧
    ∀ filled ∈ support (s4Generator state 23832),
      filled.pc = BitVec.ofNat 64 1012212 ∧ S3PermReady filled ∧
      filled.getReg .x10 = BitVec.ofNat 64 (seed - 168) ∧
      filled.getReg .x6 = BitVec.ofNat 64 (heap + 1811939560) ∧
      ∀ reg : Reg, reg ≠ .x6 → reg ≠ .x10 → reg ≠ .x11 → reg ≠ .x12 → reg ≠ .x13 →
        filled.getReg reg = state.getReg reg := by
  have setup := s3_straight_execute (submission.image .commit) s4GenSetupInstructions 9 1011404
    state (193 * 23832 + fuel) true rfl pc (by decide)
    (fun k bound current currentPC => s4_image_gen_setup k bound current currentPC)
    (fun k bound => by interval_cases k <;> rfl)
  have setupRun : execute (submission.image .commit) (9 + (193 * 23832 + fuel)) state true =
      (do let result ← execute (submission.image .commit) (193 * 23832 + fuel) (s4GenSetup state) true
          return result.charge 9 0) := setup.1
  have setupPC : (s4GenSetup state).pc = BitVec.ofNat 64 1011440 := setup.2
  have values := s4_gen_setup_values state seed heap seedReg base low
  have setupKept (reg : Reg) (h6 : reg ≠ .x6 := by decide) (h10 : reg ≠ .x10 := by decide)
      (h11 : reg ≠ .x11 := by decide) (h12 : reg ≠ .x12 := by decide)
      (h13 : reg ≠ .x13 := by decide) : (s4GenSetup state).getReg reg = state.getReg reg :=
    s4_gen_setup_register state reg h6 h10 h11 h12 h13
  have passes := s4_gen_passes_execute 23832 (s4GenSetup state) (seed - 168) (heap + 1811939560)
    (by decide) setupPC ⟨(setupKept .x5).trans selector, values.1, values.2.1⟩ values.2.2.1
    values.2.2.2.1 values.2.2.2.2 (by omega) (by omega) (by omega) (by omega)
    (Eq.trans_le (by ring) bound) fuel
  constructor
  · rw [Nat.add_assoc, setupRun, passes.1]
    simp only [s4Generator, bind_assoc, pure_bind]
    refine bind_congr fun filled => ?_
    refine bind_congr fun result => ?_
    simp [Execution.charge] <;> omega
  · intro filled reachable
    have known := passes.2 filled reachable
    refine ⟨known.1, ⟨(known.2 .x5 (by decide)).trans ((setupKept .x5).trans selector),
      (known.2 .x11 (by decide)).trans values.1, (known.2 .x13 (by decide)).trans values.2.1⟩,
      (known.2 .x10 (by decide)).trans values.2.2.1, (known.2 .x6 (by decide)).trans values.2.2.2.1,
      fun reg h6 h10 h11 h12 h13 => (known.2 reg h12).trans (setupKept reg h6 h10 h11 h12 h13)⟩

end CommitGolfCandidate
