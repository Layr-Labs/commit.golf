import CommitGolfCandidate.QuadOpeningFooter
import CommitGolfCandidate.PentaCapSpec
import CommitGolfCandidate.Machine

/-! The whole level-7 cap opening run: setup, all records, the table copy, exit. -/

namespace TwoPermutationPrototype.QuadOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
open QOpening (OpeningLayout trapdoorBase proofBase nonceBase indicesBase)

attribute [local simp] QOpening.getReg_setReg MachineState.getReg_setPC

@[local simp] private theorem reg_zero (state : MachineState) : state.getReg .x0 = 0#64 := rfl

structure OpeningABI (s : Submission) extends OpeningLayout s where
  image : s.image .opening = openingImage
  capacity : PENTA_PROOF_CAPACITY ≤ s.sizes.proof
  fuel : 17179934720 ≤ s.steps .opening

def proofLength (positions : Positions) : Nat := capLength positions

/-- Output doublewords: 142 per record, then the 860-doubleword level-7 table (none when empty). -/
def proofWords (positions : Positions) : Nat :=
  if positions.card = 0 then 0 else 142*positions.card+860

def scheduledSteps (positions : Positions) : Nat :=
  if positions.card = 0 then 6 else 71*positions.card+334

def scheduledCycles (positions : Positions) : Nat :=
  if positions.card = 0 then 6 else 211*positions.card+925

structure OpenPhysical (s : Submission) (trapdoor : BitVec (8*s.sizes.trapdoor))
    (positions : Positions) (result : Execution) : Prop where
  success : result.exit = .success
  length : (result.state.getReg .x11).toNat = proofLength positions
  noCalls : result.oracleCalls = 0
  cycles : result.cycles = scheduledCycles positions
  output : Inv (s.initialState .opening (trapdoor, positions)) result.state (proofSource positions)
    (proofWords positions)

theorem beq_shape (state : MachineState) (r₁ r₂ : Reg) (imm : BitVec 13) :
    execInstrBr state (.BEQ r₁ r₂ imm) =
      state.setPC (if state.getReg r₁ == state.getReg r₂ then state.pc + signExtend13 imm else state.pc + 4) := by
  simp only [execInstrBr]
  split <;> rfl

set_option maxRecDepth 100000 in
theorem setup_codes :
    CodeAt 0 [.ADDI .x21 .x15 0] ∧ program[1]? = some (.BEQ .x16 .x0 588) ∧
    CodeAt 148 [.SUB .x11 .x21 .x15, .ADDI .x5 .x0 1, .ADDI .x10 .x0 0] ∧ program[151]? = some .ECALL := by
  decide +kernel

def setupHead (state : MachineState) : MachineState :=
  ([.ADDI .x21 .x15 0] : List Instr).foldl execInstrBr state

def setupBranch (state : MachineState) : MachineState :=
  execInstrBr (setupHead state) (.BEQ .x16 .x0 588)

def exitRun (state : MachineState) : MachineState :=
  ([.SUB .x11 .x21 .x15, .ADDI .x5 .x0 1, .ADDI .x10 .x0 0] : List Instr).foldl execInstrBr state

theorem execute_exit (state : MachineState) (pc : state.pc = BitVec.ofNat 64 (4096+4*148)) (fuel : Nat)
    (coins : Bool) :
    execute openingImage (4+fuel) state coins = pure ⟨.success, exitRun state, 4, 0⟩ := by
  obtain ⟨_, _, c₄, c₅⟩ := setup_codes
  have pure₀ : ([.SUB .x11 .x21 .x15, .ADDI .x5 .x0 1, .ADDI .x10 .x0 0] : List Instr).all pureOp = true := rfl
  have run : Runs state (exitRun state) 3 3 :=
    (runs_pure _ 148 state c₄ pc pure₀).cast rfl (by simp [cost, instructionCycles])
  have pc₃ : (exitRun state).pc = BitVec.ofNat 64 (4096+4*151) := by
    rw [exitRun, pure_pc _ _ pure₀, pc, pc_offset]; rfl
  have halted := fetch_program (exitRun state) 151 .ECALL c₅ pc₃
  have haltFlag : (exitRun state).getReg .x5 = 1 := by simp [exitRun, execInstrBr, signExtend12]
  have successFlag : (exitRun state).getReg .x10 = 0 := by simp [exitRun, execInstrBr, signExtend12]
  rw [show 4+fuel = 3+(fuel+1) by omega, run (fuel+1) coins]
  simp [execute, halted, haltFlag, successFlag, Execution.charge]

theorem exit_length (state : MachineState) :
    (exitRun state).getReg .x11 = state.getReg .x21 - state.getReg .x15 := by
  simp [exitRun, execInstrBr]

theorem exit_memory (state : MachineState) : (exitRun state).mem = state.mem :=
  pure_mem _ _ rfl

theorem initial_registers (s : Submission) (layout : OpeningLayout s)
    (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions) :
    let init := s.initialState .opening (trapdoor, positions)
    init.pc = BitVec.ofNat 64 4096 ∧ init.getReg .x12 = BitVec.ofNat 64 trapdoorBase ∧
      init.getReg .x13 = BitVec.ofNat 64 indicesBase ∧ init.getReg .x15 = BitVec.ofNat 64 proofBase ∧
      init.getReg .x16 = BitVec.ofNat 64 positions.card :=
  ⟨rfl, congrArg (BitVec.ofNat 64) layout.trapdoor, congrArg (BitVec.ofNat 64) layout.indices,
    congrArg (BitVec.ofNat 64) layout.proof, rfl⟩

theorem setup_head (state : MachineState) (pc : state.pc = BitVec.ofNat 64 4096) :
    Runs state (setupHead state) 1 1 ∧ (setupHead state).pc = BitVec.ofNat 64 (4096+4*1) ∧
      (setupHead state).mem = state.mem ∧ (setupHead state).getReg .x15 = state.getReg .x15 ∧
      (setupHead state).getReg .x21 = state.getReg .x15 ∧
      ∀ r, r ≠ .x15 → r ≠ .x21 → (setupHead state).getReg r = state.getReg r := by
  obtain ⟨c₁, _, _, _⟩ := setup_codes
  have pure₀ : ([.ADDI .x21 .x15 0] : List Instr).all pureOp = true := rfl
  refine ⟨runs_pure _ 0 state c₁ pc pure₀, ?_, pure_mem _ _ pure₀, ?_, ?_, ?_⟩
  · rw [setupHead, pure_pc _ _ pure₀, pc]; rfl
  · simp [setupHead, execInstrBr, signExtend12]
  · simp [setupHead, execInstrBr, signExtend12]
  · intro r a b
    simp [setupHead, execInstrBr, Ne.symm a, Ne.symm b]

theorem setup_branch (state : MachineState) (pc : (setupHead state).pc = BitVec.ofNat 64 (4096+4*1)) :
    Runs (setupHead state) (setupBranch state) 1 1 ∧
      (setupBranch state).pc = (if (setupHead state).getReg .x16 = 0#64 then BitVec.ofNat 64 (4096+4*148)
        else BitVec.ofNat 64 (4096+4*2)) ∧
      (setupBranch state).mem = (setupHead state).mem ∧
      ∀ r, (setupBranch state).getReg r = (setupHead state).getReg r := by
  obtain ⟨_, c₂, _, _⟩ := setup_codes
  have shape := beq_shape (setupHead state) .x16 .x0 588
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro fuel coins
    rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ (fetch_program _ 1 _ c₂ pc) rfl]
    rfl
  · rw [setupBranch, shape, set_pc_pc, pc, reg_zero]
    by_cases zero : (setupHead state).getReg .x16 = 0#64
    · simp [zero] <;> decide
    · simp [zero] <;> decide
  · rw [setupBranch, shape]; rfl
  · intro r
    rw [setupBranch, shape, MachineState.getReg_setPC]

theorem lui_salts : ((BitVec.ofNat 20 442369).zeroExtend 32 <<< 12).signExtend 64 = BitVec.ofNat 64 1811943424 := by
  decide

theorem nonempty_bound (positions : Positions) (nonempty : positions.card ≠ 0) :
    BitVec.ofNat 64 (proofBase+8*(142*positions.card+860)) - BitVec.ofNat 64 proofBase =
      BitVec.ofNat 64 (proofLength positions) := by
  have card := card_le positions
  have hL : LENGTH = 16777216 := rfl
  have : proofBase = 10804535392 := rfl
  have length : proofLength positions = 1136*positions.card+6880 := by
    unfold proofLength capLength
    simp [nonempty]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, word_lt _ (by omega), word_lt _ (by omega), word_lt _ (by rw [length]; omega), length]
  omega

/-- Empty opening (`positions.card = 0`): branches directly from word 1 to word 148 in 6 cycles. -/
theorem empty_physical (s : Submission) (abi : OpeningABI s)
    (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions) (empty : positions.card = 0) :
    ∃ result : Execution, s.run .opening (trapdoor, positions) = pure result ∧
      OpenPhysical s trapdoor positions result := by
  let init := s.initialState .opening (trapdoor, positions)
  have budget : 6 ≤ s.steps .opening := le_trans (by decide) abi.fuel
  obtain ⟨pc₀, _, _, _, count⟩ := initial_registers s abi.toOpeningLayout trapdoor positions
  obtain ⟨run₁, pc₁, mem₁, x15, x21, keep₁⟩ := setup_head init pc₀
  obtain ⟨run₂, pc₂, mem₂, keep₂⟩ := setup_branch init pc₁
  have zero : (setupHead init).getReg .x16 = 0#64 := by
    rw [keep₁ .x16 (by decide) (by decide), count, empty]
  have pc₂' : (setupBranch init).pc = BitVec.ofNat 64 (4096+4*148) := by rw [pc₂, if_pos zero]
  let result : Execution := ⟨.success, exitRun (setupBranch init), 6, 0⟩
  refine ⟨result, ?_, ⟨rfl, ?_, rfl, by simp [result, scheduledCycles, empty], ?_⟩⟩
  · change execute (s.image .opening) (s.steps .opening) init true = pure result
    rw [abi.image, show s.steps .opening = 2+(4+(s.steps .opening-6)) by omega,
      (run₁.trans run₂) (4+(s.steps .opening-6)) true, execute_exit _ pc₂']
    simp [result, Execution.charge]
  · show ((exitRun (setupBranch init)).getReg .x11).toNat = _
    rw [exit_length, keep₂, keep₂, x15, x21]
    simp [proofLength, capLength, empty]
  · refine ⟨fun a _ _ _ => ?_, fun u h => by simp [proofWords, empty] at h⟩
    have same : (exitRun (setupBranch init)).mem = init.mem := by
      rw [exit_memory, mem₂, mem₁]
    exact congrFun same _

/-- The records and the table copy, after the setup. -/
def bodyTrace (positions : Positions) (state : MachineState) : OracleComp World MachineState := do
  let t ← recordsTrace positions positions.card 0 (setupRun state)
  footerTrace positions.card t

/-- Non-empty setup, record loop (7 forward and 7 inverse calls per record), the permutation table
copy and exit, from any `EntryAt` state at word 11. With a fixed oracle it emits the honest proof. -/
theorem body_from_record_at (s : Submission) (abi : OpeningABI s)
    (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions) (state : MachineState)
    (nonempty : positions.card ≠ 0)
    (entry : EntryAt (s.initialState .opening (trapdoor, positions)) state positions)
    (fuel : Nat) :
    execute openingImage (71*positions.card+334+fuel) state true =
        (fun u => (⟨.success, u, 211*positions.card+925, 14*positions.card+84⟩ : Execution)) <$>
          bodyTrace positions state ∧
      (∀ z ∈ support (bodyTrace positions state), (z.getReg .x11).toNat = proofLength positions) ∧
      ∀ o : Oracle,
        OpenPhysical s trapdoor positions
          ⟨.success, fixedFooter o positions.card (fixedRecords o positions positions.card 0 (setupRun state)),
            scheduledCycles positions, 0⟩ ∧
        fixedOracleRun o (bodyTrace positions state) =
          Pure.pure (fixedFooter o positions.card (fixedRecords o positions positions.card 0 (setupRun state))) := by
  have card := card_le positions
  have hL : LENGTH = 16777216 := rfl
  have pb : proofBase = 10804535392 := rfl
  let init := s.initialState .opening (trapdoor, positions)
  obtain ⟨run₁, regs₁, inv₁⟩ := setup_step init state positions nonempty entry
  have at₁ : RecAt init positions 0 (setupRun state) := by
    refine ⟨regs₁, fun a lo hi al => ?_⟩
    have := inv₁.input a lo hi al
    exact this
  have length : proofLength positions = 1136*positions.card+6880 := by
    unfold proofLength capLength
    simp [nonempty]
  have tableAt (t : MachineState) (at_ : RecAt init positions positions.card t) :
      t.pc = BitVec.ofNat 64 (4096+4*106) ∧ t.getReg .x9 = BitVec.ofNat 64 trapdoorBase ∧
      t.getReg .x21 = TwoPermutationPrototype.RV64.wordAddress (tableWord positions.card) ∧
      t.getReg .x15 = BitVec.ofNat 64 proofBase := by
    refine ⟨by simpa using at_.regs.pc, at_.regs.heap, ?_, at_.regs.begin⟩
    rw [at_.regs.dest]; unfold TwoPermutationPrototype.RV64.wordAddress tableWord
    apply congrArg (BitVec.ofNat 64); omega
  have lengthReg : ∀ z ∈ support (bodyTrace positions state), (z.getReg .x11).toNat = proofLength positions := by
    intro z hz
    simp only [bodyTrace, mem_support_bind_iff] at hz
    obtain ⟨t, ht, hz⟩ := hz
    have at_ := records_post s abi.toOpeningLayout trapdoor positions positions.card 0 _ t (by omega) at₁ ht
    simp only [Nat.zero_add] at at_
    obtain ⟨_, heap, to_, begin⟩ := tableAt t at_
    rw [footer_length_reg positions.card (by omega) t z heap to_ hz, begin]
    have e : TwoPermutationPrototype.RV64.wordAddress (tableWord positions.card + 20*42) + signExtend12 160 =
        BitVec.ofNat 64 (proofBase+8*(142*positions.card+860)) := by
      unfold TwoPermutationPrototype.RV64.wordAddress tableWord
      rw [show signExtend12 (160 : BitVec 12) = BitVec.ofNat 64 160 by decide, ← BitVec.ofNat_add]
      apply congrArg (BitVec.ofNat 64)
      omega
    rw [e, nonempty_bound positions nonempty, word_lt _ (by rw [length]; omega)]
  refine ⟨?_, lengthReg, fun o => ?_⟩
  · rw [show 71*positions.card+334+fuel = 24+(71*positions.card+(310+fuel)) by omega,
      run₁ (71*positions.card+(310+fuel)) true,
      records_exec s abi.toOpeningLayout trapdoor positions positions.card 0 _ (setupRun state) (by omega) at₁]
    simp only [bodyTrace, map_bind, bind_assoc]
    apply bind_congr_of_forall_mem_support; intro t ht
    have at_ := records_post s abi.toOpeningLayout trapdoor positions positions.card 0 _ t (by omega) at₁ ht
    simp only [Nat.zero_add] at at_
    obtain ⟨pcT, heap, to_, _⟩ := tableAt t at_
    rw [footer_exec positions.card (by omega) t pcT heap to_ fuel]
    simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp, pure_bind]
    apply bind_congr; intro u
    simp [Execution.charge]
    omega
  · obtain ⟨atF, invF⟩ := records_inv o s abi.toOpeningLayout trapdoor positions positions.card 0 _ (by omega) at₁
      (by simpa using inv₁)
    simp only [Nat.zero_add] at atF invF
    let t := fixedRecords o positions positions.card 0 (setupRun state)
    obtain ⟨_, heap, to_, _⟩ := tableAt t atF
    have member : fixedFooter o positions.card t ∈ support (bodyTrace positions state) := by
      apply writer_support (o.world.withAddCost Oracle.callCost) _ (fixedFooter o positions.card t, (14*positions.card+84 : Nat))
      change (_, _) ∈ support (o.run (bodyTrace positions state))
      rw [bodyTrace, oracle_run_bind, records_fixed]
      simp only [pure_bind]
      rw [footer_fixed]
      simp
      rfl
    have words : proofWords positions = 142*positions.card+860 := by simp [proofWords, nonempty]
    refine ⟨⟨rfl, lengthReg _ member, rfl, by simp [scheduledCycles, nonempty], ?_⟩, ?_⟩
    · exact (footer_output o _ t positions positions.card rfl heap to_ invF).cast_count words.symm
    · unfold fixedOracleRun
      rw [bodyTrace, oracle_run_bind, records_fixed]
      simp only [pure_bind]
      rw [footer_fixed]
      rfl

theorem opening_success (s : Submission) (abi : OpeningABI s)
    (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions)
    (result : Execution) (physical : OpenPhysical s trapdoor positions result) :
    s.openingSucceeded result = true := by
  have card := card_le positions
  have bytes : (result.state.getReg .x11).toNat ≤ s.sizes.proof := by
    rw [physical.length]
    refine le_trans ?_ abi.capacity
    have hL : LENGTH = 16777216 := rfl
    unfold proofLength capLength PENTA_PROOF_CAPACITY
    split <;> omega
  simp [Submission.openingSucceeded, physical.success, bytes]

theorem opening_success_of (s : Submission) (abi : OpeningABI s) (positions : Positions)
    (result : Execution) (ok : result.exit = .success)
    (len : (result.state.getReg .x11).toNat = proofLength positions) :
    s.openingSucceeded result = true := by
  have card := card_le positions
  have bytes : (result.state.getReg .x11).toNat ≤ s.sizes.proof := by
    rw [len]
    refine le_trans ?_ abi.capacity
    have hL : LENGTH = 16777216 := rfl
    unfold proofLength capLength PENTA_PROOF_CAPACITY
    split <;> omega
  simp [Submission.openingSucceeded, ok, bytes]

theorem opening_scored_limits (s : Submission) (trapdoor : BitVec (8*s.sizes.trapdoor))
    (positions : Positions) (result : Execution) (physical : OpenPhysical s trapdoor positions result)
    (count : positions.card = BATCH) :
    result.cycles ≤ 27933 ∧ (result.state.getReg .x11).toNat ≤ 152288 := by
  have size : positions.card = 128 := count
  rw [physical.cycles, physical.length]
  simp [scheduledCycles, proofLength, capLength, size]

end TwoPermutationPrototype.QuadOpening
