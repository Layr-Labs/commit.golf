import CommitGolfCandidate.QuadOpeningHyb
import CommitGolfCandidate.PentaCapSpec
import CommitGolfCandidate.Machine

/-! The whole hybrid opening run: setup, all records, the level-13 table copy, exit. -/

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

/-- Output doublewords: 94 per record, then the 352-doubleword level-13 table (none when empty). -/
def proofWords (positions : Positions) : Nat :=
  if positions.card = 0 then 0 else 94*positions.card+352

def scheduledSteps (positions : Positions) : Nat :=
  if positions.card = 0 then 6 else 347*positions.card+749

def scheduledCycles (positions : Positions) : Nat :=
  if positions.card = 0 then 6 else 452*positions.card+749

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
    BitVec.ofNat 64 (proofBase+8*(94*positions.card+352)) - BitVec.ofNat 64 proofBase =
      BitVec.ofNat 64 (proofLength positions) := by
  have card := card_le positions
  have hL : LENGTH = 16777216 := rfl
  have : proofBase = 10804535392 := rfl
  have length : proofLength positions = 752*positions.card+2816 := by
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

set_option maxHeartbeats 4000000 in
/-- Non-empty opening from the hand-over at word 11: jump, setup, all records, the level-13 table
copy and the exit; no oracle calls. -/
theorem body_from_record_at (s : Submission) (abi : OpeningABI s)
    (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions) (state : MachineState)
    (nonempty : positions.card ≠ 0)
    (entry : EntryAt (s.initialState .opening (trapdoor, positions)) state positions)
    (fuel : Nat) :
    ∃ final : MachineState,
      execute openingImage (347*positions.card+749+fuel) state true =
        pure ⟨.success, final, 452*positions.card+749, 0⟩ ∧
      OpenPhysical s trapdoor positions ⟨.success, final, scheduledCycles positions, 0⟩ := by
  let init := s.initialState .opening (trapdoor, positions)
  have card := card_le positions
  have hL : LENGTH = 16777216 := rfl
  have pb := pb_val
  have ib : indicesBase = 6375350304 := rfl
  obtain ⟨cJ, cS, _, _, _, _, _, cT, _, _, cE, cH⟩ := hyb_codes
  -- jump
  let s1 := execInstrBr state hybJump
  have run1 : Runs state s1 1 1 := by
    intro f coins
    rw [Nat.add_comm 1 f, execute_ordinary_step _ _ _ _ _ _ (fetch_program _ 11 _ cJ entry.pc) rfl]
    rfl
  have pc1 : s1.pc = BitVec.ofNat 64 (4096+4*527) := by
    show ((state.setReg .x0 (state.pc+4)).setPC (state.pc + signExtend21 2064)).pc = _
    rw [set_pc_pc, entry.pc]; decide
  have k1 : ∀ r, s1.getReg r = state.getReg r := by intro r; simp [s1, hybJump, execInstrBr]
  -- setup
  let s2 := hybSetup.foldl execInstrBr s1
  have run2 : Runs s1 s2 2 2 := (runs_pure _ _ s1 cS pc1 rfl).cast rfl rfl
  have pc2 : s2.pc = BitVec.ofNat 64 (4096+4*529) := by rw [pure_pc _ _ rfl, pc1, pc_offset]; rfl
  have x18 : s2.getReg .x18 = BitVec.ofNat 64 (indicesBase+8*positions.card) := by
    simp [s2, hybSetup, execInstrBr, k1, entry.left, entry.index]
    rw [shift_count _ (by omega), add_nat]
    apply congrArg (BitVec.ofNat 64); rw [ib]; omega
  have k2 : ∀ r, r ≠ .x18 → s2.getReg r = state.getReg r := by
    intro r h; simp [s2, hybSetup, execInstrBr, Ne.symm h, k1]
  have mem2 : s2.mem = state.mem := by
    rw [pure_mem _ _ rfl]; simp [s1, hybJump, execInstrBr, MachineState.setPC, mem_set_reg]
  have at0 : RecState init positions 0 s2 := by
    refine ⟨⟨?_, ?_, ?_, x18, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [k2 _ (by decide), entry.index]
    · rw [k2 _ (by decide), entry.heap]
    · rw [k2 _ (by decide), entry.begin]
    · rw [k2 _ (by decide), entry.five]
    · rw [k2 _ (by decide), entry.dest]
    · rw [k2 _ (by decide), entry.salts]
    · rw [k2 _ (by decide), entry.width]
    · rw [pc2, if_neg (Ne.symm nonempty)]
    · exact (entry.inv.of_mem mem2).cast_count rfl
  obtain ⟨run3, at3⟩ := records_run s abi.toOpeningLayout trapdoor positions positions.card 0 s2 (by omega) at0
  let s3 := recsRun positions.card s2
  have pc3 : s3.pc = BitVec.ofNat 64 (4096+4*876) := by simpa using at3.pc
  -- table head
  let s4 := ([.LUI .x30 (hybPage 13), .ADD .x30 .x30 .x9] : List Instr).foldl execInstrBr s3
  have run4 : Runs s3 s4 2 2 := (runs_pure _ _ s3 cT pc3 rfl).cast rfl rfl
  have pc4 : s4.pc = BitVec.ofNat 64 (4096+4*878) := by rw [pure_pc _ _ rfl, pc3, pc_offset]; rfl
  have x30 : s4.getReg .x30 = BitVec.ofNat 64 hybTableStart := by
    have h9 : s3.getReg .x9 = BitVec.ofNat 64 trapdoorBase := at3.fixed.x9
    have lui : BitVec.signExtend 64 (BitVec.setWidth 32 (hybPage 13) <<< 12) = BitVec.ofNat 64 (pentaGroupBase 13+40) := by
      decide
    simp [s4, execInstrBr, h9, lui]
    rw [add_nat]; rfl
  have k4 : ∀ r, r ≠ .x30 → s4.getReg r = s3.getReg r := by intro r h; simp [s4, execInstrBr, Ne.symm h]
  have inv4 : Inv init s4 (proofSource positions) (94*positions.card) :=
    (at3.inv.of_mem (pure_mem _ _ rfl)).source_congr (fun u h => by unfold proofSource; rw [if_pos h])
  obtain ⟨run5a, inv5a, pc5a, x21₅a, x30₅a, k5a⟩ := groups_run init positions card 17 le_rfl s4 pc4 x30
    ((k4 _ (by decide)).trans at3.fixed.x21) inv4
  let s5a := (List.replicate 17 hybGroup).flatten.foldl execInstrBr s4
  obtain ⟨run5b, inv5, pc5, x21₅, k5b⟩ := half_run init positions card s5a (pc5a.trans (by decide)) x30₅a x21₅a inv5a
  let s5 := hybHalf.foldl execInstrBr s5a
  have run5 : Runs s4 s5 (42*17+26) (42*17+26) := run5a.trans run5b
  have k5 : ∀ r, r ≠ .x21 → r ≠ .x30 → r ≠ .x31 → s5.getReg r = s4.getReg r := fun r a b c => by
    rw [k5b r a b c, k5a r a b c]
  -- exit
  let s6 := ([.SUB .x11 .x21 .x15, .ADDI .x5 .x0 1, .ADDI .x10 .x0 0] : List Instr).foldl execInstrBr s5
  have run6 : Runs s5 s6 3 3 := (runs_pure _ _ s5 cE pc5 rfl).cast rfl rfl
  have pc6 : s6.pc = BitVec.ofNat 64 (4096+4*1621) := by rw [pure_pc _ _ rfl, pc5]; decide
  have halted := fetch_program s6 1621 .ECALL cH pc6
  have haltFlag : s6.getReg .x5 = 1 := by simp [s6, execInstrBr, signExtend12]
  have successFlag : s6.getReg .x10 = 0 := by simp [s6, execInstrBr, signExtend12]
  have x11 : s6.getReg .x11 = BitVec.ofNat 64 (proofLength positions) := by
    simp only [s6, List.foldl_cons, List.foldl_nil, execInstrBr, QOpening.getReg_setReg, MachineState.getReg_setPC]
    simp only [show (Reg.x5 = Reg.x11 ∧ Reg.x5 ≠ Reg.x0) = False by decide,
      show (Reg.x10 = Reg.x11 ∧ Reg.x10 ≠ Reg.x0) = False by decide, ite_false, ite_true,
      show (Reg.x11 = Reg.x11 ∧ Reg.x11 ≠ Reg.x0) = True by decide]
    rw [x21₅, k5 _ (by decide) (by decide) (by decide), k4 _ (by decide), at3.fixed.x15]
    exact nonempty_bound positions nonempty
  have mem6 : s6.mem = s5.mem := pure_mem _ _ rfl
  refine ⟨s6, ?_, ⟨rfl, ?_, rfl, by simp [scheduledCycles, nonempty], ?_⟩⟩
  · have all := ((((run1.trans run2).trans run3).trans run4).trans (run5.trans run6))
    rw [show 347*positions.card+749+fuel = (1+2+347*positions.card+2+((42*17+26)+3))+(fuel+1) by ring, all (fuel+1) true]
    simp [execute, halted, haltFlag, successFlag, Execution.charge]
    ring
  · rw [x11]
    have : proofLength positions = 752*positions.card+2816 := by unfold proofLength capLength; simp [nonempty]
    rw [word_lt _ (by rw [this]; omega)]
  · have words : proofWords positions = 94*positions.card+352 := by simp [proofWords, nonempty]
    rw [words]
    exact (inv5.of_mem mem6).cast_count (by ring)

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
    result.cycles ≤ 58605 ∧ (result.state.getReg .x11).toNat ≤ 99072 := by
  have size : positions.card = 128 := count
  rw [physical.cycles, physical.length]
  simp [scheduledCycles, proofLength, capLength, size]

end TwoPermutationPrototype.QuadOpening
