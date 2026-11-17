import CommitGolfCandidate.CapCheckLeafImage

/-! Execution of the stage-3 checker leaf on the cap check image: three
checked straight-line segments, two permutation calls with arbitrary replies,
and the return. 90 instructions, 104 cycles, two public queries. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
attribute [local irreducible] readBuffer

/-- At the first ECALL: window built, selectors loaded. -/
def s3LeafFirst (state : MachineState) : MachineState := s3Run s3LeafBuild state

/-- After the first reply was written in place at address 0. -/
def s3LeafMiddle (state : MachineState) (first : BitVec 1600) : MachineState :=
  s3PermutationAnswer (s3LeafFirst state) first

/-- At the second ECALL: nonce and value tail placed around the chaining bytes. -/
def s3LeafSecond (state : MachineState) (first : BitVec 1600) : MachineState :=
  s3Run s3LeafChain (s3LeafMiddle state first)

/-- After the second reply was written at address 0. -/
def s3LeafLast (state : MachineState) (first second : BitVec 1600) : MachineState :=
  s3PermutationAnswer (s3LeafSecond state first) second

/-- At the return instruction: digest copied to scratch, x8 advanced. -/
def s3LeafDone (state : MachineState) (first second : BitVec 1600) : MachineState :=
  s3Run s3LeafFinish (s3LeafLast state first second)

/-- The leaf routine as an oracle computation over arbitrary replies. -/
def capCheckLeaf (state : MachineState) : OracleComp World MachineState := do
  let first ← s3PermutationQuery (readBuffer (s3LeafFirst state) 0 200)
  let second ← s3PermutationQuery (readBuffer (s3LeafSecond state first) 72 200)
  return s3LeafDone state first second

theorem s3_run_register_frame (instructions : List Instr) (intact : Bool)
    (state : MachineState) (reg : Reg) (checked : s3Checked intact instructions = true)
    (targets : List Reg)
    (written : ∀ target ∈ instructions.filterMap s3Target, target ∈ targets)
    (outside : reg ∉ targets) :
    (s3Run instructions state).getReg reg = state.getReg reg :=
  s3_run_register instructions intact state reg checked (fun instruction inside equal =>
    outside (written reg (List.mem_filterMap.mpr ⟨instruction, inside, equal⟩)))

theorem s3_leaf_first_register (state : MachineState) (reg : Reg)
    (outside : reg ∉ [Reg.x6, .x5, .x10, .x11, .x12, .x13]) :
    (s3LeafFirst state).getReg reg = state.getReg reg :=
  s3_run_register_frame s3LeafBuild true state reg s3_leaf_build_checked _ (by decide) outside

theorem s3_leaf_first_selectors (state : MachineState) :
    (s3LeafFirst state).getReg .x5 = 0 ∧ (s3LeafFirst state).getReg .x10 = 0 ∧
    (s3LeafFirst state).getReg .x11 = 200 ∧ (s3LeafFirst state).getReg .x12 = 0 ∧
    (s3LeafFirst state).getReg .x13 = 1 := by
  unfold s3LeafFirst s3LeafBuild
  rw [s3_run_append]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem s3_leaf_first_pc (state : MachineState) (pc : state.pc = 5124) :
    (s3LeafFirst state).pc = BitVec.ofNat 64 (4096 + 4 * 310) := by
  rw [s3LeafFirst, s3_run_pc _ true _ s3_leaf_build_checked, pc, s3_leaf_build_length]
  rfl

theorem s3_leaf_middle_register (state : MachineState) (first : BitVec 1600) (reg : Reg) :
    (s3LeafMiddle state first).getReg reg = (s3LeafFirst state).getReg reg :=
  s3_permutation_register _ first reg

theorem s3_leaf_second_register (state : MachineState) (first : BitVec 1600) (reg : Reg)
    (outside : reg ∉ [Reg.x6, .x10]) :
    (s3LeafSecond state first).getReg reg = (s3LeafFirst state).getReg reg :=
  (s3_run_register_frame s3LeafChain true _ reg s3_leaf_chain_checked _ (by decide)
    outside).trans (s3_leaf_middle_register state first reg)

theorem s3_leaf_second_input (state : MachineState) (first : BitVec 1600) :
    (s3LeafSecond state first).getReg .x10 = 72 := by
  unfold s3LeafSecond s3LeafChain
  rw [s3_run_append]
  rfl

theorem s3_leaf_done_register (state : MachineState) (first second : BitVec 1600) (reg : Reg)
    (outside : reg ∉ [Reg.x6, .x5, .x8, .x10, .x11, .x12, .x13]) :
    (s3LeafDone state first second).getReg reg = state.getReg reg := by
  have finish : reg ∉ [Reg.x6, .x8] := by simp_all
  have chain : reg ∉ [Reg.x6, .x10] := by simp_all
  have build : reg ∉ [Reg.x6, .x5, .x10, .x11, .x12, .x13] := by simp_all
  rw [s3LeafDone, s3_run_register_frame s3LeafFinish false _ reg s3_leaf_finish_checked _
      (by decide) finish, s3LeafLast, s3_permutation_register,
    s3_leaf_second_register state first reg chain, s3_leaf_first_register state reg build]

theorem s3_leaf_done_source (state : MachineState) (first second : BitVec 1600) :
    (s3LeafDone state first second).getReg .x8 = state.getReg .x8 + 256 := by
  have advanced : (s3LeafDone state first second).getReg .x8 =
      (s3Run s3LeafOutput (s3LeafLast state first second)).getReg .x8 + 256 := by
    unfold s3LeafDone s3LeafFinish
    rw [s3_run_append]
    rfl
  rw [advanced, s3_run_register_frame s3LeafOutput false _ .x8 (by decide) [Reg.x6]
      (by decide) (by decide), s3LeafLast, s3_permutation_register,
    s3_leaf_second_register state first .x8 (by decide),
    s3_leaf_first_register state .x8 (by decide)]

theorem s3_leaf_return_execute (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * 346))
    (link : state.getReg .x1 = 4256) (fuel : Nat) (allowCoins : Bool) :
    execute ((capExperimental 24).image .check) (1 + fuel) state allowCoins =
      (do let result ← execute ((capExperimental 24).image .check) fuel
            (state.setPC 4256) allowCoins
          return result.charge 1 0) := by
  have stepped : ordinaryStep state (.base (.JALR .x0 .x1 0)) =
      some (state.setPC 4256) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      MachineState.setReg, link]
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _
    (s3_leaf_return_fetched state pc) stepped]
  rfl

/-- The complete routine from its entry at word 257: 90 instructions, 104
cycles and two permutation calls, for arbitrary replies. -/
theorem cap_check_leaf_execute (state : MachineState) (pc : state.pc = 5124)
    (link : state.getReg .x1 = 4256)
    (sourceValid : ∀ word < 32,
      accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute ((capExperimental 24).image .check) (90 + fuel) state allowCoins =
      (do let finished ← capCheckLeaf state
          let result ← execute ((capExperimental 24).image .check) fuel
            (finished.setPC 4256) allowCoins
          return result.charge 104 2) := by
  have ready := s3_leaf_first_selectors state
  have firstPC := s3_leaf_first_pc state pc
  have build : execute ((capExperimental 24).image .check)
      (53 + (1 + (25 + (1 + (9 + (1 + fuel)))))) state allowCoins =
      (do let result ← execute ((capExperimental 24).image .check)
            (1 + (25 + (1 + (9 + (1 + fuel))))) (s3LeafFirst state) allowCoins
          return result.charge 53 0) := by
    have run := s3_run_execute ((capExperimental 24).image .check) s3LeafBuild true 257 state
      (1 + (25 + (1 + (9 + (1 + fuel))))) allowCoins pc (by decide) s3_leaf_build_decoded
      s3_leaf_build_checked (fun _ => sourceValid)
    rw [s3_leaf_build_length] at run
    exact run
  have call : execute ((capExperimental 24).image .check)
      (1 + (25 + (1 + (9 + (1 + fuel))))) (s3LeafFirst state) allowCoins =
      (do let first ← s3PermutationQuery (readBuffer (s3LeafFirst state) 0 200)
          let result ← execute ((capExperimental 24).image .check)
            (25 + (1 + (9 + (1 + fuel)))) (s3LeafMiddle state first) allowCoins
          return result.charge 8 1) := by
    have raw := s3_permutation_execute ((capExperimental 24).image .check) (s3LeafFirst state)
      (s3_leaf_call_fetched _ (Or.inl firstPC)) ⟨ready.1, ready.2.2.1, ready.2.2.2.2⟩
      (by rw [ready.2.1]; decide) (by rw [ready.2.2.2.1]; decide)
      (by rw [ready.2.1]; decide) (by rw [ready.2.2.2.1]; decide)
      (25 + (1 + (9 + (1 + fuel)))) allowCoins
    rw [show ((s3LeafFirst state).getReg .x10).toNat = 0 by rw [ready.2.1]; rfl] at raw
    exact raw
  have middlePC (first : BitVec 1600) :
      (s3LeafMiddle state first).pc = BitVec.ofNat 64 (4096 + 4 * 311) := by
    rw [s3LeafMiddle, s3_permutation_pc, firstPC]
    rfl
  have middleSource (first : BitVec 1600) : ∀ word < 32,
      accessValid ((s3LeafMiddle state first).getReg .x8 + BitVec.ofNat 64 (8 * word)) 8 =
        true := by
    rw [s3_leaf_middle_register, s3_leaf_first_register state .x8 (by decide)]
    exact sourceValid
  have chain (first : BitVec 1600) : execute ((capExperimental 24).image .check)
      (25 + (1 + (9 + (1 + fuel)))) (s3LeafMiddle state first) allowCoins =
      (do let result ← execute ((capExperimental 24).image .check)
            (1 + (9 + (1 + fuel))) (s3LeafSecond state first) allowCoins
          return result.charge 25 0) := by
    have run := s3_run_execute ((capExperimental 24).image .check) s3LeafChain true 311
      (s3LeafMiddle state first) (1 + (9 + (1 + fuel))) allowCoins (middlePC first)
      (by decide) s3_leaf_chain_decoded s3_leaf_chain_checked (fun _ => middleSource first)
    rw [s3_leaf_chain_length] at run
    exact run
  have secondPC (first : BitVec 1600) :
      (s3LeafSecond state first).pc = BitVec.ofNat 64 (4096 + 4 * 336) := by
    rw [s3LeafSecond, s3_run_pc _ true _ s3_leaf_chain_checked, middlePC,
      s3_leaf_chain_length]
    rfl
  have secondInput := s3_leaf_second_input state
  have secondOutput (first : BitVec 1600) : (s3LeafSecond state first).getReg .x12 = 0 :=
    (s3_leaf_second_register state first .x12 (by decide)).trans ready.2.2.2.1
  have call2 (first : BitVec 1600) : execute ((capExperimental 24).image .check)
      (1 + (9 + (1 + fuel))) (s3LeafSecond state first) allowCoins =
      (do let second ← s3PermutationQuery (readBuffer (s3LeafSecond state first) 72 200)
          let result ← execute ((capExperimental 24).image .check)
            (9 + (1 + fuel)) (s3LeafLast state first second) allowCoins
          return result.charge 8 1) := by
    have raw := s3_permutation_execute ((capExperimental 24).image .check)
      (s3LeafSecond state first) (s3_leaf_call_fetched _ (Or.inr (secondPC first)))
      ⟨(s3_leaf_second_register state first .x5 (by decide)).trans ready.1,
        (s3_leaf_second_register state first .x11 (by decide)).trans ready.2.2.1,
        (s3_leaf_second_register state first .x13 (by decide)).trans ready.2.2.2.2⟩
      (by rw [secondInput]; decide) (by rw [secondOutput]; decide)
      (by rw [secondInput]; decide) (by rw [secondOutput]; decide)
      (9 + (1 + fuel)) allowCoins
    rw [show ((s3LeafSecond state first).getReg .x10).toNat = 72 by
      rw [secondInput]; rfl] at raw
    exact raw
  have lastPC (first second : BitVec 1600) :
      (s3LeafLast state first second).pc = BitVec.ofNat 64 (4096 + 4 * 337) := by
    rw [s3LeafLast, s3_permutation_pc, secondPC]
    rfl
  have finish (first second : BitVec 1600) : execute ((capExperimental 24).image .check)
      (9 + (1 + fuel)) (s3LeafLast state first second) allowCoins =
      (do let result ← execute ((capExperimental 24).image .check)
            (1 + fuel) (s3LeafDone state first second) allowCoins
          return result.charge 9 0) := by
    have run := s3_run_execute ((capExperimental 24).image .check) s3LeafFinish false 337
      (s3LeafLast state first second) (1 + fuel) allowCoins (lastPC first second)
      (by decide) s3_leaf_finish_decoded s3_leaf_finish_checked
      (fun impossible => by cases impossible)
    rw [s3_leaf_finish_length] at run
    exact run
  have donePC (first second : BitVec 1600) :
      (s3LeafDone state first second).pc = BitVec.ofNat 64 (4096 + 4 * 346) := by
    rw [s3LeafDone, s3_run_pc _ false _ s3_leaf_finish_checked, lastPC,
      s3_leaf_finish_length]
    rfl
  have doneLink (first second : BitVec 1600) :
      (s3LeafDone state first second).getReg .x1 = 4256 :=
    (s3_leaf_done_register state first second .x1 (by decide)).trans link
  rw [show 90 + fuel = 53 + (1 + (25 + (1 + (9 + (1 + fuel))))) by omega, build, call]
  simp only [capCheckLeaf, bind_assoc, pure_bind]
  congr 1
  funext first
  rw [chain first, call2 first]
  simp only [bind_assoc, pure_bind]
  congr 1
  funext second
  rw [finish first second,
    s3_leaf_return_execute _ (donePC first second) (doneLink first second)]
  simp only [bind_assoc, pure_bind]
  simp [Execution.charge, ← Nat.add_assoc]

/-- The count is structural and holds on every reply continuation. -/
theorem cap_check_leaf_query_bound (state : MachineState) :
    IsTotalQueryBound (capCheckLeaf state) 2 := by
  unfold capCheckLeaf s3PermutationQuery
  erw [isTotalQueryBound_query_bind_iff]
  refine ⟨by omega, fun first => ?_⟩
  erw [isTotalQueryBound_query_bind_iff]
  exact ⟨by omega, fun second => by trivial⟩

theorem cap_check_leaf_support (state finished : MachineState)
    (reachable : finished ∈ support (capCheckLeaf state)) :
    ∃ first second, finished = s3LeafDone state first second := by
  simp only [capCheckLeaf, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at reachable
  obtain ⟨first, _, second, _, rfl⟩ := reachable
  exact ⟨first, second, rfl⟩

theorem cap_check_leaf_register_frame (state finished : MachineState)
    (reachable : finished ∈ support (capCheckLeaf state)) (reg : Reg)
    (outside : reg ∉ [Reg.x6, .x5, .x8, .x10, .x11, .x12, .x13]) :
    finished.getReg reg = state.getReg reg := by
  obtain ⟨first, second, rfl⟩ := cap_check_leaf_support state finished reachable
  exact s3_leaf_done_register state first second reg outside

theorem cap_check_leaf_source (state finished : MachineState)
    (reachable : finished ∈ support (capCheckLeaf state)) :
    finished.getReg .x8 = state.getReg .x8 + 256 := by
  obtain ⟨first, second, rfl⟩ := cap_check_leaf_support state finished reachable
  exact s3_leaf_done_source state first second

end CommitGolfCandidate
