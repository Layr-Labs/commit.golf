import CommitGolfCandidate.CapCheckGroupCollected

/-! Successful instruction-level group handling is exactly the logical
consistency insertion, and establishes its resulting collected-root map.
Only initialized zero/one occupancy is used to interpret the lookup branch. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false
attribute [local irreducible] capCheckGroupStartPrefix readBuffer

theorem cap_check_group_insert (state : MachineState) (roots : CapRootMap)
    (ready : CapCheckCollected state roots) (group : Nat) (bounded : group < 256)
    (index : state.getReg .x20 = BitVec.ofNat 64 group)
    (leaves : state.getReg .x19 = 256) (marks : state.getReg .x9 = 28672)
    (rootBase : state.getReg .x18 = 12288) (scratch : state.getReg .x21 = 256)
    (one : state.getReg .x31 = 1) :
    (capCheckGroupResult state).2 = true ↔
      (capInsert roots group (readBuffer state 256 32)).isSome = true := by
  have lookup := cap_check_group_lookup_mark state group bounded index leaves marks rootBase
  cases prior : roots group with
  | none =>
    have absent : (capCheckGroupStartPrefix state 6).getReg .x6 = 0 := by
      rw [lookup]
      exact (cap_check_collected_mark_zero state roots ready group bounded).mpr prior
    simp only [capCheckGroupResult,absent,↓reduceIte,capInsert,prior,Option.isSome_some]
  | some previous =>
    have occupied : (capCheckGroupStartPrefix state 6).getReg .x6 ≠ 0 := by
      rw [lookup,cap_check_collected_mark_one state roots ready group bounded previous prior]
      decide
    have equal := cap_check_group_duplicate_value state roots ready group bounded index
      leaves marks rootBase scratch previous prior
    dsimp only [capCheckGroupResult]
    simp only [occupied,↓reduceIte,capInsert,prior]
    by_cases same : previous = readBuffer state 256 32
    · have passed := equal.mpr same.symm
      simp only [passed,same,↓reduceIte,Option.isSome_some]
    · have failed : (capCheckDuplicateLoop (capCheckGroupCompared state) 0 4).2 ≠ true :=
        fun passed => same (equal.mp passed).symm
      simp only [failed,same,↓reduceIte,Option.isSome_none,Bool.false_eq_true]

theorem cap_check_group_insert_collected (state : MachineState) (roots next : CapRootMap)
    (ready : CapCheckCollected state roots) (group : Nat) (bounded : group < 256)
    (index : state.getReg .x20 = BitVec.ofNat 64 group)
    (leaves : state.getReg .x19 = 256) (marks : state.getReg .x9 = 28672)
    (rootBase : state.getReg .x18 = 12288) (scratch : state.getReg .x21 = 256)
    (one : state.getReg .x31 = 1)
    (accepted : capInsert roots group (readBuffer state 256 32) = some next) :
    CapCheckCollected (capCheckGroupResult state).1 next := by
  have lookup := cap_check_group_lookup_mark state group bounded index leaves marks rootBase
  have addresses := cap_check_group_compared_addresses state group bounded index leaves marks rootBase
  have comparedReady := cap_check_group_compared_collected state roots ready
  have comparedScratch := cap_check_group_compared_scratch state scratch
  have comparedOne : (capCheckGroupCompared state).getReg .x31 = 1 := by
    rw [cap_check_group_compared_register,
      cap_check_group_start_register state 6 (by decide) .x31 (by decide),one]
  cases prior : roots group with
  | none =>
    have absent : (capCheckGroupStartPrefix state 6).getReg .x6 = 0 := by
      rw [lookup]
      exact (cap_check_collected_mark_zero state roots ready group bounded).mpr prior
    simp only [capInsert,prior] at accepted
    cases accepted
    simp only [capCheckGroupResult,absent,↓reduceIte]
    have result := cap_check_store_collected (capCheckGroupCompared state) roots comparedReady
      group bounded comparedScratch addresses.1 addresses.2 comparedOne
    rw [read_buffer_memory_congr _ state (cap_check_group_compared_memory state) 256 32] at result
    exact result
  | some previous =>
    have occupied : (capCheckGroupStartPrefix state 6).getReg .x6 ≠ 0 := by
      rw [lookup,cap_check_collected_mark_one state roots ready group bounded previous prior]
      decide
    by_cases same : previous = readBuffer state 256 32
    · simp only [capInsert,prior,same,↓reduceIte,Option.some.injEq] at accepted
      subst next
      have passed := (cap_check_group_duplicate_value state roots ready group bounded index
        leaves marks rootBase scratch previous prior).mpr same.symm
      simp only [capCheckGroupResult,occupied,passed,↓reduceIte]
      exact cap_check_collected_memory _ _ roots
        (cap_check_duplicate_done_memory _) comparedReady
    · simp only [capInsert,prior,same,↓reduceIte] at accepted
      contradiction

end CommitGolfCandidate
