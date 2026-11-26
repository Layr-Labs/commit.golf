import CommitGolfCandidate.TruncCheckDigest

import CommitGolfCandidate.TruncCap

import CommitGolfCandidate.PairAncestor

namespace CommitGolfCandidate.Trunc.Check

open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate.PairCap

set_option maxRecDepth 14000

set_option maxHeartbeats 750000

theorem rec_check_position_hash_evaluation (oracle : Oracle) (state : MachineState) (pathDepth : Nat) :
    (checkEvaluation oracle (rec_checkPositionHash state pathDepth)).1 =
      rec_checkTargetState (checkEvaluation oracle (rec_checkPathLoop (rec_checkPathInitializedState
        (((checkEvaluation oracle (checkLeafSubroutineRun (rec_checkPositionState state))).1).setPC 5068))
          pathDepth)).1 := by
  rw [rec_checkPositionHash, check_evaluation_bind]
  rcases hLeaf : checkEvaluation oracle (checkLeafSubroutineRun (rec_checkPositionState state)) with ⟨leaf, c1⟩
  dsimp only
  rw [check_evaluation_bind]
  rcases hPath : checkEvaluation oracle (rec_checkPathLoop
      (rec_checkPathInitializedState (leaf.setPC 5068)) pathDepth) with ⟨pathed, c2⟩
  simp only [check_evaluation_pure]

theorem rec_finish_check_path (oracle : Oracle) (state leaf : MachineState)
    (pathDepth proofAddress : Nat) (path : List (Bool × Digest)) (digest : Digest)
    (index : Index) (mode : pathDepth=16 ∨ pathDepth=24)
    (dreg : leaf.getReg .x30=BitVec.ofNat 64 pathDepth) (cap : leaf.getReg .x19=0 ↔ pathDepth=24)
    (leafScratch : leaf.getReg .x21 = 256)
    (leafPointer : leaf.getReg .x25 = BitVec.ofNat 64 (proofAddress + 16))
    (leafIndex : leaf.getReg .x20 = state.getMem (state.getReg .x24))
    (leafOutside : ∀ address : Word,
      (∀ i < 12, address ≠ BitVec.ofNat 64 (256 + 8 * i)) → leaf.getMem address = state.getMem address)
    (leafDigestEq : readBuffer leaf 256 32 = digest)
    (proofAligned : proofAddress % 8 = 0) (proofAbove : 352 ≤ proofAddress)
    (proofBound : proofAddress + (16 + 32 * pathDepth) < 2 ^ 64)
    (pathLength : path.length = pathDepth)
    (pathData : ∀ i (hi : i < path.length),
      readBuffer state (proofAddress + 16 + 32 * i) 32 = (path[i]'hi).2)
    (directions : ∀ i (hi : i < path.length),
      (state.getMem (state.getReg .x24)).getLsbD i = (path[i]'hi).1) :
    readBuffer (checkEvaluation oracle
      (rec_checkPathLoop (rec_checkPathInitializedState (leaf.setPC 5068)) pathDepth)).1 256 32 =
      Trunc.climb oracle.compression (LENGTH+index.val) digest path := by
  let pathReady := rec_checkPathInitializedState (leaf.setPC 5068)
  have pathScratch : pathReady.getReg .x21 = 256 :=
    (rec_check_path_setup_register (leaf.setPC 5068) .x21 (by decide)).trans leafScratch
  have pathPointer : pathReady.getReg .x25 = BitVec.ofNat 64 (proofAddress + 16) :=
    (rec_check_path_setup_register (leaf.setPC 5068) .x25 (by decide)).trans leafPointer
  have pathMemory (address : Word) : pathReady.getMem address = leaf.getMem address :=
    congrFun (rec_check_path_setup_memory (leaf.setPC 5068)) address
  have afterData (i : Nat) (hi : i < path.length) :
      readBuffer pathReady (proofAddress + 16 + 32 * i) 32 = (path[i]'hi).2 := by
    have same : readBuffer pathReady (proofAddress + 16 + 32 * i) 32 =
        readBuffer state (proofAddress + 16 + 32 * i) 32 := by
      apply read_digest_congr _ _ _ (by omega)
      intro word hw
      rw [pathMemory]
      apply leafOutside
      intro j hj
      simpa only [Nat.add_assoc] using rec_word_outside_scratch proofAddress (16 + 32 * i + 8 * word) proofAbove
        (by rw [pathLength] at hi; omega) j hj
    exact same.trans (pathData i hi)
  have afterDirections (i : Nat) (hi : i < path.length) :
      (pathReady.getReg .x20).getLsbD i = (path[i]'hi).1 := by
    rw [rec_check_path_setup_register _ .x20 (by decide), MachineState.getReg_setPC, leafIndex]
    exact directions i hi
  have frame : GFrame pathReady pathDepth path.length := by
    refine ⟨?_,?_,?_⟩
    · rw [pathLength];exact (rec_check_path_initialized_counter _).trans dreg
    · exact (rec_check_path_setup_register _ .x30 (by decide)).trans dreg
    · rw [show pathReady.getReg .x19=leaf.getReg .x19 from rec_check_path_setup_register _ .x19 (by decide)];exact cap
  have folded : readBuffer (checkEvaluation oracle (rec_checkPathLoop pathReady path.length)).1 256 32 =
      Trunc.climb oracle.compression (LENGTH+index.val) (readBuffer pathReady 256 32) path := by
    have h :=  rec_check_path_loop_digest oracle pathReady (proofAddress + 16) path index pathDepth mode frame (by omega) pathScratch pathPointer
      (by omega) (by omega) (by rw [pathLength]; omega) afterData afterDirections
    simpa only [pathLength,Nat.sub_self,Nat.pow_zero,Nat.div_one] using h
  have startDigest : readBuffer pathReady 256 32 = digest := by
    have same : readBuffer pathReady 256 32 = readBuffer leaf 256 32 := by
      apply read_digest_congr _ _ _ (by decide)
      intro word hw
      exact pathMemory _
    exact same.trans leafDigestEq
  have sameLength := congrArg (fun count =>
    readBuffer (checkEvaluation oracle (rec_checkPathLoop pathReady count)).1 256 32) pathLength.symm
  exact sameLength.trans (folded.trans
    (congrArg (fun value => Trunc.climb oracle.compression (LENGTH+index.val) value path) startDigest))

theorem rec_check_position_hash_digest (oracle : Oracle) (state : MachineState)
    (pathDepth valueAddress proofAddress : Nat) (index : Index) (value : Entry) (salt : Salt)
    (path : List (Bool × Digest))
    (mode : pathDepth=16 ∨ pathDepth=24) (dreg : state.getReg .x30=BitVec.ofNat 64 pathDepth)
    (cap : state.getReg .x19=0 ↔ pathDepth=24) (scratch : state.getReg .x21 = 256)
    (valuePointer : state.getReg .x8 = BitVec.ofNat 64 valueAddress)
    (proofPointer : state.getReg .x25 = BitVec.ofNat 64 proofAddress)
    (valueAligned : valueAddress % 8 = 0) (proofAligned : proofAddress % 8 = 0)
    (valueAbove : 352 ≤ valueAddress) (proofAbove : 352 ≤ proofAddress)
    (valueBound : valueAddress + 256 < 2 ^ 64)
    (proofBound : proofAddress + (16 + 32 * pathDepth) < 2 ^ 64)
    (indexData : state.getMem (state.getReg .x24) = BitVec.ofNat 64 index.val)
    (saltData : readBuffer state proofAddress 16 = salt)
    (valueData : ∀ block < 4, readBuffer state (valueAddress + 64 * block) 64 =
      value.extractLsb' (512 * block) 512)
    (pathLength : path.length = pathDepth)
    (pathData : ∀ i (hi : i < path.length),
      readBuffer state (proofAddress + 16 + 32 * i) 32 = (path[i]'hi).2)
    (directions : ∀ i (hi : i < path.length),
      (state.getMem (state.getReg .x24)).getLsbD i = (path[i]'hi).1) :
    readBuffer (checkEvaluation oracle (rec_checkPositionHash state pathDepth)).1 256 32 =
      Trunc.climb oracle.compression (LENGTH+index.val) (leafDigest oracle.compression index salt value) path := by
  let ready := rec_checkPositionState state
  let leaf := (checkEvaluation oracle (checkLeafSubroutineRun ready)).1
  have readyScratch : ready.getReg .x21 = 256 :=
    (rec_check_position_register state .x21 (by decide)).trans scratch
  have readyPointer : ready.getReg .x8 = BitVec.ofNat 64 valueAddress :=
    (rec_check_position_register state .x8 (by decide)).trans valuePointer
  have saltTag := rec_check_position_salt_tag state proofAddress index scratch proofPointer
    proofAligned (by omega) (by omega) indexData
  have readySalt : readBuffer ready 256 16 = salt := saltTag.1.trans saltData
  have readyTag : readBuffer ready 272 8 = leafTag index := saltTag.2
  have readyOutside (address : Word) (outside : ∀ i < 4, address ≠ BitVec.ofNat 64 (256 + 8 * i)) :
      ready.getMem address = state.getMem address := rec_check_position_outside state address scratch outside
  have readyHalf (address : Nat) (aligned : address % 8 = 0) (above : 352 ≤ address)
      (bounded : address + 32 < 2 ^ 64) : readBuffer ready address 32 = readBuffer state address 32 := by
    apply read_digest_congr _ _ _ aligned
    intro word hw
    apply readyOutside
    intro i hi
    exact rec_word_outside_scratch address (8 * word) above (by omega) i (by omega)
  have readyData (block : Nat) (hb : block < 4) :
      readBuffer ready (valueAddress + 64 * block) 64 = value.extractLsb' (512 * block) 512 := by
    rw [read_compression_halves _ _ (by omega),
      readyHalf (valueAddress + 64 * block + 32) (by omega) (by omega) (by omega),
      readyHalf (valueAddress + 64 * block) (by omega) (by omega) (by omega),
      ← read_compression_halves _ _ (by omega)]
    exact valueData block hb
  have leafDigestEq : readBuffer leaf 256 32 = leafDigest oracle.compression index salt value :=
    check_leaf_digest oracle ready valueAddress index salt value readyScratch readyPointer
      valueAligned valueAbove valueBound readySalt readyTag readyData
  have leafRegs := check_leaf_subroutine_registers ready leaf (check_evaluation_support oracle _)
  have leafScratch : leaf.getReg .x21 = 256 := (leafRegs.2 .x21 (by decide)).trans readyScratch
  have leafPointer : leaf.getReg .x25 = BitVec.ofNat 64 (proofAddress + 16) := by
    rw [leafRegs.2 .x25 (by decide)]
    change (rec_checkPositionState state).getReg .x25 = _
    rw [rec_check_position_proof_pointer, proofPointer]
    exact (BitVec.ofNat_add proofAddress 16).symm
  have leafIndex : leaf.getReg .x20 = state.getMem (state.getReg .x24) := by
    rw [leafRegs.2 .x20 (by decide)]
    exact rec_check_position_index state
  have leafOutside (address : Word) (outside : ∀ i < 12, address ≠ BitVec.ofNat 64 (256 + 8 * i)) :
      leaf.getMem address = state.getMem address :=
    (check_leaf_subroutine_outside oracle ready address readyScratch outside).trans
      (readyOutside address (fun i hi => outside i (by omega)))
  rw [rec_check_position_hash_evaluation, read_buffer_memory_congr _ _ (rec_check_target_memory _)]
  have ld := (leafRegs.2 .x30 (by decide)).trans ((rec_check_position_register state .x30 (by decide)).trans dreg)
  have ls : leaf.getReg .x19=0 ↔ pathDepth=24 := by
    rw [show leaf.getReg .x19=state.getReg .x19 from (leafRegs.2 .x19 (by decide)).trans (rec_check_position_register state .x19 (by decide))]
    exact cap
  exact rec_finish_check_path oracle state leaf pathDepth proofAddress path _ index mode ld ls leafScratch leafPointer leafIndex
    leafOutside leafDigestEq proofAligned proofAbove proofBound pathLength pathData directions

theorem rec_check_path_phase_outside (oracle : Oracle) (leaf : MachineState) (pathDepth : Nat)
    (address : Word) (scratch : leaf.getReg .x21 = 256)
    (outside : ∀ i < 12, address ≠ BitVec.ofNat 64 (256 + 8 * i)) :
    (checkEvaluation oracle
      (rec_checkPathLoop (rec_checkPathInitializedState (leaf.setPC 5068)) pathDepth)).1.getMem address =
        leaf.getMem address := by
  have pathScratch : (rec_checkPathInitializedState (leaf.setPC 5068)).getReg .x21 = 256 :=
    (rec_check_path_setup_register (leaf.setPC 5068) .x21 (by decide)).trans scratch
  exact (rec_check_path_loop_outside oracle (rec_checkPathInitializedState (leaf.setPC 5068))
    pathDepth address pathScratch (fun i hi => outside i (by omega))).trans
      (congrFun (rec_check_path_setup_memory (leaf.setPC 5068)) address)

theorem rec_check_position_hash_outside (oracle : Oracle) (state : MachineState) (pathDepth : Nat)
    (address : Word) (scratch : state.getReg .x21 = 256)
    (outside : ∀ i < 12, address ≠ BitVec.ofNat 64 (256 + 8 * i)) :
    (checkEvaluation oracle (rec_checkPositionHash state pathDepth)).1.getMem address = state.getMem address := by
  let ready := rec_checkPositionState state
  let leaf := (checkEvaluation oracle (checkLeafSubroutineRun ready)).1
  have readyScratch : ready.getReg .x21 = 256 :=
    (rec_check_position_register state .x21 (by decide)).trans scratch
  have leafScratch : leaf.getReg .x21 = 256 :=
    ((check_leaf_subroutine_registers ready leaf (check_evaluation_support oracle _)).2 .x21 (by decide)).trans
      readyScratch
  have initialMemory : ready.getMem address = state.getMem address :=
    rec_check_position_outside state address scratch (fun i hi => outside i (by omega))
  have leafMemory := check_leaf_subroutine_outside oracle ready address readyScratch outside
  rw [rec_check_position_hash_evaluation]
  change (rec_checkTargetState _).mem address = _
  rw [rec_check_target_memory]
  exact (rec_check_path_phase_outside oracle leaf pathDepth address leafScratch outside).trans
    (leafMemory.trans initialMemory)

theorem rec_check_record_ancestor (oracle : Oracle) (state : MachineState)
    (pathDepth valueAddress proofAddress : Nat) (value : Entry) (salt : Salt)
    (index : Index) (siblings : Nat → Digest)
    (mode : pathDepth=16 ∨ pathDepth=24) (dreg : state.getReg .x30=BitVec.ofNat 64 pathDepth)
    (cap : state.getReg .x19=0 ↔ pathDepth=24) (depthBound : pathDepth ≤ 24)
    (scratch : state.getReg .x21 = 256)
    (valuePointer : state.getReg .x8 = BitVec.ofNat 64 valueAddress)
    (proofPointer : state.getReg .x25 = BitVec.ofNat 64 proofAddress)
    (valueAligned : valueAddress % 8 = 0) (proofAligned : proofAddress % 8 = 0)
    (valueAbove : 352 ≤ valueAddress) (proofAbove : 352 ≤ proofAddress)
    (valueBound : valueAddress + 256 < 2 ^ 64)
    (proofBound : proofAddress + (16 + 32 * pathDepth) < 2 ^ 64)
    (valueData : ∀ block < 4, readBuffer state (valueAddress + 64 * block) 64 =
      value.extractLsb' (512 * block) 512)
    (saltData : readBuffer state proofAddress 16 = salt)
    (indexData : state.getMem (state.getReg .x24) = BitVec.ofNat 64 index.val)
    (pathData : ∀ level < pathDepth,
      readBuffer state (proofAddress + 16 + 32 * level) 32 = siblings level) :
    readBuffer (checkEvaluation oracle (rec_checkPositionHash state pathDepth)).1 256 32 =
      Trunc.recordAncestor oracle.compression pathDepth value salt index siblings := by
  apply rec_check_position_hash_digest oracle state pathDepth valueAddress proofAddress index value salt
    (recordPathPrefix pathDepth index siblings) mode dreg cap scratch valuePointer proofPointer
    valueAligned proofAligned valueAbove proofAbove valueBound proofBound indexData saltData valueData
    (record_path_prefix_length _ _ _)
  · intro level inside
    have below : level < pathDepth := by rw [record_path_prefix_length] at inside; exact inside
    simpa only [recordPathPrefix, List.getElem_map, List.getElem_range] using pathData level below
  · intro level inside
    have below : level < pathDepth := by rw [record_path_prefix_length] at inside; exact inside
    rw [indexData, BitVec.getLsbD_ofNat]
    simp only [recordPathPrefix, List.getElem_map, List.getElem_range,
      show level < 64 by omega, decide_true, Bool.true_and]

end CommitGolfCandidate.Trunc.Check
