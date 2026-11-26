import CommitGolfCandidate.PairControl

import CommitGolfCandidate.CheckSound

import CommitGolfCandidate.PairPathValue

namespace CommitGolfCandidate.PairCap

open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 12000

set_option maxHeartbeats 1400000

theorem rec_tag_word_eq (index : Index) :
    ((BitVec.ofNat 64 index.val + 16#64) <<< 8) + 18446744073709551592#64 = leafTag index := by
  have hi : index.val < 16777216 := index.isLt
  apply BitVec.eq_of_toNat_eq
  have h1 : (BitVec.ofNat 64 index.val + 16#64).toNat = index.val + 16 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    have h16 : (16#64 : Word).toNat = 16 := rfl
    rw [h16]
    change (index.val % 18446744073709551616 + 16) % 18446744073709551616 = _; omega
  have h2 : ((BitVec.ofNat 64 index.val + 16#64) <<< 8).toNat = 256 * (index.val + 16) := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, h1]
    change ((index.val + 16) * 256) % 18446744073709551616 = _; omega
  have h24 : (18446744073709551592#64 : Word).toNat = 18446744073709551592 := rfl
  rw [BitVec.toNat_add, h2, h24, leafTag_toNat]
  change (256 * (index.val + 16) + 18446744073709551592) % 18446744073709551616 = 4072 + 256 * index.val
  omega

theorem rec_check_getMem_setMem (s : MachineState) (a v q : Word) :
    (s.setMem a v).getMem q = if q = a then v else s.getMem q := by
  by_cases h : q = a
  · subst h; simp [MachineState.getMem_setMem_eq]
  · simp only [if_neg h]
    first | exact MachineState.getMem_setMem_ne h | exact MachineState.getMem_setMem_ne h.symm

theorem rec_check_salt_tag_getMem (state : MachineState) (address : Nat)
    (scratch : state.getReg .x21 = 256) (pointer : state.getReg .x25 = BitVec.ofNat 64 address)
    (above : 320 ≤ address) (bounded : address + 16 < 2^64) (addr : Word) :
    (checkSaltTagState state).getMem addr =
      if addr = 272#64 then ((state.getReg .x20 + 16#64) <<< 8) + 18446744073709551592#64
      else if addr = 264#64 then state.getMem (BitVec.ofNat 64 (address + 8))
      else if addr = 256#64 then state.getMem (BitVec.ofNat 64 address)
      else state.getMem addr := by
  have h256 : state.getReg .x21 = 256#64 := scratch
  have neqAddr1 : BitVec.ofNat 64 (address + 8) ≠ 256#64 := by
    intro h; have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : address + 8 < 2^64)] at this; omega
  have hadd8 : BitVec.ofNat 64 address + 8#64 = BitVec.ofNat 64 (address + 8) := by
    change BitVec.ofNat 64 address + BitVec.ofNat 64 8 = _; rw [← BitVec.ofNat_add]
  have memReg (s : MachineState) (a v : Word) (r : Reg) : (s.setMem a v).getReg r = s.getReg r := by
    cases r <;> rfl
  have hse0 : signExtend12 (0 : BitVec 12) = 0#64 := rfl
  have hse8 : signExtend12 (8 : BitVec 12) = 8#64 := rfl
  have hse16 : signExtend12 (16 : BitVec 12) = 16#64 := rfl
  have hse4072 : signExtend12 (4072 : BitVec 12) = 18446744073709551592#64 := rfl
  have hsh8 : (8 : BitVec 6).toNat = 8 := rfl
  have hadd0 (x : Word) : x + 0#64 = x := BitVec.add_zero x
  have h256_8 : 256#64 + 8#64 = 264#64 := rfl
  have h256_16 : 256#64 + 16#64 = 272#64 := rfl
  rw [check_salt_tag_expansion]
  simp only [List.foldl, execInstrBr, hse0, hse8, hse16, hse4072, hsh8, MachineState.getReg_setPC,
    MachineState.getMem_setPC, MachineState.getMem_setReg, memReg,
    MachineState.getReg_setReg_eq (by decide : Reg.x6 ≠ .x0),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x21),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x25),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x20),
    h256, pointer, hadd8, h256_8, h256_16, hadd0]
  simp only [rec_check_getMem_setMem, MachineState.getMem_setPC, MachineState.getMem_setReg,
    neqAddr1, ↓reduceIte]

theorem rec_check_position_salt_tag (state : MachineState) (address : Nat) (index : Index)
    (scratch : state.getReg .x21 = 256) (pointer : state.getReg .x25 = BitVec.ofNat 64 address)
    (aligned : address % 8 = 0) (above : 320 ≤ address) (bounded : address + 16 < 2 ^ 64)
    (indexData : state.getMem (state.getReg .x24) = BitVec.ofNat 64 index.val) :
    readBuffer (rec_checkPositionState state) 256 16 = readBuffer state address 16 ∧
    readBuffer (rec_checkPositionState state) 272 8 = leafTag index := by
  let st := rec_checkIndexState state
  have stScratch : st.getReg .x21 = 256 := by
    simpa [st, rec_checkIndexState, MachineState.getReg_setReg_ne] using scratch
  have stPointer : st.getReg .x25 = BitVec.ofNat 64 address := by
    simpa [st, rec_checkIndexState, MachineState.getReg_setReg_ne] using pointer
  have stIndex : st.getReg .x20 = BitVec.ofNat 64 index.val := by
    simpa [st, rec_checkIndexState, MachineState.getReg_setReg_eq] using indexData
  have gm := rec_check_salt_tag_getMem st address stScratch stPointer above bounded
  constructor
  · change readBuffer (checkSaltTagState st) 256 16 = readBuffer state address 16
    rw [read_salt_words _ _ (by decide), read_salt_words _ _ aligned, gm, gm]
    simp only [show (256 : Word) ≠ 272#64 by decide, show (256 : Word) ≠ 264#64 by decide,
      show (264 : Word) ≠ 272#64 by decide, ↓reduceIte]
    rfl
  · change readBuffer (checkSaltTagState st) 272 8 = leafTag index
    rw [read_word_eq _ _ (by decide), gm, if_pos rfl, stIndex]
    exact rec_tag_word_eq index

theorem rec_check_position_outside (state : MachineState) (address : Word)
    (scratch : state.getReg .x21 = 256)
    (outside : ∀ i < 4, address ≠ BitVec.ofNat 64 (256 + 8 * i)) :
    (rec_checkPositionState state).getMem address = state.getMem address := by
  change (checkSaltTagState (rec_checkIndexState state)).getMem address = _
  exact check_salt_tag_mem_outside (rec_checkIndexState state) address
    (by simpa [rec_checkIndexState, MachineState.getReg_setReg_ne] using scratch)
    (fun i hi => outside i (by omega))

theorem rec_word_outside_scratch (address offset : Nat) (above : 352 ≤ address)
    (bounded : address + offset < 2 ^ 64) (i : Nat) (hi : i < 12) :
    BitVec.ofNat 64 (address + offset) ≠ BitVec.ofNat 64 (256 + 8 * i) := by
  intro equal
  have natural := congrArg BitVec.toNat equal
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bounded,
    Nat.mod_eq_of_lt (by omega : 256 + 8 * i < 2 ^ 64)] at natural
  omega

theorem rec_check_path_setup_memory (state : MachineState) :
    (rec_checkPathInitializedState state).mem = state.mem := rfl

theorem rec_check_target_memory (state : MachineState) :
    (rec_checkTargetState state).mem = state.mem := rfl

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
      climb oracle.compression digest path := by
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
  have folded := rec_check_path_loop_digest oracle pathReady (proofAddress + 16) path pathScratch pathPointer
    (by omega) (by omega) (by rw [pathLength]; omega) afterData afterDirections
  have startDigest : readBuffer pathReady 256 32 = digest := by
    have same : readBuffer pathReady 256 32 = readBuffer leaf 256 32 := by
      apply read_digest_congr _ _ _ (by decide)
      intro word hw
      exact pathMemory _
    exact same.trans leafDigestEq
  have sameLength := congrArg (fun count =>
    readBuffer (checkEvaluation oracle (rec_checkPathLoop pathReady count)).1 256 32) pathLength.symm
  exact sameLength.trans (folded.trans
    (congrArg (fun value => climb oracle.compression value path) startDigest))

theorem rec_check_position_hash_digest (oracle : Oracle) (state : MachineState)
    (pathDepth valueAddress proofAddress : Nat) (index : Index) (value : Entry) (salt : Salt)
    (path : List (Bool × Digest))
    (scratch : state.getReg .x21 = 256)
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
      climb oracle.compression (leafDigest oracle.compression index salt value) path := by
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
  exact rec_finish_check_path oracle state leaf pathDepth proofAddress path _ leafScratch leafPointer leafIndex
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
    (depthBound : pathDepth ≤ 24)
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
      recordAncestor oracle.compression pathDepth value salt index siblings := by
  apply rec_check_position_hash_digest oracle state pathDepth valueAddress proofAddress index value salt
    (recordPathPrefix pathDepth index siblings) scratch valuePointer proofPointer
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

end CommitGolfCandidate.PairCap
