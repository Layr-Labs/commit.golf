import CommitGolfCandidate.PathRefinement
import CommitGolfCandidate.BufferRefinement
import CommitGolfCandidate.HeapModel

/-! Functional refinement of the actual checker's complete position computation
(16-byte position-tagged salt + 4-call leaf chain + `pathDepth`-level Merkle path,
where `pathDepth = 24` in normal mode and `pathDepth = 17` in cap-table mode). -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

private theorem tag_word_eq (index : Index) :
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

private theorem check_getMem_setMem (s : MachineState) (a v q : Word) :
    (s.setMem a v).getMem q = if q = a then v else s.getMem q := by
  by_cases h : q = a
  · subst h; simp [MachineState.getMem_setMem_eq]
  · simp only [if_neg h]
    first | exact MachineState.getMem_setMem_ne h | exact MachineState.getMem_setMem_ne h.symm

private theorem check_salt_tag_getMem (state : MachineState) (address : Nat)
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
  simp only [check_getMem_setMem, MachineState.getMem_setPC, MachineState.getMem_setReg,
    neqAddr1, ↓reduceIte]

/-- The per-position setup copies the 16-byte proof salt into `[256, 272)` and writes
`leafTag index` into `[272, 280)`. -/
theorem check_position_salt_tag (state : MachineState) (address : Nat) (index : Index)
    (scratch : state.getReg .x21 = 256) (pointer : state.getReg .x25 = BitVec.ofNat 64 address)
    (aligned : address % 8 = 0) (above : 320 ≤ address) (bounded : address + 16 < 2 ^ 64)
    (indexData : state.getMem (state.getReg .x24) = BitVec.ofNat 64 index.val) :
    readBuffer (checkPositionState state) 256 16 = readBuffer state address 16 ∧
    readBuffer (checkPositionState state) 272 8 = leafTag index := by
  let st := checkIndexState state
  have stScratch : st.getReg .x21 = 256 := by
    simpa [st, checkIndexState, MachineState.getReg_setReg_ne] using scratch
  have stPointer : st.getReg .x25 = BitVec.ofNat 64 address := by
    simpa [st, checkIndexState, MachineState.getReg_setReg_ne] using pointer
  have stIndex : st.getReg .x20 = BitVec.ofNat 64 index.val := by
    simpa [st, checkIndexState, MachineState.getReg_setReg_eq] using indexData
  have gm := check_salt_tag_getMem st address stScratch stPointer above bounded
  constructor
  · change readBuffer (checkSaltTagState st) 256 16 = readBuffer state address 16
    rw [read_salt_words _ _ (by decide), read_salt_words _ _ aligned, gm, gm]
    simp only [show (256 : Word) ≠ 272#64 by decide, show (256 : Word) ≠ 264#64 by decide,
      show (264 : Word) ≠ 272#64 by decide, ↓reduceIte]
    rfl
  · change readBuffer (checkSaltTagState st) 272 8 = leafTag index
    rw [read_word_eq _ _ (by decide), gm, if_pos rfl, stIndex]
    exact tag_word_eq index

/-- The index load and salt/tag setup preserve all words outside `[256, 288)`. -/
theorem check_position_outside (state : MachineState) (address : Word)
    (scratch : state.getReg .x21 = 256)
    (outside : ∀ i < 4, address ≠ BitVec.ofNat 64 (256 + 8 * i)) :
    (checkPositionState state).getMem address = state.getMem address := by
  change (checkSaltTagState (checkIndexState state)).getMem address = _
  exact check_salt_tag_mem_outside (checkIndexState state) address
    (by simpa [checkIndexState, MachineState.getReg_setReg_ne] using scratch)
    (fun i hi => outside i (by omega))

private theorem word_outside_scratch (address offset : Nat) (above : 352 ≤ address)
    (bounded : address + offset < 2 ^ 64) (i : Nat) (hi : i < 12) :
    BitVec.ofNat 64 (address + offset) ≠ BitVec.ofNat 64 (256 + 8 * i) := by
  intro equal
  have natural := congrArg BitVec.toNat equal
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bounded,
    Nat.mod_eq_of_lt (by omega : 256 + 8 * i < 2 ^ 64)] at natural
  omega

private theorem check_path_setup_memory (state : MachineState) :
    (checkPathInitializedState state).mem = state.mem := rfl

private theorem check_target_memory (state : MachineState) :
    (checkTargetState state).mem = state.mem := rfl

attribute [local irreducible] checkPositionState checkLeafSubroutineRun checkPathLoop
  checkPathInitializedState checkTargetState checkEvaluation checkPositionHash

set_option maxRecDepth 4096 in
theorem check_position_hash_evaluation (oracle : Oracle) (state : MachineState) (pathDepth : Nat) :
    (checkEvaluation oracle (checkPositionHash state pathDepth)).1 =
      checkTargetState (checkEvaluation oracle (checkPathLoop (checkPathInitializedState
        (((checkEvaluation oracle (checkLeafSubroutineRun (checkPositionState state))).1).setPC 4200))
          pathDepth)).1 := by
  rw [checkPositionHash, check_evaluation_bind]
  rcases hLeaf : checkEvaluation oracle (checkLeafSubroutineRun (checkPositionState state)) with ⟨leaf, c1⟩
  dsimp only
  rw [check_evaluation_bind]
  rcases hPath : checkEvaluation oracle (checkPathLoop
      (checkPathInitializedState (leaf.setPC 4200)) pathDepth) with ⟨pathed, c2⟩
  simp only [check_evaluation_pure]

set_option maxRecDepth 4096 in
private theorem finish_check_path (oracle : Oracle) (state leaf : MachineState)
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
      (checkPathLoop (checkPathInitializedState (leaf.setPC 4200)) pathDepth)).1 256 32 =
      climb oracle.compression digest path := by
  let pathReady := checkPathInitializedState (leaf.setPC 4200)
  have pathScratch : pathReady.getReg .x21 = 256 :=
    (check_path_setup_register (leaf.setPC 4200) .x21 (by decide)).trans leafScratch
  have pathPointer : pathReady.getReg .x25 = BitVec.ofNat 64 (proofAddress + 16) :=
    (check_path_setup_register (leaf.setPC 4200) .x25 (by decide)).trans leafPointer
  have pathMemory (address : Word) : pathReady.getMem address = leaf.getMem address :=
    congrFun (check_path_setup_memory (leaf.setPC 4200)) address
  have afterData (i : Nat) (hi : i < path.length) :
      readBuffer pathReady (proofAddress + 16 + 32 * i) 32 = (path[i]'hi).2 := by
    have same : readBuffer pathReady (proofAddress + 16 + 32 * i) 32 =
        readBuffer state (proofAddress + 16 + 32 * i) 32 := by
      apply read_digest_congr _ _ _ (by omega)
      intro word hw
      rw [pathMemory]
      apply leafOutside
      intro j hj
      simpa only [Nat.add_assoc] using word_outside_scratch proofAddress (16 + 32 * i + 8 * word) proofAbove
        (by rw [pathLength] at hi; omega) j hj
    exact same.trans (pathData i hi)
  have afterDirections (i : Nat) (hi : i < path.length) :
      (pathReady.getReg .x20).getLsbD i = (path[i]'hi).1 := by
    rw [check_path_setup_register _ .x20 (by decide), MachineState.getReg_setPC, leafIndex]
    exact directions i hi
  have folded := check_path_loop_digest oracle pathReady (proofAddress + 16) path pathScratch pathPointer
    (by omega) (by omega) (by rw [pathLength]; omega) afterData afterDirections
  have startDigest : readBuffer pathReady 256 32 = digest := by
    have same : readBuffer pathReady 256 32 = readBuffer leaf 256 32 := by
      apply read_digest_congr _ _ _ (by decide)
      intro word hw
      exact pathMemory _
    exact same.trans leafDigestEq
  have sameLength := congrArg (fun count =>
    readBuffer (checkEvaluation oracle (checkPathLoop pathReady count)).1 256 32) pathLength.symm
  exact sameLength.trans (folded.trans
    (congrArg (fun value => climb oracle.compression value path) startDigest))

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4096 in
/-- One complete checker iteration computes the submitted tagged leaf digest and folds its
`pathDepth` supplied siblings in the direction determined by the submitted position. -/
theorem check_position_hash_digest (oracle : Oracle) (state : MachineState)
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
    readBuffer (checkEvaluation oracle (checkPositionHash state pathDepth)).1 256 32 =
      climb oracle.compression (leafDigest oracle.compression index salt value) path := by
  let ready := checkPositionState state
  let leaf := (checkEvaluation oracle (checkLeafSubroutineRun ready)).1
  have readyScratch : ready.getReg .x21 = 256 :=
    (check_position_register state .x21 (by decide)).trans scratch
  have readyPointer : ready.getReg .x8 = BitVec.ofNat 64 valueAddress :=
    (check_position_register state .x8 (by decide)).trans valuePointer
  have saltTag := check_position_salt_tag state proofAddress index scratch proofPointer
    proofAligned (by omega) (by omega) indexData
  have readySalt : readBuffer ready 256 16 = salt := saltTag.1.trans saltData
  have readyTag : readBuffer ready 272 8 = leafTag index := saltTag.2
  have readyOutside (address : Word) (outside : ∀ i < 4, address ≠ BitVec.ofNat 64 (256 + 8 * i)) :
      ready.getMem address = state.getMem address := check_position_outside state address scratch outside
  have readyHalf (address : Nat) (aligned : address % 8 = 0) (above : 352 ≤ address)
      (bounded : address + 32 < 2 ^ 64) : readBuffer ready address 32 = readBuffer state address 32 := by
    apply read_digest_congr _ _ _ aligned
    intro word hw
    apply readyOutside
    intro i hi
    exact word_outside_scratch address (8 * word) above (by omega) i (by omega)
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
    change (checkPositionState state).getReg .x25 = _
    rw [check_position_proof_pointer, proofPointer]
    exact (BitVec.ofNat_add proofAddress 16).symm
  have leafIndex : leaf.getReg .x20 = state.getMem (state.getReg .x24) := by
    rw [leafRegs.2 .x20 (by decide)]
    exact check_position_index state
  have leafOutside (address : Word) (outside : ∀ i < 12, address ≠ BitVec.ofNat 64 (256 + 8 * i)) :
      leaf.getMem address = state.getMem address :=
    (check_leaf_subroutine_outside oracle ready address readyScratch outside).trans
      (readyOutside address (fun i hi => outside i (by omega)))
  rw [check_position_hash_evaluation, read_buffer_memory_congr _ _ (check_target_memory _)]
  exact finish_check_path oracle state leaf pathDepth proofAddress path _ leafScratch leafPointer leafIndex
    leafOutside leafDigestEq proofAligned proofAbove proofBound pathLength pathData directions

private theorem check_path_phase_outside (oracle : Oracle) (leaf : MachineState) (pathDepth : Nat)
    (address : Word) (scratch : leaf.getReg .x21 = 256)
    (outside : ∀ i < 12, address ≠ BitVec.ofNat 64 (256 + 8 * i)) :
    (checkEvaluation oracle
      (checkPathLoop (checkPathInitializedState (leaf.setPC 4200)) pathDepth)).1.getMem address =
        leaf.getMem address := by
  have pathScratch : (checkPathInitializedState (leaf.setPC 4200)).getReg .x21 = 256 :=
    (check_path_setup_register (leaf.setPC 4200) .x21 (by decide)).trans scratch
  exact (check_path_loop_outside oracle (checkPathInitializedState (leaf.setPC 4200))
    pathDepth address pathScratch (fun i hi => outside i (by omega))).trans
      (congrFun (check_path_setup_memory (leaf.setPC 4200)) address)

set_option maxRecDepth 4096 in
/-- Computing one position does not modify any input buffer or the target digest table. -/
theorem check_position_hash_outside (oracle : Oracle) (state : MachineState) (pathDepth : Nat)
    (address : Word) (scratch : state.getReg .x21 = 256)
    (outside : ∀ i < 12, address ≠ BitVec.ofNat 64 (256 + 8 * i)) :
    (checkEvaluation oracle (checkPositionHash state pathDepth)).1.getMem address = state.getMem address := by
  let ready := checkPositionState state
  let leaf := (checkEvaluation oracle (checkLeafSubroutineRun ready)).1
  have readyScratch : ready.getReg .x21 = 256 :=
    (check_position_register state .x21 (by decide)).trans scratch
  have leafScratch : leaf.getReg .x21 = 256 :=
    ((check_leaf_subroutine_registers ready leaf (check_evaluation_support oracle _)).2 .x21 (by decide)).trans
      readyScratch
  have initialMemory : ready.getMem address = state.getMem address :=
    check_position_outside state address scratch (fun i hi => outside i (by omega))
  have leafMemory := check_leaf_subroutine_outside oracle ready address readyScratch outside
  rw [check_position_hash_evaluation]
  change (checkTargetState _).mem address = _
  rw [check_target_memory]
  exact (check_path_phase_outside oracle leaf pathDepth address leafScratch outside).trans
    (leafMemory.trans initialMemory)

/-- The four machine-word comparisons at `check-root` test exact digest equality against
the target at `targetAddress + 32 * (index.val / 2 ^ pathDepth)` (the commitment when
`pathDepth = 24`, or the level-7 cap slot when `pathDepth = 17`). -/
theorem check_position_comparison (oracle : Oracle) (state : MachineState)
    (pathDepth targetAddress : Nat) (index : Index)
    (depthPos : 0 < pathDepth) (depthBound : pathDepth ≤ 24)
    (depthReg : state.getReg .x30 = BitVec.ofNat 64 pathDepth)
    (scratch : state.getReg .x21 = 256)
    (targetPointer : state.getReg .x26 = BitVec.ofNat 64 targetAddress)
    (indexData : state.getMem (state.getReg .x24) = BitVec.ofNat 64 index.val)
    (targetAligned : targetAddress % 8 = 0) (targetAbove : 352 ≤ targetAddress)
    (targetBound : targetAddress + 32 * 2 ^ (24 - pathDepth) < 2 ^ 64) :
    let hashed := (checkEvaluation oracle (checkPositionHash state pathDepth)).1
    (∀ word < 4, hashed.getMem (hashed.getReg .x21 + BitVec.ofNat 64 (8 * word)) =
      hashed.getMem (hashed.getReg .x23 + BitVec.ofNat 64 (8 * word))) ↔
    readBuffer hashed 256 32 = readBuffer state (targetAddress + 32 * (index.val / 2 ^ pathDepth)) 32 := by
  let hashed := (checkEvaluation oracle (checkPositionHash state pathDepth)).1
  have regs := check_position_hash_registers pathDepth depthPos depthBound state hashed depthReg
    (check_evaluation_support oracle _)
  have hashedScratch : hashed.getReg .x21 = 256 := (regs.2.2.2.2 .x21 (by simp)).trans scratch
  have qBound : index.val / 2 ^ pathDepth < 2 ^ (24 - pathDepth) := by
    have hpow : 2 ^ pathDepth * 2 ^ (24 - pathDepth) = 2 ^ 24 := by
      rw [← Nat.pow_add, Nat.add_sub_of_le depthBound]
    have hlt : index.val < 2 ^ 24 := index.isLt
    exact (Nat.div_lt_iff_lt_mul (by positivity)).mpr (by rw [Nat.mul_comm, hpow]; exact hlt)
  have shiftVal : ((BitVec.ofNat 64 index.val >>> pathDepth) <<< 5) =
      BitVec.ofNat 64 (32 * (index.val / 2 ^ pathDepth)) := by
    apply BitVec.eq_of_toNat_eq
    have hlt : index.val < 2 ^ 24 := index.isLt
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
      Nat.shiftLeft_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : index.val < 2 ^ 64)]
    have h1 : index.val / 2 ^ pathDepth * 2 ^ 5 = 32 * (index.val / 2 ^ pathDepth) := by omega
    rw [h1]
  let slotAddr := targetAddress + 32 * (index.val / 2 ^ pathDepth)
  have hashedTarget : hashed.getReg .x23 = BitVec.ofNat 64 slotAddr := by
    rw [regs.2.2.2.1, targetPointer, indexData, shiftVal, ← BitVec.ofNat_add]
  have slotAligned : slotAddr % 8 = 0 := by dsimp [slotAddr]; omega
  have slotAbove : 352 ≤ slotAddr := by dsimp [slotAddr]; omega
  have slotBound : slotAddr + 32 < 2 ^ 64 := by
    dsimp [slotAddr]
    have : 32 * (index.val / 2 ^ pathDepth) + 32 ≤ 32 * 2 ^ (24 - pathDepth) := by omega
    omega
  have targetMemory : readBuffer hashed slotAddr 32 = readBuffer state slotAddr 32 := by
    apply read_digest_congr _ _ _ slotAligned
    intro word hw
    apply check_position_hash_outside oracle state pathDepth _ scratch
    intro i hi
    exact word_outside_scratch slotAddr (8 * word) slotAbove (by omega) i hi
  change (∀ word < 4, hashed.getMem (hashed.getReg .x21 + BitVec.ofNat 64 (8 * word)) =
    hashed.getMem (hashed.getReg .x23 + BitVec.ofNat 64 (8 * word))) ↔ _
  rw [← targetMemory, read_digest_eq_iff _ _ _ _ (by decide) slotAligned]
  constructor <;> intro words word hw
  · have agree := words word hw
    rw [hashedScratch, hashedTarget] at agree
    change hashed.getMem (BitVec.ofNat 64 256 + BitVec.ofNat 64 (8 * word)) = _ at agree
    rw [← BitVec.ofNat_add, ← BitVec.ofNat_add] at agree
    exact agree
  · have agree := words word hw
    rw [hashedScratch, hashedTarget]
    change hashed.getMem (BitVec.ofNat 64 256 + BitVec.ofNat 64 (8 * word)) = _
    rw [← BitVec.ofNat_add, ← BitVec.ofNat_add]
    exact agree

/-- With a consistent commitment heap, the actual checker reconstructs the ancestor at
height `pathDepth` (`heap 1` when `pathDepth = 24`, or `heap (128 + index / 2^17)` when
`pathDepth = 17`) from the 16-byte leaf salt and the `pathDepth` siblings copied by opening. -/
theorem check_position_heap_ancestor (oracle : Oracle) (state : MachineState)
    (pathDepth valueAddress proofAddress : Nat) (value : Entry) (salt : Salt)
    (heap : Nat → Digest) (index : Index)
    (depthBound : pathDepth ≤ 24)
    (scratch : state.getReg .x21 = 256)
    (valuePointer : state.getReg .x8 = BitVec.ofNat 64 valueAddress)
    (proofPointer : state.getReg .x25 = BitVec.ofNat 64 proofAddress)
    (valueAligned : valueAddress % 8 = 0) (proofAligned : proofAddress % 8 = 0)
    (valueAbove : 352 ≤ valueAddress) (proofAbove : 352 ≤ proofAddress)
    (valueBound : valueAddress + 256 < 2 ^ 64)
    (proofBound : proofAddress + (16 + 32 * pathDepth) < 2 ^ 64)
    (saltData : readBuffer state proofAddress 16 = salt)
    (valueData : ∀ block < 4, readBuffer state (valueAddress + 64 * block) 64 =
      value.extractLsb' (512 * block) 512)
    (indexData : state.getMem (state.getReg .x24) = BitVec.ofNat 64 index.val)
    (pathData : ∀ level < pathDepth, readBuffer state (proofAddress + 16 + 32 * level) 32 =
      heap (((2 ^ 24 + index.val) / 2 ^ level) ^^^ 1))
    (leafData : heap (2 ^ 24 + index.val) = leafDigest oracle.compression index salt value)
    (parents : ∀ parent, 0 < parent → parent < 2 ^ 24 →
      heap parent = combine oracle.compression (heap (2 * parent)) (heap (2 * parent + 1))) :
    readBuffer (checkEvaluation oracle (checkPositionHash state pathDepth)).1 256 32 =
      heap ((2 ^ 24 + index.val) / 2 ^ pathDepth) := by
  let path := heapPath heap (2 ^ 24 + index.val) pathDepth
  have pathLength : path.length = pathDepth := heap_path_length _ _ _
  have data (i : Nat) (hi : i < path.length) :
      readBuffer state (proofAddress + 16 + 32 * i) 32 = (path[i]'hi).2 := by
    have below : i < pathDepth := by rw [pathLength] at hi; exact hi
    have entry := heap_path_get heap (2 ^ 24 + index.val) pathDepth i below
    change readBuffer state (proofAddress + 16 + 32 * i) 32 =
      ((heapPath heap (2 ^ 24 + index.val) pathDepth)[i]'hi).2
    rw [entry]
    exact pathData i below
  have directions (i : Nat) (hi : i < path.length) :
      (state.getMem (state.getReg .x24)).getLsbD i = (path[i]'hi).1 := by
    have below : i < pathDepth := by rw [pathLength] at hi; exact hi
    have entry := heap_path_get heap (2 ^ 24 + index.val) pathDepth i below
    change (state.getMem (state.getReg .x24)).getLsbD i =
      ((heapPath heap (2 ^ 24 + index.val) pathDepth)[i]'hi).1
    rw [entry, indexData, BitVec.getLsbD_ofNat,
      heap_leaf_direction 24 index.val i index.isLt (by omega)]
    simp only [show i < 64 by omega, decide_true, Bool.true_and]
  have hashed := check_position_hash_digest oracle state pathDepth valueAddress proofAddress
    index value salt path scratch valuePointer proofPointer valueAligned proofAligned
    valueAbove proofAbove valueBound proofBound indexData saltData valueData pathLength data directions
  have heightLe : 2 ^ pathDepth ≤ 2 ^ 24 + index.val :=
    Nat.le_trans (Nat.pow_le_pow_right (by decide) depthBound) (by omega)
  exact hashed.trans ((congrArg (fun digest => climb oracle.compression digest path) leafData.symm).trans
    (reconstruct_heap_ancestor oracle.compression heap (2 ^ 24) parents pathDepth
      (2 ^ 24 + index.val) (by have hlt : index.val < 2 ^ 24 := index.isLt; omega) heightLe))

end CommitGolfCandidate
