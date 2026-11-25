import CommitGolfCandidate.CheckHonest

/-! Acceptance implies authentication of every supplied record, including adversarial
proof bytes. This is the machine-to-collision bridge needed for binding. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

/-- A fixed-height authentication record, with directions determined solely by its index. -/
def recordPath (index : Index) (siblings : Nat → Digest) : List (Bool × Digest) :=
  (List.range 24).map fun level => (index.val.testBit level, siblings level)

theorem record_path_length (index : Index) (siblings : Nat → Digest) :
    (recordPath index siblings).length = 24 := by
  simp only [recordPath, List.length_map, List.length_range]

theorem record_path_directions (index : Index) (siblings siblings' : Nat → Digest) :
    (recordPath index siblings).map Prod.fst = (recordPath index siblings').map Prod.fst := by
  simp only [recordPath, List.map_map, Function.comp_def]

/-- The reference root computed by one supplied salt/value/path record. -/
def recordRoot (compress : Compression) (value : Entry) (salt : Digest)
    (index : Index) (siblings : Nat → Digest) : Digest :=
  climb compress (leafDigest compress salt value) (recordPath index siblings)

attribute [local irreducible] checkPositionHash checkEvaluation nextCheckState
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- One actual checker iteration computes the root of its supplied record. -/
theorem check_record_root (oracle : Oracle) (state : MachineState)
    (valueAddress proofAddress : Nat) (value : Entry) (salt : Digest)
    (index : Index) (siblings : Nat → Digest)
    (scratch : state.getReg .x21 = 256)
    (valuePointer : state.getReg .x8 = BitVec.ofNat 64 valueAddress)
    (proofPointer : state.getReg .x25 = BitVec.ofNat 64 proofAddress)
    (valueAligned : valueAddress%8 = 0) (proofAligned : proofAddress%8 = 0)
    (valueAbove : 352 ≤ valueAddress) (proofAbove : 352 ≤ proofAddress)
    (valueBound : valueAddress+256 < 2^64) (proofBound : proofAddress+800 < 2^64)
    (valueData : ∀ block < 4, readBuffer state (valueAddress+64*block) 64 =
      value.extractLsb' (512*block) 512)
    (saltData : readBuffer state proofAddress 32 = salt)
    (indexData : state.getMem (state.getReg .x24) = BitVec.ofNat 64 index.val)
    (pathData : ∀ level < 24, readBuffer state (proofAddress+32+32*level) 32 = siblings level) :
    readBuffer (checkEvaluation oracle (checkPositionHash state)).1 256 32 =
      recordRoot oracle.compression value salt index siblings := by
  apply check_position_hash_digest oracle state valueAddress proofAddress value salt
    (recordPath index siblings) scratch valuePointer proofPointer valueAligned proofAligned
    valueAbove proofAbove valueBound proofBound saltData valueData (record_path_length _ _)
  · intro level inside
    have below : level < 24 := by rw [record_path_length] at inside; exact inside
    simpa only [recordPath, List.getElem_map, List.getElem_range] using pathData level below
  · intro level inside
    have below : level < 24 := by rw [record_path_length] at inside; exact inside
    rw [indexData, BitVec.getLsbD_ofNat]
    simp only [recordPath, List.getElem_map, List.getElem_range,
      show level < 64 by omega, decide_true, Bool.true_and]

/-- If the full checker loop accepts, every supplied record reconstructs its root.
The input values, salts, and siblings are arbitrary; they need not be honestly generated. -/
theorem check_loop_sound (oracle : Oracle) (state : MachineState)
    (root : Digest) (values : Nat → Entry) (salts : Nat → Digest)
    (indices : Nat → Index) (siblings : Nat → Nat → Digest)
    (rootAddress valueAddress proofAddress indexAddress count : Nat)
    (scratch : state.getReg .x21 = 256)
    (rootPointer : state.getReg .x26 = BitVec.ofNat 64 rootAddress)
    (valuePointer : state.getReg .x8 = BitVec.ofNat 64 valueAddress)
    (proofPointer : state.getReg .x25 = BitVec.ofNat 64 proofAddress)
    (indexPointer : state.getReg .x24 = BitVec.ofNat 64 indexAddress)
    (rootAligned : rootAddress%8 = 0) (valueAligned : valueAddress%8 = 0)
    (proofAligned : proofAddress%8 = 0)
    (rootAbove : 352 ≤ rootAddress) (valueAbove : 352 ≤ valueAddress)
    (proofAbove : 352 ≤ proofAddress) (indexAbove : 352 ≤ indexAddress)
    (rootBound : rootAddress+32 < 2^64) (valueBound : valueAddress+256*count < 2^64)
    (proofBound : proofAddress+800*count < 2^64) (indexBound : indexAddress+8*count < 2^64)
    (rootData : readBuffer state rootAddress 32 = root)
    (indexData : ∀ ordinal < count, state.getMem (BitVec.ofNat 64 (indexAddress+8*ordinal)) =
      BitVec.ofNat 64 (indices ordinal).val)
    (valueData : ∀ ordinal < count, ∀ block < 4,
      readBuffer state (valueAddress+256*ordinal+64*block) 64 =
        (values ordinal).extractLsb' (512*block) 512)
    (saltData : ∀ ordinal < count, readBuffer state (proofAddress+800*ordinal) 32 = salts ordinal)
    (pathData : ∀ ordinal < count, ∀ level < 24,
      readBuffer state (proofAddress+800*ordinal+32+32*level) 32 = siblings ordinal level)
    (accepted : checkLoopAccepts oracle count state = true) :
    ∀ ordinal < count,
      recordRoot oracle.compression (values ordinal) (salts ordinal) (indices ordinal) (siblings ordinal) = root := by
  induction count generalizing state values salts indices siblings valueAddress proofAddress indexAddress with
  | zero => intro ordinal inside; omega
  | succ count ih =>
    have acceptedParts : rootWordsMatch (checkEvaluation oracle (checkPositionHash state)).1 = true ∧
        checkLoopAccepts oracle count (nextCheckState oracle state) = true := by
      simpa only [checkLoopAccepts, nextCheckState, Bool.and_eq_true] using accepted
    have reconstructed := check_record_root oracle state valueAddress proofAddress
      (values 0) (salts 0) (indices 0) (siblings 0) scratch valuePointer proofPointer
      valueAligned proofAligned valueAbove proofAbove (by omega) (by omega)
      (by simpa only [Nat.mul_zero, Nat.add_zero] using valueData 0 (by omega))
      (by simpa only [Nat.mul_zero, Nat.add_zero] using saltData 0 (by omega))
      (by rw [indexPointer]; simpa only [Nat.mul_zero, Nat.add_zero] using indexData 0 (by omega))
      (by simpa only [Nat.mul_zero, Nat.add_zero] using pathData 0 (by omega))
    have first : recordRoot oracle.compression (values 0) (salts 0) (indices 0) (siblings 0) = root :=
      reconstructed.symm.trans (((check_position_comparison oracle state rootAddress scratch rootPointer
        rootAligned rootAbove rootBound).mp ((root_words_match_iff _).mp acceptedParts.1)).trans rootData)
    let next := nextCheckState oracle state
    have regs := next_check_registers oracle state
    have nextValues : next.getReg .x8 = BitVec.ofNat 64 (valueAddress+256) := by
      rw [regs.1, valuePointer, BitVec.ofNat_add]; rfl
    have nextProof : next.getReg .x25 = BitVec.ofNat 64 (proofAddress+800) := by
      rw [regs.2.1, proofPointer, BitVec.ofNat_add]; rfl
    have nextIndices : next.getReg .x24 = BitVec.ofNat 64 (indexAddress+8) := by
      rw [regs.2.2.1, indexPointer, BitVec.ofNat_add]; rfl
    have nextRoot : readBuffer next rootAddress 32 = root :=
      (next_check_digest oracle state rootAddress scratch rootAligned rootAbove rootBound).trans rootData
    have nextIndexData (ordinal : Nat) (inside : ordinal < count) :
        next.getMem (BitVec.ofNat 64 (indexAddress+8+8*ordinal)) = BitVec.ofNat 64 (indices (ordinal+1)).val := by
      rw [next_check_memory oracle state _ scratch (by omega) (by omega)]
      convert indexData (ordinal+1) (by omega) using 1
      congr 2
      omega
    have nextValueData (ordinal : Nat) (inside : ordinal < count) (block : Nat) (blockBound : block < 4) :
        readBuffer next (valueAddress+256+256*ordinal+64*block) 64 =
          (values (ordinal+1)).extractLsb' (512*block) 512 := by
      rw [read_compression_halves _ _ (by omega),
        next_check_digest oracle state (valueAddress+256+256*ordinal+64*block+32) scratch (by omega) (by omega) (by omega),
        next_check_digest oracle state (valueAddress+256+256*ordinal+64*block) scratch (by omega) (by omega) (by omega),
        ← read_compression_halves _ _ (by omega)]
      convert valueData (ordinal+1) (by omega) block blockBound using 1
      congr 1
      omega
    have nextSaltData (ordinal : Nat) (inside : ordinal < count) :
        readBuffer next (proofAddress+800+800*ordinal) 32 = salts (ordinal+1) := by
      rw [next_check_digest oracle state _ scratch (by omega) (by omega) (by omega)]
      convert saltData (ordinal+1) (by omega) using 1
      congr 1
      omega
    have nextPathData (ordinal : Nat) (inside : ordinal < count) (level : Nat) (levelBound : level < 24) :
        readBuffer next (proofAddress+800+800*ordinal+32+32*level) 32 = siblings (ordinal+1) level := by
      rw [next_check_digest oracle state _ scratch (by omega) (by omega) (by omega)]
      convert pathData (ordinal+1) (by omega) level levelBound using 1
      congr 1
      omega
    intro ordinal inside
    cases ordinal with
    | zero => exact first
    | succ ordinal =>
      exact ih next (fun k => values (k+1)) (fun k => salts (k+1)) (fun k => indices (k+1))
        (fun k => siblings (k+1)) (valueAddress+256) (proofAddress+800) (indexAddress+8)
        (regs.2.2.2.1.trans scratch) (regs.2.2.2.2.trans rootPointer)
        nextValues nextProof nextIndices (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) nextRoot nextIndexData nextValueData nextSaltData nextPathData
        acceptedParts.2 ordinal (by omega)

end CommitGolfCandidate
