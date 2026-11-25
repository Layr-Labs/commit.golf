import CommitGolfCandidate.CheckHonest

/-! Acceptance implies authentication of every supplied record, including adversarial
proof bytes. Covers both depth-24 normal openings and depth-17 cap-table openings. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

/-- Prefix of `pathDepth` authentication levels, with directions determined solely by `index`. -/
def recordPathPrefix (pathDepth : Nat) (index : Index) (siblings : Nat → Digest) :
    List (Bool × Digest) :=
  (List.range pathDepth).map fun level => (index.val.testBit level, siblings level)

theorem record_path_prefix_length (pathDepth : Nat) (index : Index) (siblings : Nat → Digest) :
    (recordPathPrefix pathDepth index siblings).length = pathDepth := by
  simp only [recordPathPrefix, List.length_map, List.length_range]

/-- A fixed-height 24-level authentication record, with directions determined solely by its index. -/
def recordPath (index : Index) (siblings : Nat → Digest) : List (Bool × Digest) :=
  recordPathPrefix 24 index siblings

theorem record_path_length (index : Index) (siblings : Nat → Digest) :
    (recordPath index siblings).length = 24 :=
  record_path_prefix_length 24 index siblings

theorem record_path_directions (index : Index) (siblings siblings' : Nat → Digest) :
    (recordPath index siblings).map Prod.fst = (recordPath index siblings').map Prod.fst := by
  simp only [recordPath, recordPathPrefix, List.map_map, Function.comp_def]

/-- The reference ancestor at height `pathDepth` computed from one salt/value/path record. -/
def recordAncestor (compress : Compression) (pathDepth : Nat) (value : Entry) (salt : Digest)
    (index : Index) (siblings : Nat → Digest) : Digest :=
  climb compress (leafDigest compress salt value) (recordPathPrefix pathDepth index siblings)

/-- The reference root computed by one supplied 24-level salt/value/path record. -/
def recordRoot (compress : Compression) (value : Entry) (salt : Digest)
    (index : Index) (siblings : Nat → Digest) : Digest :=
  climb compress (leafDigest compress salt value) (recordPath index siblings)

attribute [local irreducible] checkPositionHash checkEvaluation nextCheckState
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- One actual checker iteration computes the height-`pathDepth` ancestor of its supplied record. -/
theorem check_record_ancestor (oracle : Oracle) (state : MachineState)
    (pathDepth valueAddress proofAddress : Nat) (value : Entry) (salt : Digest)
    (index : Index) (siblings : Nat → Digest)
    (depthBound : pathDepth ≤ 24)
    (scratch : state.getReg .x21 = 256)
    (valuePointer : state.getReg .x8 = BitVec.ofNat 64 valueAddress)
    (proofPointer : state.getReg .x25 = BitVec.ofNat 64 proofAddress)
    (valueAligned : valueAddress % 8 = 0) (proofAligned : proofAddress % 8 = 0)
    (valueAbove : 352 ≤ valueAddress) (proofAbove : 352 ≤ proofAddress)
    (valueBound : valueAddress + 256 < 2 ^ 64)
    (proofBound : proofAddress + (32 + 32 * pathDepth) < 2 ^ 64)
    (valueData : ∀ block < 4, readBuffer state (valueAddress + 64 * block) 64 =
      value.extractLsb' (512 * block) 512)
    (saltData : readBuffer state proofAddress 32 = salt)
    (indexData : state.getMem (state.getReg .x24) = BitVec.ofNat 64 index.val)
    (pathData : ∀ level < pathDepth,
      readBuffer state (proofAddress + 32 + 32 * level) 32 = siblings level) :
    readBuffer (checkEvaluation oracle (checkPositionHash state pathDepth)).1 256 32 =
      recordAncestor oracle.compression pathDepth value salt index siblings := by
  apply check_position_hash_digest oracle state pathDepth valueAddress proofAddress value salt
    (recordPathPrefix pathDepth index siblings) scratch valuePointer proofPointer
    valueAligned proofAligned valueAbove proofAbove valueBound proofBound saltData valueData
    (record_path_prefix_length _ _ _)
  · intro level inside
    have below : level < pathDepth := by rw [record_path_prefix_length] at inside; exact inside
    simpa only [recordPathPrefix, List.getElem_map, List.getElem_range] using pathData level below
  · intro level inside
    have below : level < pathDepth := by rw [record_path_prefix_length] at inside; exact inside
    rw [indexData, BitVec.getLsbD_ofNat]
    simp only [recordPathPrefix, List.getElem_map, List.getElem_range,
      show level < 64 by omega, decide_true, Bool.true_and]

/-- If the unified checker loop accepts at `pathDepth`, every supplied record authenticates
to its target slot `targets (index / 2 ^ pathDepth)`. -/
theorem check_loop_sound (oracle : Oracle) (state : MachineState)
    (targets : Nat → Digest) (values : Nat → Entry) (salts : Nat → Digest)
    (indices : Nat → Index) (siblings : Nat → Nat → Digest)
    (pathDepth targetAddress valueAddress proofAddress indexAddress count : Nat)
    (depthPos : 0 < pathDepth) (depthBound : pathDepth ≤ 24)
    (depthReg : state.getReg .x30 = BitVec.ofNat 64 pathDepth)
    (scratch : state.getReg .x21 = 256)
    (targetPointer : state.getReg .x26 = BitVec.ofNat 64 targetAddress)
    (valuePointer : state.getReg .x8 = BitVec.ofNat 64 valueAddress)
    (proofPointer : state.getReg .x25 = BitVec.ofNat 64 proofAddress)
    (indexPointer : state.getReg .x24 = BitVec.ofNat 64 indexAddress)
    (targetAligned : targetAddress % 8 = 0) (valueAligned : valueAddress % 8 = 0)
    (proofAligned : proofAddress % 8 = 0)
    (targetAbove : 352 ≤ targetAddress) (valueAbove : 352 ≤ valueAddress)
    (proofAbove : 352 ≤ proofAddress) (indexAbove : 352 ≤ indexAddress)
    (targetBound : targetAddress + 32 * 2 ^ (24 - pathDepth) < 2 ^ 64)
    (valueBound : valueAddress + 256 * count < 2 ^ 64)
    (proofBound : proofAddress + (32 + 32 * pathDepth) * count < 2 ^ 64)
    (indexBound : indexAddress + 8 * count < 2 ^ 64)
    (targetData : ∀ slot < 2 ^ (24 - pathDepth),
      readBuffer state (targetAddress + 32 * slot) 32 = targets slot)
    (indexData : ∀ ordinal < count, state.getMem (BitVec.ofNat 64 (indexAddress + 8 * ordinal)) =
      BitVec.ofNat 64 (indices ordinal).val)
    (valueData : ∀ ordinal < count, ∀ block < 4,
      readBuffer state (valueAddress + 256 * ordinal + 64 * block) 64 =
        (values ordinal).extractLsb' (512 * block) 512)
    (saltData : ∀ ordinal < count,
      readBuffer state (proofAddress + (32 + 32 * pathDepth) * ordinal) 32 = salts ordinal)
    (pathData : ∀ ordinal < count, ∀ level < pathDepth,
      readBuffer state (proofAddress + (32 + 32 * pathDepth) * ordinal + 32 + 32 * level) 32 =
        siblings ordinal level)
    (accepted : checkLoopAccepts oracle count pathDepth state = true) :
    ∀ ordinal < count,
      recordAncestor oracle.compression pathDepth (values ordinal) (salts ordinal)
        (indices ordinal) (siblings ordinal) = targets ((indices ordinal).val / 2 ^ pathDepth) := by
  induction count generalizing state values salts indices siblings valueAddress proofAddress indexAddress with
  | zero => intro ordinal inside; omega
  | succ count ih =>
    have hrec : (32 + 32 * pathDepth) * (count + 1) =
        (32 + 32 * pathDepth) * count + (32 + 32 * pathDepth) := Nat.mul_succ _ _
    have acceptedParts : rootWordsMatch (checkEvaluation oracle (checkPositionHash state pathDepth)).1 = true ∧
        checkLoopAccepts oracle count pathDepth (nextCheckState oracle pathDepth state) = true := by
      simpa only [checkLoopAccepts, nextCheckState, Bool.and_eq_true] using accepted
    have idx0 : state.getMem (state.getReg .x24) = BitVec.ofNat 64 (indices 0).val := by
      rw [indexPointer]; simpa only [Nat.mul_zero, Nat.add_zero] using indexData 0 (by omega)
    have reconstructed := check_record_ancestor oracle state pathDepth valueAddress proofAddress
      (values 0) (salts 0) (indices 0) (siblings 0) depthBound scratch valuePointer proofPointer
      valueAligned proofAligned valueAbove proofAbove (by omega) (by omega)
      (by simpa only [Nat.mul_zero, Nat.add_zero] using valueData 0 (by omega))
      (by simpa only [Nat.mul_zero, Nat.add_zero] using saltData 0 (by omega))
      idx0
      (by simpa only [Nat.mul_zero, Nat.add_zero] using pathData 0 (by omega))
    have qBound : (indices 0).val / 2 ^ pathDepth < 2 ^ (24 - pathDepth) := by
      have hpow : 2 ^ pathDepth * 2 ^ (24 - pathDepth) = 2 ^ 24 := by
        rw [← Nat.pow_add, Nat.add_sub_of_le depthBound]
      have hlt : (indices 0).val < 2 ^ 24 := (indices 0).isLt
      exact (Nat.div_lt_iff_lt_mul (by positivity)).mpr (by rw [Nat.mul_comm, hpow]; exact hlt)
    have first : recordAncestor oracle.compression pathDepth (values 0) (salts 0)
        (indices 0) (siblings 0) = targets ((indices 0).val / 2 ^ pathDepth) :=
      reconstructed.symm.trans (((check_position_comparison oracle state pathDepth targetAddress
        (indices 0) depthPos depthBound depthReg scratch targetPointer idx0
        targetAligned targetAbove targetBound).mp ((root_words_match_iff _).mp acceptedParts.1)).trans
          (targetData _ qBound))
    let next := nextCheckState oracle pathDepth state
    have regs := next_check_registers oracle pathDepth state depthPos depthBound depthReg
    have nextValues : next.getReg .x8 = BitVec.ofNat 64 (valueAddress + 256) := by
      rw [regs.1, valuePointer, BitVec.ofNat_add]; rfl
    have nextProof : next.getReg .x25 = BitVec.ofNat 64 (proofAddress + (32 + 32 * pathDepth)) := by
      rw [regs.2.1, proofPointer, ← BitVec.ofNat_add]
    have nextIndices : next.getReg .x24 = BitVec.ofNat 64 (indexAddress + 8) := by
      rw [regs.2.2.1, indexPointer, BitVec.ofNat_add]; rfl
    have nextTargetData (slot : Nat) (hs : slot < 2 ^ (24 - pathDepth)) :
        readBuffer next (targetAddress + 32 * slot) 32 = targets slot := by
      have sBound : targetAddress + 32 * slot + 32 < 2 ^ 64 := by
        have : 32 * slot + 32 ≤ 32 * 2 ^ (24 - pathDepth) := by omega
        omega
      exact (next_check_digest oracle pathDepth state (targetAddress + 32 * slot) scratch
        (by omega) (by omega) sBound).trans (targetData slot hs)
    have nextIndexData (ordinal : Nat) (inside : ordinal < count) :
        next.getMem (BitVec.ofNat 64 (indexAddress + 8 + 8 * ordinal)) =
          BitVec.ofNat 64 (indices (ordinal + 1)).val := by
      rw [next_check_memory oracle pathDepth state _ scratch (by omega) (by omega)]
      convert indexData (ordinal + 1) (by omega) using 1
      congr 2
      omega
    have nextValueData (ordinal : Nat) (inside : ordinal < count) (block : Nat) (blockBound : block < 4) :
        readBuffer next (valueAddress + 256 + 256 * ordinal + 64 * block) 64 =
          (values (ordinal + 1)).extractLsb' (512 * block) 512 := by
      rw [read_compression_halves _ _ (by omega),
        next_check_digest oracle pathDepth state (valueAddress + 256 + 256 * ordinal + 64 * block + 32)
          scratch (by omega) (by omega) (by omega),
        next_check_digest oracle pathDepth state (valueAddress + 256 + 256 * ordinal + 64 * block)
          scratch (by omega) (by omega) (by omega),
        ← read_compression_halves _ _ (by omega)]
      convert valueData (ordinal + 1) (by omega) block blockBound using 1
      congr 1
      omega
    have nextSaltData (ordinal : Nat) (inside : ordinal < count) :
        readBuffer next (proofAddress + (32 + 32 * pathDepth) + (32 + 32 * pathDepth) * ordinal) 32 =
          salts (ordinal + 1) := by
      have hord : (32 + 32 * pathDepth) * (ordinal + 1) ≤ (32 + 32 * pathDepth) * count :=
        Nat.mul_le_mul_left _ (by omega)
      have hmul : (32 + 32 * pathDepth) * (ordinal + 1) =
          (32 + 32 * pathDepth) * ordinal + (32 + 32 * pathDepth) := Nat.mul_succ _ _
      have hmod8 : ((32 + 32 * pathDepth) * ordinal) % 8 = 0 := by
        rw [show 32 + 32 * pathDepth = 8 * (4 + 4 * pathDepth) by omega, Nat.mul_assoc]
        exact Nat.mul_mod_right 8 _
      rw [next_check_digest oracle pathDepth state _ scratch (by omega) (by omega) (by omega)]
      convert saltData (ordinal + 1) (by omega) using 1
      congr 1
      omega
    have nextPathData (ordinal : Nat) (inside : ordinal < count) (level : Nat) (levelBound : level < pathDepth) :
        readBuffer next
          (proofAddress + (32 + 32 * pathDepth) + (32 + 32 * pathDepth) * ordinal + 32 + 32 * level) 32 =
          siblings (ordinal + 1) level := by
      have hord : (32 + 32 * pathDepth) * (ordinal + 1) ≤ (32 + 32 * pathDepth) * count :=
        Nat.mul_le_mul_left _ (by omega)
      have hmul : (32 + 32 * pathDepth) * (ordinal + 1) =
          (32 + 32 * pathDepth) * ordinal + (32 + 32 * pathDepth) := Nat.mul_succ _ _
      have hmod8 : ((32 + 32 * pathDepth) * ordinal) % 8 = 0 := by
        rw [show 32 + 32 * pathDepth = 8 * (4 + 4 * pathDepth) by omega, Nat.mul_assoc]
        exact Nat.mul_mod_right 8 _
      rw [next_check_digest oracle pathDepth state _ scratch (by omega) (by omega) (by omega)]
      convert pathData (ordinal + 1) (by omega) level levelBound using 1
      congr 1
      omega
    intro ordinal inside
    cases ordinal with
    | zero => exact first
    | succ ordinal =>
      exact ih next (fun k => values (k + 1)) (fun k => salts (k + 1)) (fun k => indices (k + 1))
        (fun k => siblings (k + 1)) (valueAddress + 256) (proofAddress + (32 + 32 * pathDepth))
        (indexAddress + 8) (regs.2.2.2.2.2.trans depthReg) (regs.2.2.2.1.trans scratch)
        (regs.2.2.2.2.1.trans targetPointer) nextValues nextProof nextIndices
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        nextTargetData nextIndexData nextValueData nextSaltData nextPathData
        acceptedParts.2 ordinal (by omega)

end CommitGolfCandidate
