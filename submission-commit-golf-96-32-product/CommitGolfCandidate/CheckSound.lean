import CommitGolfCandidate.CheckInput

/-! The position loop accepts exactly when every supplied record climbs to its supplied
cap node. Both directions hold for adversarial proof bytes and every fixed oracle;
this is the machine-to-collision bridge for binding and the completeness bridge. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 8192

/-- A fixed-height authentication record, with directions determined solely by its index. -/
def recordPath (index : Index) (siblings : Nat → Digest) : List (Bool × Digest) :=
  (List.range PATH_LEVELS).map fun level => (index.val.testBit level, siblings level)

theorem record_path_length (index : Index) (siblings : Nat → Digest) :
    (recordPath index siblings).length = PATH_LEVELS := by
  simp only [recordPath, List.length_map, List.length_range]

theorem record_path_directions (index : Index) (siblings siblings' : Nat → Digest) :
    (recordPath index siblings).map Prod.fst = (recordPath index siblings').map Prod.fst := by
  simp only [recordPath, List.map_map, Function.comp_def]

/-- The reference cap node computed by one supplied salt/value/path record. -/
def recordRoot (compress : Compression) (value : Entry) (salt : Digest)
    (index : Index) (siblings : Nat → Digest) : Digest :=
  climb compress (leafDigest compress salt value) (recordPath index siblings)

attribute [local irreducible] checkPositionHash checkEvaluation nextCheckState
set_option maxHeartbeats 1000000

/-- One actual checker iteration computes the cap node of its supplied record. -/
theorem check_record_root (oracle : Oracle) (state : MachineState)
    (valueAddress proofAddress : Nat) (value : Entry) (salt : Digest)
    (index : Index) (siblings : Nat → Digest)
    (scratch : state.getReg .x21 = 256)
    (valuePointer : state.getReg .x8 = BitVec.ofNat 64 valueAddress)
    (proofPointer : state.getReg .x25 = BitVec.ofNat 64 proofAddress)
    (valueAligned : valueAddress%8 = 0) (proofAligned : proofAddress%8 = 0)
    (valueAbove : 352 ≤ valueAddress) (proofAbove : 352 ≤ proofAddress)
    (valueBound : valueAddress+256 < 2^64) (proofBound : proofAddress+568 < 2^64)
    (valueData : ∀ block < 4, readBuffer state (valueAddress+64*block) 64 =
      value.extractLsb' (512*block) 512)
    (saltData : saltState (readBuffer state proofAddress 24) = salt)
    (indexData : state.getMem (state.getReg .x24) = BitVec.ofNat 64 index.val)
    (pathData : ∀ level < 17, readBuffer state (proofAddress+24+32*level) 32 = siblings level) :
    readBuffer (positionHashState oracle state) 256 32 =
      recordRoot oracle.compression value salt index siblings := by
  rw [← saltData]
  apply check_position_hash_digest oracle state valueAddress proofAddress value
    (readBuffer state proofAddress 24)
    (recordPath index siblings) scratch valuePointer proofPointer valueAligned proofAligned
    valueAbove proofAbove valueBound proofBound rfl valueData (record_path_length _ _)
  · intro level inside
    have below : level < 17 := by rw [record_path_length] at inside; exact inside
    simpa only [recordPath, List.getElem_map, List.getElem_range] using pathData level below
  · intro level inside
    have below : level < 17 := by rw [record_path_length] at inside; exact inside
    rw [indexData, BitVec.getLsbD_ofNat]
    simp only [recordPath, List.getElem_map, List.getElem_range,
      show level < 64 by omega, decide_true, Bool.true_and]

private theorem outside_scratch (address : Nat) (above : 352 ≤ address) (bounded : address < 2^64) :
    ∀ i < 12, BitVec.ofNat 64 address ≠ BitVec.ofNat 64 (256+8*i) := by
  intro i hi equal
  have natural := congrArg BitVec.toNat equal
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bounded,
    Nat.mod_eq_of_lt (by omega : 256+8*i < 2^64)] at natural
  omega

theorem next_check_digest (oracle : Oracle) (state : MachineState) (address : Nat)
    (scratch : state.getReg .x21 = 256) (aligned : address%8 = 0)
    (above : 352 ≤ address) (bounded : address+32 < 2^64) :
    readBuffer (nextCheckState oracle state) address 32 = readBuffer state address 32 := by
  apply read_digest_congr _ _ _ aligned
  intro word inside
  exact next_check_outside oracle state _ scratch (outside_scratch _ (by omega) (by omega))

theorem next_check_salt (oracle : Oracle) (state : MachineState) (address : Nat)
    (scratch : state.getReg .x21 = 256) (aligned : address%8 = 0)
    (above : 352 ≤ address) (bounded : address+24 < 2^64) :
    readBuffer (nextCheckState oracle state) address 24 = readBuffer state address 24 := by
  apply read_salt_congr _ _ _ _ aligned aligned
  intro word inside
  exact next_check_outside oracle state _ scratch (outside_scratch _ (by omega) (by omega))

/-- One position passes its comparison exactly when its climbed digest equals the
supplied cap node selected by the index's top bits. -/
theorem check_position_accepts (oracle : Oracle) (state : MachineState) (capAddress index : Nat)
    (scratch : state.getReg .x21 = 256)
    (capPointer : state.getReg .x30 = BitVec.ofNat 64 capAddress)
    (capAligned : capAddress % 8 = 0) (capAbove : 352 ≤ capAddress)
    (capBound : capAddress + 4096 < 2^64) (indexSmall : index < 2^24)
    (indexData : state.getMem (state.getReg .x24) = BitVec.ofNat 64 index) :
    rootWordsMatch false (positionSelectState oracle state) = true ↔
      readBuffer (positionHashState oracle state) 256 32 =
        readBuffer state (capAddress + 32 * (index / 2^17)) 32 := by
  have toNatEq : (state.getMem (state.getReg .x24)).toNat = index := by
    rw [indexData, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have small : (state.getMem (state.getReg .x24)).toNat < 2^24 := by rw [toNatEq]; exact indexSmall
  have node : index / 2^17 < 128 := by omega
  have pointer : (positionSelectState oracle state).getReg (compareReg false) =
      BitVec.ofNat 64 (capAddress + 32 * (index / 2^17)) := by
    change (positionSelectState oracle state).getReg .x22 = _
    rw [position_select_node oracle state small, capPointer, toNatEq, ← BitVec.ofNat_add]
  rw [root_words_match_iff, check_compare_digest false _ _ (position_select_scratch oracle state scratch)
    pointer (by omega)]
  have selMem := position_select_memory oracle state
  rw [read_buffer_memory_congr _ _ selMem, read_buffer_memory_congr _ _ selMem]
  have outside : readBuffer (positionHashState oracle state) (capAddress + 32 * (index / 2^17)) 32 =
      readBuffer state (capAddress + 32 * (index / 2^17)) 32 := by
    apply read_digest_congr _ _ _ (by omega)
    intro word hw
    exact check_position_hash_outside oracle state _ scratch
      (outside_scratch _ (by omega) (by omega))
  rw [outside]

/-- The real position loop accepts exactly when every supplied record climbs to its
supplied cap node. Values, salts, siblings and cap nodes are arbitrary input bytes. -/
theorem check_loop_accepts_iff (oracle : Oracle) (state : MachineState) (cap : Nat → Digest)
    (values : Nat → Entry) (salts : Nat → Digest)
    (indices : Nat → Index) (siblings : Nat → Nat → Digest)
    (capAddress valueAddress proofAddress indexAddress count : Nat)
    (scratch : state.getReg .x21 = 256)
    (capPointer : state.getReg .x30 = BitVec.ofNat 64 capAddress)
    (valuePointer : state.getReg .x8 = BitVec.ofNat 64 valueAddress)
    (proofPointer : state.getReg .x25 = BitVec.ofNat 64 proofAddress)
    (indexPointer : state.getReg .x24 = BitVec.ofNat 64 indexAddress)
    (capAligned : capAddress%8 = 0) (valueAligned : valueAddress%8 = 0)
    (proofAligned : proofAddress%8 = 0)
    (capAbove : 352 ≤ capAddress) (valueAbove : 352 ≤ valueAddress)
    (proofAbove : 352 ≤ proofAddress) (indexAbove : 352 ≤ indexAddress)
    (capBound : capAddress+4096 < 2^64) (valueBound : valueAddress+256*count < 2^64)
    (proofBound : proofAddress+568*count < 2^64) (indexBound : indexAddress+8*count < 2^64)
    (capData : ∀ node < 128, readBuffer state (capAddress+32*node) 32 = cap node)
    (indexData : ∀ ordinal < count, state.getMem (BitVec.ofNat 64 (indexAddress+8*ordinal)) =
      BitVec.ofNat 64 (indices ordinal).val)
    (valueData : ∀ ordinal < count, ∀ block < 4,
      readBuffer state (valueAddress+256*ordinal+64*block) 64 =
        (values ordinal).extractLsb' (512*block) 512)
    (saltData : ∀ ordinal < count,
      saltState (readBuffer state (proofAddress+568*ordinal) 24) = salts ordinal)
    (pathData : ∀ ordinal < count, ∀ level < 17,
      readBuffer state (proofAddress+568*ordinal+24+32*level) 32 = siblings ordinal level) :
    checkLoopAccepts oracle count state = true ↔
      ∀ ordinal < count, recordRoot oracle.compression (values ordinal) (salts ordinal)
        (indices ordinal) (siblings ordinal) = cap ((indices ordinal).val / 2^PATH_LEVELS) := by
  induction count generalizing state values salts indices siblings valueAddress proofAddress
    indexAddress with
  | zero => simp [checkLoopAccepts]
  | succ count ih =>
    have reconstructed := check_record_root oracle state valueAddress proofAddress
      (values 0) (salts 0) (indices 0) (siblings 0) scratch valuePointer proofPointer
      valueAligned proofAligned valueAbove proofAbove (by omega) (by omega)
      (by simpa only [Nat.mul_zero, Nat.add_zero] using valueData 0 (by omega))
      (by simpa only [Nat.mul_zero, Nat.add_zero] using saltData 0 (by omega))
      (by rw [indexPointer]; simpa only [Nat.mul_zero, Nat.add_zero] using indexData 0 (by omega))
      (by simpa only [Nat.mul_zero, Nat.add_zero] using pathData 0 (by omega))
    have indexSmall : (indices 0).val < 2^24 := (indices 0).isLt
    have first : rootWordsMatch false (positionSelectState oracle state) = true ↔
        recordRoot oracle.compression (values 0) (salts 0) (indices 0) (siblings 0) =
          cap ((indices 0).val / 2^PATH_LEVELS) := by
      rw [check_position_accepts oracle state capAddress (indices 0).val scratch capPointer
        capAligned capAbove capBound indexSmall
        (by rw [indexPointer]; simpa only [Nat.mul_zero, Nat.add_zero] using indexData 0 (by omega)),
        reconstructed, capData _ (by omega)]
    let next := nextCheckState oracle state
    have regs := next_check_registers oracle state
    have nextValues : next.getReg .x8 = BitVec.ofNat 64 (valueAddress+256) := by
      rw [regs.1, valuePointer, BitVec.ofNat_add]; rfl
    have nextProof : next.getReg .x25 = BitVec.ofNat 64 (proofAddress+568) := by
      rw [regs.2.1, proofPointer, BitVec.ofNat_add]; rfl
    have nextIndices : next.getReg .x24 = BitVec.ofNat 64 (indexAddress+8) := by
      rw [regs.2.2.1, indexPointer, BitVec.ofNat_add]; rfl
    have nextScratch : next.getReg .x21 = 256 := regs.2.2.2.2.1.trans scratch
    have nextCap : next.getReg .x30 = BitVec.ofNat 64 capAddress := regs.2.2.2.2.2.2.trans capPointer
    have nextCapData (node : Nat) (inside : node < 128) :
        readBuffer next (capAddress+32*node) 32 = cap node := by
      rw [next_check_digest oracle state _ scratch (by omega) (by omega) (by omega)]
      exact capData node inside
    have nextIndexData (ordinal : Nat) (inside : ordinal < count) :
        next.getMem (BitVec.ofNat 64 (indexAddress+8+8*ordinal)) =
          BitVec.ofNat 64 (indices (ordinal+1)).val := by
      rw [next_check_outside oracle state _ scratch (outside_scratch _ (by omega) (by omega))]
      convert indexData (ordinal+1) (by omega) using 2
      congr 1
      omega
    have nextValueData (ordinal : Nat) (inside : ordinal < count) (block : Nat) (blockBound : block < 4) :
        readBuffer next (valueAddress+256+256*ordinal+64*block) 64 =
          (values (ordinal+1)).extractLsb' (512*block) 512 := by
      rw [read_compression_halves _ _ (by omega),
        next_check_digest oracle state (valueAddress+256+256*ordinal+64*block+32) scratch
          (by omega) (by omega) (by omega),
        next_check_digest oracle state (valueAddress+256+256*ordinal+64*block) scratch
          (by omega) (by omega) (by omega),
        ← read_compression_halves _ _ (by omega)]
      convert valueData (ordinal+1) (by omega) block blockBound using 2
      omega
    have nextSaltData (ordinal : Nat) (inside : ordinal < count) :
        saltState (readBuffer next (proofAddress+568+568*ordinal) 24) = salts (ordinal+1) := by
      rw [next_check_salt oracle state _ scratch (by omega) (by omega) (by omega)]
      convert saltData (ordinal+1) (by omega) using 3
      omega
    have nextPathData (ordinal : Nat) (inside : ordinal < count) (level : Nat) (levelBound : level < 17) :
        readBuffer next (proofAddress+568+568*ordinal+24+32*level) 32 = siblings (ordinal+1) level := by
      rw [next_check_digest oracle state _ scratch (by omega) (by omega) (by omega)]
      convert pathData (ordinal+1) (by omega) level levelBound using 2
      omega
    have rest := ih next (fun k => values (k+1)) (fun k => salts (k+1)) (fun k => indices (k+1))
      (fun k => siblings (k+1)) (valueAddress+256) (proofAddress+568) (indexAddress+8)
      nextScratch nextCap nextValues nextProof nextIndices (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) nextCapData nextIndexData
      nextValueData nextSaltData nextPathData
    rw [checkLoopAccepts, Bool.and_eq_true, first, rest]
    constructor
    · rintro ⟨head, tail⟩ ordinal inside
      cases ordinal with
      | zero => exact head
      | succ ordinal => exact tail ordinal (by omega)
    · intro all
      exact ⟨all 0 (by omega), fun ordinal inside => all (ordinal+1) (by omega)⟩

end CommitGolfCandidate
