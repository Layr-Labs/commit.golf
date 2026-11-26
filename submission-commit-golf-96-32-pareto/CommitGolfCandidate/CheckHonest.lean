import CommitGolfCandidate.CheckAcceptance

/-! The whole checker loop accepts correctly encoded heap authentication records,
for both normal openings (`pathDepth = 24`) and cap-table openings (`pathDepth = 17`). -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

attribute [local irreducible] checkPositionHash checkEvaluation
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

def nextCheckState (oracle : Oracle) (pathDepth : Nat) (state : MachineState) : MachineState :=
  checkPositionNextState
    (checkRootWordsState (checkEvaluation oracle (checkPositionHash state pathDepth)).1 66 4)

private theorem latch_register (state : MachineState) (reg : Reg)
    (not24 : reg ≠ .x24) (not27 : reg ≠ .x27) :
    (checkPositionNextState state).getReg reg = state.getReg reg := by
  simp only [checkPositionNextState, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not27),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not24)]

private theorem latch_index (state : MachineState) :
    (checkPositionNextState state).getReg .x24 = state.getReg .x24 + 8 := by
  simp only [checkPositionNextState, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x27 ≠ .x24),
    MachineState.getReg_setReg_eq (by decide : Reg.x24 ≠ .x0)]

theorem next_check_registers (oracle : Oracle) (pathDepth : Nat) (state : MachineState)
    (depthPos : 0 < pathDepth) (depthBound : pathDepth ≤ 24)
    (depthReg : state.getReg .x30 = BitVec.ofNat 64 pathDepth) :
    (nextCheckState oracle pathDepth state).getReg .x8 = state.getReg .x8 + 256 ∧
    (nextCheckState oracle pathDepth state).getReg .x25 =
      state.getReg .x25 + BitVec.ofNat 64 (16 + 32 * pathDepth) ∧
    (nextCheckState oracle pathDepth state).getReg .x24 = state.getReg .x24 + 8 ∧
    (nextCheckState oracle pathDepth state).getReg .x21 = state.getReg .x21 ∧
    (nextCheckState oracle pathDepth state).getReg .x26 = state.getReg .x26 ∧
    (nextCheckState oracle pathDepth state).getReg .x30 = state.getReg .x30 := by
  let hashed := (checkEvaluation oracle (checkPositionHash state pathDepth)).1
  let compared := checkRootWordsState hashed 66 4
  have regs := check_position_hash_registers pathDepth depthPos depthBound state hashed depthReg
    (check_evaluation_support oracle _)
  have keep (reg : Reg) (not6 : reg ≠ .x6) (not7 : reg ≠ .x7) :
      compared.getReg reg = hashed.getReg reg :=
    (check_root_words_preserves hashed 66 4 reg not6 not7).1
  have other (reg : Reg) (not24 : reg ≠ .x24) (not27 : reg ≠ .x27)
      (not6 : reg ≠ .x6) (not7 : reg ≠ .x7) :
      (nextCheckState oracle pathDepth state).getReg reg = hashed.getReg reg :=
    (latch_register compared reg not24 not27).trans (keep reg not6 not7)
  exact ⟨(other .x8 (by decide) (by decide) (by decide) (by decide)).trans regs.2.1,
    (other .x25 (by decide) (by decide) (by decide) (by decide)).trans regs.2.2.1,
    (latch_index compared).trans (congrArg (· + 8)
      ((keep .x24 (by decide) (by decide)).trans (regs.2.2.2.2 .x24 (by simp)))),
    (other .x21 (by decide) (by decide) (by decide) (by decide)).trans (regs.2.2.2.2 .x21 (by simp)),
    (other .x26 (by decide) (by decide) (by decide) (by decide)).trans (regs.2.2.2.2 .x26 (by simp)),
    (other .x30 (by decide) (by decide) (by decide) (by decide)).trans (regs.2.2.2.2 .x30 (by simp))⟩

private theorem latch_memory (state : MachineState) :
    (checkPositionNextState state).mem = state.mem := rfl

private theorem compare_next_memory (hashed : MachineState) :
    (checkPositionNextState (checkRootWordsState hashed 66 4)).mem = hashed.mem :=
  (latch_memory _).trans (check_root_words_preserves hashed 66 4 .x21 (by decide) (by decide)).2

theorem next_check_memory (oracle : Oracle) (pathDepth : Nat) (state : MachineState) (address : Nat)
    (scratch : state.getReg .x21 = 256) (above : 352 ≤ address) (bounded : address < 2 ^ 64) :
    (nextCheckState oracle pathDepth state).getMem (BitVec.ofNat 64 address) =
      state.getMem (BitVec.ofNat 64 address) := by
  let hashed := (checkEvaluation oracle (checkPositionHash state pathDepth)).1
  have same : (nextCheckState oracle pathDepth state).getMem = hashed.getMem :=
    congrArg (fun mem address => mem address) (compare_next_memory hashed)
  rw [same]
  apply check_position_hash_outside oracle state pathDepth _ scratch
  intro i hi equal
  have natural := congrArg BitVec.toNat equal
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bounded,
    Nat.mod_eq_of_lt (by omega : 256 + 8 * i < 2 ^ 64)] at natural
  omega

theorem next_check_digest (oracle : Oracle) (pathDepth : Nat) (state : MachineState) (address : Nat)
    (scratch : state.getReg .x21 = 256) (aligned : address % 8 = 0)
    (above : 352 ≤ address) (bounded : address + 32 < 2 ^ 64) :
    readBuffer (nextCheckState oracle pathDepth state) address 32 = readBuffer state address 32 := by
  apply read_digest_congr _ _ _ aligned
  intro word inside
  exact next_check_memory oracle pathDepth state (address + 8 * word) scratch (by omega) (by omega)

theorem next_check_salt (oracle : Oracle) (pathDepth : Nat) (state : MachineState) (address : Nat)
    (scratch : state.getReg .x21 = 256) (aligned : address % 8 = 0)
    (above : 352 ≤ address) (bounded : address + 16 < 2 ^ 64) :
    readBuffer (nextCheckState oracle pathDepth state) address 16 = readBuffer state address 16 := by
  apply read_salt_congr _ _ _ aligned
  intro word inside
  exact next_check_memory oracle pathDepth state (address + 8 * word) scratch (by omega) (by omega)

attribute [local irreducible] nextCheckState

/-- All requested positions pass when the input records authenticate their values
against one consistent heap at depth `pathDepth` (`24` against `heap 1`, or `17`
against `heap (128 + slot)`). -/
theorem check_loop_honest (oracle : Oracle) (state : MachineState) (message : Message)
    (heap : Nat → Digest) (salts : Index → Salt) (indices : Nat → Index)
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
    (proofBound : proofAddress + (16 + 32 * pathDepth) * count < 2 ^ 64)
    (indexBound : indexAddress + 8 * count < 2 ^ 64)
    (targetData : ∀ slot < 2 ^ (24 - pathDepth),
      readBuffer state (targetAddress + 32 * slot) 32 = heap (2 ^ (24 - pathDepth) + slot))
    (indexData : ∀ ordinal < count, state.getMem (BitVec.ofNat 64 (indexAddress + 8 * ordinal)) =
      BitVec.ofNat 64 (indices ordinal).val)
    (valueData : ∀ ordinal < count, ∀ block < 4,
      readBuffer state (valueAddress + 256 * ordinal + 64 * block) 64 =
        (message (indices ordinal)).extractLsb' (512 * block) 512)
    (saltData : ∀ ordinal < count,
      readBuffer state (proofAddress + (16 + 32 * pathDepth) * ordinal) 16 = salts (indices ordinal))
    (pathData : ∀ ordinal < count, ∀ level < pathDepth,
      readBuffer state (proofAddress + (16 + 32 * pathDepth) * ordinal + 16 + 32 * level) 32 =
        heap (((LENGTH + (indices ordinal).val) / 2 ^ level) ^^^ 1))
    (leaves : ∀ index : Index,
      heap (LENGTH + index.val) = leafDigest oracle.compression index (salts index) (message index))
    (parents : ∀ parent, 0 < parent → parent < LENGTH →
      heap parent = combine oracle.compression (heap (2 * parent)) (heap (2 * parent + 1))) :
    checkLoopAccepts oracle count pathDepth state = true := by
  induction count generalizing state indices valueAddress proofAddress indexAddress with
  | zero => rfl
  | succ count ih =>
    have hrec : (16 + 32 * pathDepth) * (count + 1) =
        (16 + 32 * pathDepth) * count + (16 + 32 * pathDepth) := Nat.mul_succ _ _
    have idx0 : state.getMem (state.getReg .x24) = BitVec.ofNat 64 (indices 0).val := by
      rw [indexPointer]; simpa only [Nat.mul_zero, Nat.add_zero] using indexData 0 (by omega)
    have reconstructed := check_position_heap_ancestor oracle state pathDepth valueAddress proofAddress
      (message (indices 0)) (salts (indices 0)) heap (indices 0) depthBound scratch
      valuePointer proofPointer valueAligned proofAligned valueAbove proofAbove
      (by omega) (by omega)
      (by simpa only [Nat.mul_zero, Nat.add_zero] using saltData 0 (by omega))
      (by simpa only [Nat.mul_zero, Nat.add_zero] using valueData 0 (by omega))
      idx0
      (by simpa only [Nat.mul_zero, Nat.add_zero, LENGTH, LOG_LENGTH] using pathData 0 (by omega))
      (leaves (indices 0)) parents
    have hpow : 2 ^ 24 = 2 ^ pathDepth * 2 ^ (24 - pathDepth) := by
      rw [← Nat.pow_add, Nat.add_sub_of_le depthBound]
    have qBound : (indices 0).val / 2 ^ pathDepth < 2 ^ (24 - pathDepth) := by
      have hlt : (indices 0).val < 2 ^ 24 := (indices 0).isLt
      exact (Nat.div_lt_iff_lt_mul (by positivity)).mpr (by rw [Nat.mul_comm, ← hpow]; exact hlt)
    have ancEq : (2 ^ 24 + (indices 0).val) / 2 ^ pathDepth =
        2 ^ (24 - pathDepth) + (indices 0).val / 2 ^ pathDepth := by
      rw [hpow, Nat.mul_add_div (by positivity)]
    have accepted : rootWordsMatch (checkEvaluation oracle (checkPositionHash state pathDepth)).1 = true := by
      apply (root_words_match_iff _).mpr
      apply (check_position_comparison oracle state pathDepth targetAddress (indices 0)
        depthPos depthBound depthReg scratch targetPointer idx0
        targetAligned targetAbove targetBound).mpr
      rw [reconstructed, ancEq, targetData _ qBound]
    let next := nextCheckState oracle pathDepth state
    have regs := next_check_registers oracle pathDepth state depthPos depthBound depthReg
    have nextValues : next.getReg .x8 = BitVec.ofNat 64 (valueAddress + 256) := by
      rw [regs.1, valuePointer, BitVec.ofNat_add]; rfl
    have nextProof : next.getReg .x25 = BitVec.ofNat 64 (proofAddress + (16 + 32 * pathDepth)) := by
      rw [regs.2.1, proofPointer, ← BitVec.ofNat_add]
    have nextIndices : next.getReg .x24 = BitVec.ofNat 64 (indexAddress + 8) := by
      rw [regs.2.2.1, indexPointer, BitVec.ofNat_add]; rfl
    have nextTargetData (slot : Nat) (hs : slot < 2 ^ (24 - pathDepth)) :
        readBuffer next (targetAddress + 32 * slot) 32 = heap (2 ^ (24 - pathDepth) + slot) := by
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
          (message (indices (ordinal + 1))).extractLsb' (512 * block) 512 := by
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
        readBuffer next (proofAddress + (16 + 32 * pathDepth) + (16 + 32 * pathDepth) * ordinal) 16 =
          salts (indices (ordinal + 1)) := by
      have hord : (16 + 32 * pathDepth) * (ordinal + 1) ≤ (16 + 32 * pathDepth) * count :=
        Nat.mul_le_mul_left _ (by omega)
      have hmul : (16 + 32 * pathDepth) * (ordinal + 1) =
          (16 + 32 * pathDepth) * ordinal + (16 + 32 * pathDepth) := Nat.mul_succ _ _
      have hmod8 : ((16 + 32 * pathDepth) * ordinal) % 8 = 0 := by
        rw [show 16 + 32 * pathDepth = 8 * (2 + 4 * pathDepth) by omega, Nat.mul_assoc]
        exact Nat.mul_mod_right 8 _
      rw [next_check_salt oracle pathDepth state _ scratch (by omega) (by omega) (by omega)]
      convert saltData (ordinal + 1) (by omega) using 1
      congr 1
      omega
    have nextPathData (ordinal : Nat) (inside : ordinal < count) (level : Nat) (levelBound : level < pathDepth) :
        readBuffer next
          (proofAddress + (16 + 32 * pathDepth) + (16 + 32 * pathDepth) * ordinal + 16 + 32 * level) 32 =
          heap (((LENGTH + (indices (ordinal + 1)).val) / 2 ^ level) ^^^ 1) := by
      have hord : (16 + 32 * pathDepth) * (ordinal + 1) ≤ (16 + 32 * pathDepth) * count :=
        Nat.mul_le_mul_left _ (by omega)
      have hmul : (16 + 32 * pathDepth) * (ordinal + 1) =
          (16 + 32 * pathDepth) * ordinal + (16 + 32 * pathDepth) := Nat.mul_succ _ _
      have hmod8 : ((16 + 32 * pathDepth) * ordinal) % 8 = 0 := by
        rw [show 16 + 32 * pathDepth = 8 * (2 + 4 * pathDepth) by omega, Nat.mul_assoc]
        exact Nat.mul_mod_right 8 _
      rw [next_check_digest oracle pathDepth state _ scratch (by omega) (by omega) (by omega)]
      convert pathData (ordinal + 1) (by omega) level levelBound using 1
      congr 1
      omega
    rw [checkLoopAccepts, accepted, Bool.true_and]
    suffices rest : checkLoopAccepts oracle count pathDepth next = true by
      simpa only [next, nextCheckState] using rest
    exact ih next (fun k => indices (k + 1))
      (valueAddress + 256) (proofAddress + (16 + 32 * pathDepth)) (indexAddress + 8)
      (regs.2.2.2.2.2.trans depthReg) (regs.2.2.2.1.trans scratch) (regs.2.2.2.2.1.trans targetPointer)
      nextValues nextProof nextIndices (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)
      nextTargetData nextIndexData nextValueData nextSaltData nextPathData

end CommitGolfCandidate
