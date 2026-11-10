import CommitGolfCandidate.CommitRefinement

/-! Every salted leaf digest stored by the actual commitment leaf loop. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

attribute [local irreducible] commitPositionRun commitLeaves checkEvaluation

/-- Fixed-oracle evaluation of one leaf followed by the remaining leaf loop. -/
theorem commit_leaves_evaluation (oracle : Oracle) (state : MachineState) (count : Nat) :
    checkEvaluation oracle (commitLeaves state (count+1)) =
      let first := checkEvaluation oracle (commitPositionRun state)
      let rest := checkEvaluation oracle (commitLeaves first.1 count)
      (rest.1, first.2+rest.2) := by
  rw [commitLeaves, check_evaluation_bind]

set_option maxRecDepth 4096 in
/-- The leaf loop preserves every digest outside consumed inputs and heap outputs. -/
theorem commit_leaves_preserves_digest (oracle : Oracle) (state : MachineState)
    (source destination count address : Nat)
    (scratch : state.getReg .x10 = state.getReg .x12 - 32)
    (messagePointer : state.getReg .x12 = BitVec.ofNat 64 source)
    (heapPointer : state.getReg .x23 = BitVec.ofNat 64 destination)
    (sourceAbove : 32 ≤ source) (sourceBound : source+256*count < 2^64)
    (aligned : address % 8 = 0)
    (destinationBound : destination+32*count ≤ 2^64) (readBound : address+32 ≤ 2^64)
    (sourceSeparate : address+32 ≤ source-32 ∨ source+256*count ≤ address)
    (separate : address+32 ≤ destination ∨ destination+32*count ≤ address) :
    readBuffer (checkEvaluation oracle (commitLeaves state count)).1 address 32 =
      readBuffer state address 32 := by
  induction count generalizing state source destination with
  | zero => rw [commitLeaves, check_evaluation_pure]
  | succ count ih =>
    rw [commit_leaves_evaluation]
    let next := (checkEvaluation oracle (commitPositionRun state)).1
    have reached := check_evaluation_support oracle (commitPositionRun state)
    have regs := commit_position_registers state next reached
    have nextScratch := commit_position_chain state next reached
    have nextSource : next.getReg .x12 = BitVec.ofNat 64 (source+256) := by
      rw [regs.1, messagePointer, BitVec.ofNat_add]; rfl
    have nextPointer : next.getReg .x23 = BitVec.ofNat 64 (destination+32) := by
      rw [regs.2.2.1, heapPointer, BitVec.ofNat_add]; rfl
    change readBuffer (checkEvaluation oracle (commitLeaves next count)).1 address 32 = _
    rw [ih next (source+256) (destination+32) nextScratch nextSource nextPointer (by omega)
      (by omega) (by omega) (by rcases sourceSeparate with h | h <;> omega)
      (by rcases separate with h | h <;> omega)]
    exact commit_position_preserves_digest oracle state source destination address scratch
      messagePointer heapPointer sourceAbove (by omega) aligned (by omega) readBound
      (by rcases sourceSeparate with h | h <;> omega) (by rcases separate with h | h <;> omega)

set_option maxRecDepth 4096 in
/-- All heap leaf slots contain the salted hash of the corresponding original input.
The source vector, leaf-output range, and salt range occur in that order in memory. -/
theorem commit_leaves_digests (oracle : Oracle) (state : MachineState)
    (source destination saltAddress count : Nat) (message : Nat → Entry) (salts : Nat → Digest)
    (scratch : state.getReg .x10 = state.getReg .x12 - 32)
    (messagePointer : state.getReg .x12 = BitVec.ofNat 64 source)
    (heapPointer : state.getReg .x23 = BitVec.ofNat 64 destination)
    (saltPointer : state.getReg .x18 = BitVec.ofNat 64 saltAddress)
    (sourceAligned : source % 8 = 0) (destinationAligned : destination % 8 = 0)
    (saltAligned : saltAddress % 8 = 0) (above : 32 ≤ source)
    (sourceBefore : source+256*count ≤ destination)
    (saltsAfter : destination+32*count ≤ saltAddress)
    (bounded : saltAddress+32*count < 2^64)
    (data : ∀ index < count, ∀ block < 8,
      readBuffer state (source+256*index+32*block) 32 = (message index).extractLsb' (256*block) 256)
    (saltData : ∀ index < count, readBuffer state (saltAddress+32*index) 32 = salts index) :
    ∀ index < count,
      readBuffer (checkEvaluation oracle (commitLeaves state count)).1 (destination+32*index) 32 =
        leafDigest oracle.compression (salts index) (message index) := by
  induction count generalizing state source destination saltAddress message salts with
  | zero => intro index inside; omega
  | succ count ih =>
    let next := (checkEvaluation oracle (commitPositionRun state)).1
    have regs := commit_position_registers state next (check_evaluation_support oracle _)
    have nextScratch := commit_position_chain state next (check_evaluation_support oracle _)
    have nextSource : next.getReg .x12 = BitVec.ofNat 64 (source+256) := by
      rw [regs.1, messagePointer, BitVec.ofNat_add]
      rfl
    have nextDestination : next.getReg .x23 = BitVec.ofNat 64 (destination+32) := by
      rw [regs.2.2.1, heapPointer, BitVec.ofNat_add]
      rfl
    have nextSalt : next.getReg .x18 = BitVec.ofNat 64 (saltAddress+32) := by
      rw [regs.2.1, saltPointer, BitVec.ofNat_add]
      rfl
    have nextData (index : Nat) (inside : index < count) (block : Nat) (blockInside : block < 8) :
        readBuffer next (source+256+256*index+32*block) 32 =
          (message (index+1)).extractLsb' (256*block) 256 := by
      rw [commit_position_preserves_digest oracle state source destination _ scratch messagePointer heapPointer
        above (by omega) (by omega) (by omega) (by omega) (Or.inr (by omega)) (Or.inl (by omega))]
      convert data (index+1) (by omega) block blockInside using 1
      · congr 1
        omega
    have nextSaltData (index : Nat) (inside : index < count) :
        readBuffer next (saltAddress+32+32*index) 32 = salts (index+1) := by
      rw [commit_position_preserves_digest oracle state source destination _ scratch messagePointer heapPointer
        above (by omega) (by omega) (by omega) (by omega) (Or.inr (by omega)) (Or.inr (by omega))]
      convert saltData (index+1) (by omega) using 1
      · congr 1
        omega
    intro index inside
    rw [commit_leaves_evaluation]
    change readBuffer (checkEvaluation oracle (commitLeaves next count)).1 (destination+32*index) 32 = _
    cases index with
    | zero =>
      simp only [Nat.mul_zero, Nat.add_zero]
      rw [commit_leaves_preserves_digest oracle next (source+256) (destination+32) count destination
        nextScratch nextSource nextDestination (by omega) (by omega) destinationAligned
        (by omega) (by omega) (Or.inr (by omega)) (Or.inl (by omega))]
      rw [commit_position_digest oracle state source saltAddress destination (message 0)
        scratch messagePointer saltPointer heapPointer sourceAligned saltAligned destinationAligned
        above (by omega) (by omega) (by omega) (by omega) (by omega)
        (by simpa using data 0 (by omega))]
      rw [← saltData 0 (by omega)]
      simp only [Nat.mul_zero, Nat.add_zero]
    | succ index =>
      have record := ih next (source+256) (destination+32) (saltAddress+32)
        (fun i => message (i+1)) (fun i => salts (i+1)) nextScratch nextSource nextDestination nextSalt
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        nextData nextSaltData index (by omega)
      convert record using 1
      · congr 1
        omega

end CommitGolfCandidate
