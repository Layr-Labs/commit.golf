import CommitGolfCandidate.CommitLoop
import CommitGolfCandidate.CopyRefinement
import CommitGolfCandidate.LeafRefinement

/-! Salt loading and heap writes of the actual commitment leaf iteration. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

/-- Commitment's three digest copies use the same load/store sequence as opening.
Only the source and destination registers differ. -/
theorem commit_copy_memory_as_opening (state : MachineState) (start : Nat)
    (location : start = 40 ∨ start = 49 ∨ start = 73) :
    (commitCopyState state start).mem =
      (openingCopyState
        ((state.setReg .x23 (if start = 40 then state.getReg .x18
          else if start = 49 then state.getReg .x21 else state.getReg .x9+32)).setReg .x25
          (if start = 40 then state.getReg .x21
          else if start = 49 then state.getReg .x23 else state.getReg .x26))).mem := by
  rcases location with rfl | rfl | rfl <;>
    rw [commit_copy_expansion, opening_copy_expansion] <;>
    simp [List.foldl, execInstrBr, signExtend12, MachineState.getReg,
      MachineState.setReg, MachineState.setPC, MachineState.setMem, MachineState.getMem, BitVec.add_assoc]

/-- Copy a complete digest from one of the three commitment copy sites. -/
theorem commit_copy_digest (state : MachineState) (start source destination : Nat)
    (location : start = 40 ∨ start = 49 ∨ start = 73)
    (sourcePointer : (if start = 40 then state.getReg .x18
      else if start = 49 then state.getReg .x21 else state.getReg .x9+32) = BitVec.ofNat 64 source)
    (destinationPointer : (if start = 40 then state.getReg .x21
      else if start = 49 then state.getReg .x23 else state.getReg .x26) = BitVec.ofNat 64 destination)
    (sourceAligned : source % 8 = 0) (destinationAligned : destination % 8 = 0)
    (sourceBound : source+32 ≤ 2^64) (destinationBound : destination+32 ≤ 2^64)
    (separate : source+32 ≤ destination ∨ destination+32 ≤ source) :
    readBuffer (commitCopyState state start) destination 32 = readBuffer state source 32 := by
  rw [read_buffer_memory_congr _ _ (commit_copy_memory_as_opening state start location)]
  rw [opening_copy_digest _ source destination (by simpa [MachineState.getReg, MachineState.setReg] using sourcePointer)
    (by simpa [MachineState.getReg, MachineState.setReg] using destinationPointer) sourceAligned destinationAligned sourceBound destinationBound separate]
  rfl

/-- The commitment copy preserves every disjoint complete digest. -/
theorem commit_copy_preserves_digest (state : MachineState) (start destination address : Nat)
    (location : start = 40 ∨ start = 49 ∨ start = 73)
    (destinationPointer : (if start = 40 then state.getReg .x21
      else if start = 49 then state.getReg .x23 else state.getReg .x26) = BitVec.ofNat 64 destination)
    (aligned : address % 8 = 0)
    (destinationBound : destination+32 ≤ 2^64) (readBound : address+32 ≤ 2^64)
    (separate : address+32 ≤ destination ∨ destination+32 ≤ address) :
    readBuffer (commitCopyState state start) address 32 = readBuffer state address 32 := by
  rw [read_buffer_memory_congr _ _ (commit_copy_memory_as_opening state start location)]
  rw [opening_copy_preserves_digest _ destination address (by simpa [MachineState.getReg, MachineState.setReg] using destinationPointer)
    aligned destinationBound readBound separate]
  rfl

/-- A complete leaf iteration evaluates the leaf subroutine, then copies its
result into the heap. This equality retains the actual interpreter memory state. -/
theorem commit_position_evaluation (oracle : Oracle) (state : MachineState) :
    checkEvaluation oracle (commitPositionRun state) =
      let leaf := checkEvaluation oracle
        (commitLeafLoop (commitLeafPrepared (commitPositionState state)) 8)
      (commitPositionNextState (commitCopyState (leaf.1.setPC 4292) 49), leaf.2) := by
  rw [commitPositionRun, check_evaluation_bind]
  simp only [check_evaluation_pure, Nat.add_zero]

/-- The salt copy initializes the leaf hasher with the original salt digest. -/
theorem commit_position_salt (state : MachineState) (saltAddress : Nat)
    (scratch : state.getReg .x21 = 256)
    (saltPointer : state.getReg .x18 = BitVec.ofNat 64 saltAddress)
    (aligned : saltAddress % 8 = 0) (above : 288 ≤ saltAddress)
    (bounded : saltAddress+32 ≤ 2^64) :
    readBuffer (commitLeafPrepared (commitPositionState state)) 256 32 =
      readBuffer state saltAddress 32 := by
  change readBuffer (commitCopyState state 40) 256 32 = _
  exact commit_copy_digest state 40 saltAddress 256 (by simp) saltPointer scratch
    aligned (by decide) bounded (by decide) (Or.inr above)

/-- Setting up the salted leaf hash preserves every digest outside scratch. -/
theorem commit_position_input_digest (state : MachineState) (address : Nat)
    (scratch : state.getReg .x21 = 256) (aligned : address % 8 = 0)
    (above : 288 ≤ address) (bounded : address+32 ≤ 2^64) :
    readBuffer (commitLeafPrepared (commitPositionState state)) address 32 =
      readBuffer state address 32 := by
  change readBuffer (commitCopyState state 40) address 32 = _
  exact commit_copy_preserves_digest state 40 256 address (by simp) scratch aligned
    (by decide) bounded (Or.inr above)

/-- The final copy stores the computed digest before advancing the leaf pointers. -/
theorem commit_leaf_heap_write (leaf : MachineState) (destination : Nat)
    (scratch : leaf.getReg .x21 = 256)
    (heapPointer : leaf.getReg .x23 = BitVec.ofNat 64 destination)
    (aligned : destination % 8 = 0) (above : 288 ≤ destination)
    (bounded : destination+32 ≤ 2^64) :
    readBuffer (commitPositionNextState (commitCopyState (leaf.setPC 4292) 49)) destination 32 =
      readBuffer leaf 256 32 := by
  change readBuffer (commitCopyState (leaf.setPC 4292) 49) destination 32 = _
  exact commit_copy_digest (leaf.setPC 4292) 49 256 destination (by simp) scratch heapPointer
    (by decide) aligned (by decide) bounded (Or.inl above)

private theorem commit_heap_write_preserves (leaf : MachineState) (destination address : Nat)
    (heapPointer : leaf.getReg .x23 = BitVec.ofNat 64 destination)
    (aligned : address % 8 = 0)
    (destinationBound : destination+32 ≤ 2^64) (readBound : address+32 ≤ 2^64)
    (separate : address+32 ≤ destination ∨ destination+32 ≤ address) :
    readBuffer (commitPositionNextState (commitCopyState (leaf.setPC 4292) 49)) address 32 =
      readBuffer leaf address 32 := by
  change readBuffer (commitCopyState (leaf.setPC 4292) 49) address 32 = _
  exact commit_copy_preserves_digest (leaf.setPC 4292) 49 destination address (by simp)
    heapPointer aligned destinationBound readBound separate

private theorem commit_leaf_preserves_buffer (oracle : Oracle) (ready : MachineState)
    (count address : Nat) (scratch : ready.getReg .x21 = 256)
    (aligned : address % 8 = 0) (above : 320 ≤ address) (readBound : address+32 ≤ 2^64) :
    readBuffer (checkEvaluation oracle (commitLeafLoop ready count)).1 address 32 =
      readBuffer ready address 32 := by
  apply read_digest_congr _ _ _ aligned
  intro i hi
  apply commit_leaf_loop_outside oracle ready count _ scratch
  intro j hj equal
  have numeric := congrArg BitVec.toNat equal
  simp only [BitVec.toNat_ofNat] at numeric
  rw [Nat.mod_eq_of_lt (by omega : address+8*i < 2^64),
    Nat.mod_eq_of_lt (by omega : 256+8*j < 2^64)] at numeric
  omega

attribute [local irreducible] commitPositionState commitLeafLoop checkEvaluation

/-- One full iteration of the submitted commitment program stores the salted
leaf digest, using the original message blocks and salt in input memory. -/
theorem commit_position_digest (oracle : Oracle) (state : MachineState)
    (source saltAddress destination : Nat) (value : Entry)
    (scratch : state.getReg .x21 = 256)
    (messagePointer : state.getReg .x8 = BitVec.ofNat 64 source)
    (saltPointer : state.getReg .x18 = BitVec.ofNat 64 saltAddress)
    (heapPointer : state.getReg .x23 = BitVec.ofNat 64 destination)
    (sourceAligned : source % 8 = 0) (saltAligned : saltAddress % 8 = 0)
    (destinationAligned : destination % 8 = 0)
    (sourceAbove : 320 ≤ source) (saltAbove : 288 ≤ saltAddress) (destinationAbove : 288 ≤ destination)
    (sourceBound : source+256 < 2^64) (saltBound : saltAddress+32 ≤ 2^64)
    (destinationBound : destination+32 ≤ 2^64)
    (data : ∀ block < 8, readBuffer state (source+32*block) 32 = value.extractLsb' (256*block) 256) :
    readBuffer (checkEvaluation oracle (commitPositionRun state)).1 destination 32 =
      leafDigest oracle.compression (readBuffer state saltAddress 32) value := by
  let ready := commitLeafPrepared (commitPositionState state)
  let leaf := (checkEvaluation oracle (commitLeafLoop ready 8)).1
  have readyReg (reg : Reg) (notCounter : reg ≠ .x28) (not5 : reg ≠ .x5)
      (not10 : reg ≠ .x10) (not11 : reg ≠ .x11) (not12 : reg ≠ .x12) (not13 : reg ≠ .x13)
      (notLink : reg ≠ .x1) (notTemporary : reg ≠ .x6) : ready.getReg reg = state.getReg reg :=
    (commitLeafPrepared_register _ reg notCounter not5 not10 not11 not12 not13).trans
      (commit_position_register state reg notLink notTemporary)
  have hashed : readBuffer leaf 256 32 =
      leafDigest oracle.compression (readBuffer state saltAddress 32) value := by
    apply commit_leaf_digest oracle ready source _ value
      ((readyReg .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)).trans scratch)
      ((readyReg .x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)).trans messagePointer)
      sourceAligned sourceAbove sourceBound
    · exact commit_position_salt state saltAddress scratch saltPointer saltAligned saltAbove saltBound
    · intro block inside
      rw [commit_position_input_digest state (source+32*block) scratch (by omega) (by omega) (by omega)]
      exact data block inside
  have leafRegs := commit_leaf_loop_registers ready 8 leaf (check_evaluation_support oracle _)
  rw [commit_position_evaluation]
  change readBuffer (commitPositionNextState (commitCopyState (leaf.setPC 4292) 49)) destination 32 = _
  rw [commit_leaf_heap_write leaf destination
    ((leafRegs.2 .x21 (by decide)).trans ((readyReg .x21 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans scratch))
    ((leafRegs.2 .x23 (by decide)).trans ((readyReg .x23 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans heapPointer))
    destinationAligned destinationAbove destinationBound]
  exact hashed

/-- Leaf hashing and its final heap write preserve any digest outside scratch
and the single destination slot. This includes all other leaves, salts, and inputs. -/
theorem commit_position_preserves_digest (oracle : Oracle) (state : MachineState)
    (destination address : Nat)
    (scratch : state.getReg .x21 = 256)
    (heapPointer : state.getReg .x23 = BitVec.ofNat 64 destination)
    (aligned : address % 8 = 0) (above : 320 ≤ address)
    (destinationBound : destination+32 ≤ 2^64) (readBound : address+32 ≤ 2^64)
    (separate : address+32 ≤ destination ∨ destination+32 ≤ address) :
    readBuffer (checkEvaluation oracle (commitPositionRun state)).1 address 32 =
      readBuffer state address 32 := by
  let ready := commitLeafPrepared (commitPositionState state)
  let leaf := (checkEvaluation oracle (commitLeafLoop ready 8)).1
  have readyScratch : ready.getReg .x21 = 256 := by
    rw [commitLeafPrepared_register _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      commit_position_register state .x21 (by decide) (by decide), scratch]
  have readyPointer : ready.getReg .x23 = BitVec.ofNat 64 destination := by
    rw [commitLeafPrepared_register _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      commit_position_register state .x23 (by decide) (by decide), heapPointer]
  have leafPointer : leaf.getReg .x23 = BitVec.ofNat 64 destination :=
    ((commit_leaf_loop_registers ready 8 leaf (check_evaluation_support oracle _)).2 .x23
      (by decide)).trans readyPointer
  rw [commit_position_evaluation]
  change readBuffer (commitPositionNextState (commitCopyState (leaf.setPC 4292) 49)) address 32 = _
  rw [commit_heap_write_preserves leaf destination address leafPointer aligned destinationBound readBound separate]
  rw [commit_leaf_preserves_buffer oracle ready 8 address readyScratch aligned above readBound]
  exact commit_position_input_digest state address scratch aligned (by omega) readBound

end CommitGolfCandidate
