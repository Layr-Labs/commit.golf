import CommitGolfCandidate.Layout2Records

/-! Layout 2 V2: the state at the cap stage (word 6960) after the record blocks (`L2Done`), reached by the fused loop
(`Layout2FusedLoop`). -/
namespace TwoPermutationPrototype.GroupedOpening.Layout2
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate
open CommitGolfCandidate.Layout2Phase (stride phaseBase writerByte writerCarry recordSource streamRun)
open CommitGolfCandidate.Layout2Phase2 (bodyLen)
open Opening (sortedIndex groupsBefore)
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000

theorem runs_cost {a b : MachineState} {c c' : Nat} (run : RunsOpeningBlock a b c) (e : c=c') :
    RunsOpeningBlock a b c' := e ▸ run

theorem runs_zero (a : MachineState) : RunsOpeningBlock a a 0 := by
  intro fuel coins
  simp [Execution.charge]

theorem loop_mono (j n : Nat) : loopCost j ≤ loopCost (j+n) := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih => rw [← Nat.add_assoc, loopCost]; omega

/-- The state at the cap stage (word 6960) after the record loop. -/
structure L2Done (s : Submission) (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions)
    (pass state : MachineState) : Prop where
  pc : state.pc=address 6960
  heap : state.getReg .x9=BitVec.ofNat 64 trapdoorBase
  index : state.getReg .x8=BitVec.ofNat 64 (indicesBase+8*positions.card)
  nonce : state.getReg .x22=BitVec.ofNat 64 nonceBase
  dest : state.getReg .x21=BitVec.ofNat 64 (proofBase+534*positions.card)
  leaves : state.getReg .x19=BitVec.ofNat 64 4194304
  slots : state.getReg .x24=BitVec.ofNat 64 groupSlots
  endIndex : state.getReg .x17=BitVec.ofNat 64 (indicesBase+8*positions.card)
  marks : state.getReg .x26=BitVec.ofNat 64 Opening.markBase
  one : state.getReg .x23=1#64
  capHeap : state.getReg .x25=BitVec.ofNat 64 trapdoorBase
  capLeaves : state.getReg .x27=256#64
  proofBegin : state.getReg .x20=BitVec.ofNat 64 proofBase
  input : SameOpeningInput (s.initialState .opening (trapdoor, positions)) state
  marked : ByteMarks positions state positions.card
  bytes : L2Bytes (s.initialState .opening (trapdoor, positions)) pass positions state positions.card
  /-- The pending stream bytes of the last phase (none after a phase-3 record). -/
  flush : ∀ b<flushLen ((positions.card+3)%4), state.getByte (BitVec.ofNat 64 (destOf positions.card+b))=
    (carryAt (s.initialState .opening (trapdoor, positions)) positions positions.card).extractLsb' (8*b) 8

theorem ofNat_ne (a b : Nat) (h : a<b) (hb : b<2^64) : BitVec.ofNat 64 a ≠ BitVec.ofNat 64 b := by
  intro e
  have := congrArg BitVec.toNat e
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hb] at this
  omega

end TwoPermutationPrototype.GroupedOpening.Layout2
