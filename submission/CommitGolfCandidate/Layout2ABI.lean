import CommitGolfCandidate.Layout2Run
import CommitGolfCandidate.Layout2CapStage
import CommitGolfCandidate.QuartetOpeningSchedule
import CommitGolfCandidate.GroupOpenSetup

/-! Layout 2 V2b opener after the pass: the record loop (`records_run`, to word 6960), then the cap stage
(`Layout2CapStage.CapStage capRaw`, a hypothesis until the cap stage's theorem is supplied). The result
(`L2OpenPhysical`) holds the V2a record blocks (relative to the state `pass` the pass left), the flush bytes and the
raw cap bytes `capRaw (frontierDigests td p)` at `proofBase + 534 k`. -/
namespace TwoPermutationPrototype.GroupedOpening.Layout2
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate Sampling
open CommitGolfCandidate.Layout2Phase (stride writerByte)
open CommitGolfCandidate.Layout2Phase2 (PhaseFacts)
open CommitGolfCandidate.Layout2CapStage (CapEntry CapStage frontierDigests)
open QuartetOpening (proofLength)
open Opening (groupsBefore openingNodes)
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000

/-- Today's `OpeningABI`, restated here (the old record writer modules are not imported). -/
structure L2ABI (s : Submission) extends OpeningLayout s where
  image : s.image .opening = openingImage
  capacity : capacity ≤ s.sizes.proof
  fuel : 17179934720 ≤ s.steps .opening

/-- The opener's result after the pass: success, length, no oracle call, the Layout 2 record blocks and flush bytes,
and the raw cap bytes. -/
structure L2OpenPhysical (s : Submission) (capRaw : List (BitVec 256) → List Byte)
    (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions) (pass : MachineState) (result : Execution) :
    Prop where
  success : result.exit = .success
  length : (result.state.getReg .x11).toNat = proofLength positions
  noCalls : result.oracleCalls = 0
  lower : L2Bytes (s.initialState .opening (trapdoor, positions)) pass positions result.state positions.card
  flush : ∀ b<flushLen ((positions.card+3)%4), result.state.getByte (BitVec.ofNat 64 (destOf positions.card+b))=
    (carryAt (s.initialState .opening (trapdoor, positions)) positions positions.card).extractLsb' (8*b) 8
  footer : bytesAt result.state (proofBase+534*positions.card) (capOffset (openingNodes positions).length) =
    capRaw (frontierDigests trapdoor positions)

/-- The record loop leaves the cap stage's entry state. -/
theorem done_entry (s : Submission) (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions)
    (pass state : MachineState) (positive : 0<positions.card) (done : L2Done s trapdoor positions pass state) :
    CapEntry (s.initialState .opening (trapdoor, positions)) state positions :=
  { nonempty := positive, pc := done.pc, marks := done.marks, heap := done.capHeap, leaves := done.capLeaves,
    one := done.one, begin := done.proofBegin, dest := done.dest,
    marked := fun i hi => done.marked i hi, input := done.input }

theorem proof_length_split (positions : Positions) :
    proofLength positions=534*positions.card+capOffset (openingNodes positions).length := by
  unfold proofLength capOffset; omega

/-- The record loop, then the cap stage: `l2RecordsCost k + cycles` cycles, `l2RecordsCost k + steps` steps. -/
theorem l2_body (phases : ∀ p<4, PhaseFacts openingImage p) (capRaw : List (BitVec 256) → List Byte)
    (cap : CapStage capRaw) (s : Submission) (abi : L2ABI s)
    (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions) (begin : MachineState)
    (positive : 0<positions.card) (ready : L2Start s trapdoor positions begin) :
    ∃ final steps cycles, steps ≤ 2^30 ∧ (positions.card=128 → cycles ≤ 3407) ∧
      (∀ surplus, execute openingImage (l2RecordsCost positions.card+steps+surplus) begin true =
        pure ⟨.success,final,l2RecordsCost positions.card+cycles,0⟩) ∧
      L2OpenPhysical s capRaw trapdoor positions begin ⟨.success,final,l2RecordsCost positions.card+cycles,0⟩ := by
  obtain ⟨lower, ranRecords, done⟩ := records_run phases s abi.toOpeningLayout trapdoor positions begin positive ready
  obtain ⟨final, steps, cycles, stepBound, cycleBound, ranCap, len, kept, footer⟩ :=
    cap.run s abi.toOpeningLayout trapdoor positions lower abi.image (done_entry s trapdoor positions begin lower positive done)
  have flushEnd := dest_flush positions.card positive
  refine ⟨final, steps, cycles, stepBound, cycleBound, ?_, ⟨rfl, ?_, rfl, ?_, ?_, footer⟩⟩
  · intro surplus
    rw [Nat.add_assoc, ranRecords (steps+surplus) true, ranCap surplus]
    simp [Execution.charge]
  · change (final.getReg .x11).toNat=_
    rw [len, proof_length_split]
  · intro j hj b hb
    have mono := dest_mono j positions.card hj
    have lo := (dest_bound j).1
    change final.getByte _=_
    rw [kept _ (by omega) (by omega)]
    exact done.bytes j hj b hb
  · intro b hb
    have lo := (dest_bound positions.card).1
    change final.getByte _=_
    rw [kept _ (by omega) (by omega)]
    exact done.flush b hb

end TwoPermutationPrototype.GroupedOpening.Layout2
