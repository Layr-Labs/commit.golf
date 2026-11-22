import CommitGolfCandidate.K3OpenCapBytes
import CommitGolfCandidate.GroupOpenMemory
import CommitGolfCandidate.TwoPermutationOpeningRecordGroups
import CommitGolfCandidate.TwoPermutationOpeningABI
import CommitGolfCandidate.Layout2CapCodec
import CommitGolfCandidate.GroupOpenImage

/-! Layout 2 V2b: the boundary between the record loop (Opus) and the cap stage (Astra) at opening word 6960.

`CapEntry` is what the record loop establishes at 6960 for `k = p.card > 0` records (Opus, `Layout2ABI`).
`CapStage capRaw` is what the cap stage provides, for a pure byte function `capRaw` of the raw frontier digests:

- `run`: from any `CapEntry`, a deterministic run to the successful HALT, with no oracle call, an explicit steps bound
  (fuel), at most 3,407 cycles for 128 positions, the proof length `534 k + capOffset f`, the record bytes
  `[proofBase, proofBase+534k)` kept, and the cap bytes `capRaw (frontierDigests td p)` after them;
- `length`: `capRaw ds` has `capOffset ds.length` bytes;
- `honest`: on digests whose bits `238..255` are zero, the bytes of `capRaw ds` are, block by block,
  `gather enc` of `foldNodes ds` (the `caps` premise of `Cap.encoder_of_blocks`).

Definitions only; neither side imports the other's proof modules. -/
namespace CommitGolfCandidate.Layout2CapStage
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype TwoPermutationPrototype.GroupedOpening

/-- The state at opening word 6960 after the record loop, for `k = p.card > 0` records, with the input loaded as
`initial`. -/
structure CapEntry (initial s : MachineState) (p : Positions) : Prop where
  nonempty : 0<p.card
  pc : s.pc=BitVec.ofNat 64 (4096+4*6960)
  marks : s.getReg .x26=BitVec.ofNat 64 4096
  heap : s.getReg .x25=BitVec.ofNat 64 trapdoorBase
  leaves : s.getReg .x27=256#64
  one : s.getReg .x23=1#64
  begin : s.getReg .x20=BitVec.ofNat 64 proofBase
  dest : s.getReg .x21=BitVec.ofNat 64 (proofBase+534*p.card)
  /-- The byte marks (`CapB.ByteMarks (groupsBefore p k) s`). -/
  marked : ∀ i<256, s.getByte (BitVec.ofNat 64 (4096+256+i))=
    BitVec.ofNat 8 (Sampling.capIsMarked (Opening.groupsBefore p p.card) (256+i) 0).toNat
  /-- The dwords of `[trapdoorBase, proofBase)` are the loaded input's. -/
  input : SameOpeningInput initial s

/-- The raw frontier digests of a trapdoor, in the canonical frontier order (arbitrary high bits). -/
def frontierDigests {s : Submission} (td : BitVec (8*s.sizes.trapdoor)) (p : Positions) : List (BitVec 256) :=
  (Opening.openingNodes p).map (fun n => td.extractLsb' (256*n) 256)

/-- The cap stage's honest relation: on digests whose bits `238..255` are zero, the bytes of `capRaw ds` are, block by
block, `gather enc` of V1's `foldNodes ds` (the `caps` premise of `Cap.encoder_of_blocks`). -/
def HonestCap (capRaw : List (BitVec 256) → List Byte) : Prop :=
  ∀ ds : List (BitVec 256), ds.length ≤ 128 → (∀ d∈ds, d.extractLsb' 238 18=0) →
    ∀ g j, j<952 → 952*g+j<capOffset ds.length →
      (capRaw ds)[952*g+j]?.getD 0=
        CommitGolfCandidate.Layout2.gather CommitGolfCandidate.Layout2.Cap.enc
          (if g<capOffset ds.length/952 then 32 else CommitGolfCandidate.Layout2.Cap.tag (capOffset ds.length%952))
          (fun z => (foldNodes ds)[952*g+z]?.getD 0) j

/-- What the V2b cap stage (words 6960.. and the walk, handlers and return) guarantees. -/
structure CapStage (capRaw : List (BitVec 256) → List Byte) : Prop where
  run : ∀ (s : Submission) (layout : OpeningLayout s) (td : BitVec (8*s.sizes.trapdoor)) (p : Positions)
      (st : MachineState), s.image .opening=openingImage →
      CapEntry (s.initialState .opening (td,p)) st p →
    ∃ final steps cycles, steps ≤ 2^30 ∧ (p.card=128 → cycles ≤ 3407) ∧
      (∀ surplus, execute openingImage (steps+surplus) st true=pure ⟨.success,final,cycles,0⟩) ∧
      (final.getReg .x11).toNat=534*p.card+capOffset (Opening.openingNodes p).length ∧
      (∀ a, proofBase ≤ a → a<proofBase+534*p.card →
        final.getByte (BitVec.ofNat 64 a)=st.getByte (BitVec.ofNat 64 a)) ∧
      bytesAt final (proofBase+534*p.card) (capOffset (Opening.openingNodes p).length)=
        capRaw (frontierDigests td p)
  length : ∀ ds, (capRaw ds).length=capOffset ds.length
  honest : HonestCap capRaw

end CommitGolfCandidate.Layout2CapStage
