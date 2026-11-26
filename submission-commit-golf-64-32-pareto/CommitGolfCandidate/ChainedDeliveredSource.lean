import CommitGolfCandidate.ChainedCachedPrefix
import CommitGolfCandidate.ChainedPrefixGeometry

/-! Connect actual cached-prefix execution and delivered commitment serialization to the native postpass. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp SplitCodec
open TwoPermutationPrototype.Sampling TwoPermutationPrototype.Opening
open CommitGolfCandidate.Permutation.NonceChain (Key)
set_option maxRecDepth 8192

theorem delivered_cached_boundary (target : Image)
    (codePrefix : target.code.take 1435=TwoPermutationPrototype.PackedOpening.openingImage.code.take 1435)
    (layout : OpeningLayout Artifact.submission) (dataAbove : 8192≤dataBase (Artifact.submission.image .opening))
    (oracle : Oracle) (message : Message) (key : Key) (positions : Positions) :
    let trapdoor := (Artifact.submission.readCommit (deliveredSeedOutput oracle message key)).2
    let heap := referenceHeap oracle (pinnedLeafNodes oracle (deliveredReady oracle message key))
    ∃ before, (∀ coins, execute target (TwoPermutationPrototype.PackedOpening.scheduledCycles positions)
      (Artifact.submission.initialState .opening (trapdoor,positions)) coins=
        pure ⟨.unfinished,before,TwoPermutationPrototype.PackedOpening.scheduledCycles positions,0⟩) ∧
      CachedPrefixBoundary Artifact.submission trapdoor positions before ∧
      BytesAt before (BitVec.ofNat 64 proofBase)
        (rawRecordStream (cachedRecords heap (deliveredSalts oracle key) positions)++
          rawFieldsBytes (footerRawFields (openingNodes positions) (cachedFooter (openingNodes positions) heap))) := by
  obtain ⟨before,ran,boundary⟩ := cached_prefix target codePrefix Artifact.submission layout dataAbove
    (Artifact.submission.readCommit (deliveredSeedOutput oracle message key)).2 positions
  exact ⟨before,ran,boundary,delivered_cached_source_view oracle message key positions before boundary.source⟩

theorem delivered_cached_nonempty_postpass (oracle : Oracle) (message : Message) (key : Key)
    (positions : Positions) (before : MachineState) (nonempty : positions.card≠0)
    (boundary : CachedPrefixBoundary Artifact.submission
      (Artifact.submission.readCommit (deliveredSeedOutput oracle message key)).2 positions before) :
    let heap := referenceHeap oracle (pinnedLeafNodes oracle (deliveredReady oracle message key))
    let records := cachedRecords heap (deliveredSalts oracle key) positions
    let footer := cachedFooter (openingNodes positions) heap
    ∃ after cycles, (∀ fuel coins, execute openingControllerImage (cycles+fuel) (before.setPC 4096) coins=
        pure ⟨.success,after,cycles,0⟩) ∧
      BytesAt after (BitVec.ofNat 64 proofBase) (encodedRecords records++encode footer) ∧
      after.getReg .x6=BitVec.ofNat 64 (proofBase+(encodedRecords records).length+(encode footer).length) ∧
      (after.getReg .x11).toNat=(encodedRecords records).length+(encode footer).length ∧
      cycles≤2273*positions.card+66460+13*(openingNodes positions).length := by
  let heap := referenceHeap oracle (pinnedLeafNodes oracle (deliveredReady oracle message key))
  let records := cachedRecords heap (deliveredSalts oracle key) positions
  let groups := groupsBefore positions positions.card
  have frontier : openingNodes positions=capFrontierNodes groups 1 8 := by simp [openingNodes,nonempty,groups]
  have count : records.length=positions.card := cached_records_count heap (deliveredSalts oracle key) positions
  have hasRecord : records≠[] := by intro empty; rw [empty,List.length_nil] at count; omega
  have source := delivered_cached_source_view oracle message key positions before boundary.source
  rw [frontier] at source
  have encoded := congrArg (fun nodes : List Nat => encode (cachedFooter nodes heap)) frontier
  have raw := congrArg (fun nodes : List Nat => rawFieldsBytes (footerRawFields nodes (cachedFooter nodes heap))) frontier
  have packed := native_opening_nonempty groups records (cachedFooter (capFrontierNodes groups 1 8) heap) []
    (before.setPC 4096) proofBase rfl hasRecord
    (by simpa only [MachineState.getReg_setPC,count] using boundary.count)
    (by simpa only [MachineState.getReg_setPC] using boundary.pointer)
    (by simpa only [BytesAt,List.append_nil,heap,records,MachineState.getByte,MachineState.getMem,
      MachineState.setPC] using source) boundary.marks cached_controller_above
    (by simpa only [List.append_nil,←raw,records] using
      cached_source_separate heap (deliveredSalts oracle key) positions (cachedFooter (openingNodes positions) heap))
    (by simpa only [←frontier] using cached_controller_capacity positions)
  simpa only [←encoded,←frontier,count,records,heap] using packed

end CommitGolfCandidate.Chained.Native
