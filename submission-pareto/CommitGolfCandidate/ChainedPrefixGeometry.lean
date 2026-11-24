import CommitGolfCandidate.ChainedCachedSource
import CommitGolfCandidate.ChainedOpeningRun

/-! The cached-prefix ABI leaves enough room for every raw packet and descriptor table. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 SplitCodec
open TwoPermutationPrototype.Sampling TwoPermutationPrototype.Opening

theorem cached_source_separate (heap : Nat → BitVec 238) (salts : Index → BitVec 128) (positions : Positions)
    (footer : Payload (InteriorCodec.footerSpec (openingNodes positions))) :
    proofBase+(rawRecordStream (cachedRecords heap salts positions)++
      rawFieldsBytes (footerRawFields (openingNodes positions) footer)).length≤proofBase+2^33 := by
  have cardinal : positions.card≤LENGTH := by simpa [Index] using Finset.card_le_univ positions
  have nodes := opening_nodes_bound positions
  rw [List.length_append,raw_record_stream_length,cached_records_count,footer_raw_fields_length]
  change positions.card≤16777216 at cardinal
  omega

theorem cached_controller_capacity (positions : Positions) :
    proofBase+2^33+max 34 (2*(openingNodes positions).length)≤MEMORY_BYTES := by
  have nodes := opening_nodes_bound positions
  have metadata : max 34 (2*(openingNodes positions).length)≤256 := by omega
  have room : proofBase+2^33+256≤MEMORY_BYTES := by decide
  omega

theorem cached_controller_above : 8192≤proofBase := by decide

end CommitGolfCandidate.Chained.Native
