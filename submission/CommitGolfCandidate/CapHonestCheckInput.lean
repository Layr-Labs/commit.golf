import CommitGolfCandidate.CapHonestOpening
import CommitGolfCandidate.CapCheckEncodedAccepts
import CommitGolfCandidate.CapOpenResult
import CommitGolfCandidate.InputOrder

/-! Honest openings at every cardinality feed the actual checker ABI. Admission
uses the full output-capacity theorem, independently of the batch-256 score
bound. The nonempty acceptance theorem retains actual committed-heap facts;
the empty opening is handled separately by the scheme wrapper. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option autoImplicit false
set_option maxHeartbeats 200000

def capHonestCheckInput (message : Message) (committed : MachineState)
    (positions : Positions) : CheckInput :=
  ⟨readBuffer committed capProgram.layout.commitment 32,positions,
    fun index => message index.val,
    capOpenLoadedBytes
      (readBuffer committed capProgram.layout.trapdoor capProgram.sizes.trapdoor)
      positions⟩

theorem cap_honest_input_parsed (message : Message) (committed : MachineState)
    (positions : Positions) :
    CapCheckParsedRecords (capHonestCheckInput message committed positions)
      (capHonestLowerRecords message committed positions)
      (capDigestEncoding (capOpenBoundaryDigests
        (readBuffer committed capProgram.layout.trapdoor capProgram.sizes.trapdoor)
        positions)) := by
  constructor
  · change capOpenLoadedBytes _ positions=_
    rw [capOpenLoadedBytes,
      cap_honest_lower_loaded_transcript message committed positions]
  · exact cap_open_loaded_bytes_capacity _ positions
  · simp only [capHonestLowerRecords,List.length_map,capOpenRequestedIndices,
      Finset.length_sort,capHonestCheckInput]
  · intro ordinal inside present
    change ordinal < positions.card at present
    simp only [capHonestLowerRecords,List.getElem_map,capHonestLowerRecord,
      capOpenRequestedIndices,capHonestCheckInput]
  · intro ordinal inside present
    change ordinal < positions.card at present
    simp only [capHonestLowerRecords,List.getElem_map,capHonestLowerRecord,
      capOpenRequestedIndices,capHonestCheckInput]
    have order := sorted_value_index positions ordinal present
    change message ((positions.sort (· ≤ ·))[ordinal]'(by simpa using present)) =
      message ((positions.attach.sort (fun i j => i.val≤j.val))[ordinal]'(by
        simpa using present)).val
    apply congrArg message
    apply Fin.ext
    simpa only [openingIndex,dif_pos present] using order.symm

theorem cap_honest_nonempty_check (oracle : Oracle) (message : Message)
    (committed : MachineState) (correct : CommittedState oracle message committed)
    (positions : Positions) (positive : 0 < positions.card) :
    let input := capHonestCheckInput message committed positions
    (oracle.eval (capProgram.scheme.check input.commitment input.positions
      input.values input.proof)).1=true := by
  obtain ⟨roots,lower,agree⟩ :=
    cap_honest_lower_collection oracle message committed correct positions
  apply cap_check_encoded_accepts oracle
    (capHonestCheckInput message committed positions)
    (capHonestLowerRecords message committed positions)
    (capOpenBoundaryDigests
      (readBuffer committed capProgram.layout.trapdoor capProgram.sizes.trapdoor) positions)
    (cap_honest_input_parsed message committed positions) positive roots lower
  exact cap_honest_cap_accepts oracle message committed correct positions roots lower agree

end CommitGolfCandidate
