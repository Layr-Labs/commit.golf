import CommitGolfCandidate.Compact.OpeningOutput
import CommitGolfCandidate.NoncePaddingRecords
import CommitGolfCandidate.NonceCodec
import CommitGolfCandidate.Compact.EncodeIndex
/-! Byte-for-byte equality of actual compact opening output with the padding-removal encoding of the original certified machine output. -/
namespace CommitGolfCandidate.Compact
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem opening_nonce_eq (td : BitVec (8*submission.sizes.trapdoor)) (positions : Positions)
    (ordinal : Nat) (inside : ordinal<positions.card) :
    readBuffer (openingResult td positions).state (submission.layout.proof+792*ordinal) 24=
      readBuffer (CommitGolfCandidate.openingResult td positions).state
        (CommitGolfCandidate.submission.layout.proof+800*ordinal) 24 := by
  have compact := (arbitrary_output_records td positions ordinal inside).1
  have original := (CommitGolfCandidate.arbitrary_output_records td positions ordinal inside).1
  have truncated := congrArg (fun value : BitVec 256 => value.extractLsb' 0 192) original
  rw [read_buffer_slice _ _ 32 0 24 (by decide)] at truncated
  exact compact.trans truncated.symm

theorem opening_sibling_eq (td : BitVec (8*submission.sizes.trapdoor)) (positions : Positions)
    (ordinal : Nat) (inside : ordinal<positions.card) (level : Nat) (levelBound : level<24) :
    readBuffer (openingResult td positions).state (submission.layout.proof+792*ordinal+24+32*level) 32=
      readBuffer (CommitGolfCandidate.openingResult td positions).state
        (CommitGolfCandidate.submission.layout.proof+800*ordinal+32+32*level) 32 := by
  exact ((arbitrary_output_records td positions ordinal inside).2 level levelBound).trans
    ((CommitGolfCandidate.arbitrary_output_records td positions ordinal inside).2 level levelBound).symm
theorem opening_record_byte (td : BitVec (8*submission.sizes.trapdoor)) (positions : Positions)
    (ordinal : Nat) (inside : ordinal<positions.card) (offset : Nat) (small : offset<792) :
    (openingResult td positions).state.getByte
      (BitVec.ofNat 64 (submission.layout.proof+792*ordinal+offset))=
    (CommitGolfCandidate.openingResult td positions).state.getByte
      (BitVec.ofNat 64 (CommitGolfCandidate.submission.layout.proof+800*ordinal+
        (if offset<24 then offset else offset+8))) := by
  by_cases nonce : offset<24
  · have equal := congrArg (fun value : BitVec 192 => value.extractLsb' (8*offset) 8)
      (opening_nonce_eq td positions ordinal inside)
    rw [read_buffer_byte _ _ _ _ nonce,read_buffer_byte _ _ _ _ nonce] at equal
    simpa only [if_pos nonce] using equal
  · let level := (offset-24)/32
    let byte := (offset-24)%32
    have levelBound : level<24 := by dsimp [level];omega
    have byteBound : byte<32 := by dsimp [byte];omega
    have equal := congrArg (fun value : BitVec 256 => value.extractLsb' (8*byte) 8)
      (opening_sibling_eq td positions ordinal inside level levelBound)
    rw [read_buffer_byte _ _ _ _ byteBound,read_buffer_byte _ _ _ _ byteBound] at equal
    have compactAddress : submission.layout.proof+792*ordinal+24+32*level+byte=
        submission.layout.proof+792*ordinal+offset := by dsimp [level,byte];omega
    have oldAddress : CommitGolfCandidate.submission.layout.proof+800*ordinal+32+32*level+byte=
        CommitGolfCandidate.submission.layout.proof+800*ordinal+(offset+8) := by dsimp [level,byte];omega
    simpa only [compactAddress,oldAddress,if_neg nonce] using equal

theorem read_proof_byte (program : Submission) (result : Execution)
    (success : program.openingSucceeded result=true) (index : Nat)
    (inside : index<(result.state.getReg .x11).toNat) :
    (program.readProof result)[index]?=some (result.state.getByte
      (BitVec.ofNat 64 (program.layout.proof+index))) := by
  simp [Submission.readProof,success,List.getElem?_map,List.getElem?_range,inside]
theorem opening_proof_encoded (td : BitVec (8*submission.sizes.trapdoor)) (positions : Positions) :
    submission.readProof (openingResult td positions)=
      NonceCodec.encode positions.card
        (CommitGolfCandidate.submission.readProof (CommitGolfCandidate.openingResult td positions)) := by
  apply List.ext_getElem?
  intro index
  by_cases inside : index<792*positions.card
  · have sourceBound : NonceCodec.sourceIndex index<800*positions.card := by
      unfold NonceCodec.sourceIndex
      split <;> omega
    rw [NonceCodec.encode_index _ _ (CommitGolfCandidate.opening_proof_length td positions) _ inside,
      read_proof_byte _ _ (opening_result_succeeded td positions) _
        (by rw [opening_result_length];exact inside),
      read_proof_byte _ _ (CommitGolfCandidate.opening_result_succeeded td positions) _
        (by rw [CommitGolfCandidate.opening_result_length td positions];exact sourceBound)]
    apply congrArg some
    have equal := opening_record_byte td positions (index/792) (by omega) (index%792) (by omega)
    have address : submission.layout.proof+792*(index/792)+index%792=submission.layout.proof+index := by omega
    rw [address] at equal
    simpa only [NonceCodec.sourceIndex,Nat.add_assoc] using equal
  · rw [List.getElem?_eq_none (by rw [opening_proof_length];omega),
      List.getElem?_eq_none (by rw [NonceCodec.encode_length _ _
        (CommitGolfCandidate.opening_proof_length td positions)];omega)]
end CommitGolfCandidate.Compact
