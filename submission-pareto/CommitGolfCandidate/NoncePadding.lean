import CommitGolfCandidate.NonceBits
import CommitGolfCandidate.FastOpeningCertificate
import CommitGolfCandidate.NoncePaddingRecords
/-! The original machine emits zero nonce-padding bytes on every opening input; the proof reads the actual output memory. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem padded_digest_high (state : MachineState) (address : Nat) (nonce : BitVec 192)
    (aligned : address%8=0) (digest : readBuffer state address 32=expandNonce192 nonce) :
    state.getMem (BitVec.ofNat 64 (address+24))=0 := by
  rw [read_digest_words _ _ aligned] at digest
  have high := congrArg (fun x : BitVec 256 => x.extractLsb' 192 64) digest
  simp only [expandNonce192] at high
  rw [nonce_bits_high] at high
  exact high.trans (nonce_bits_expand_high nonce)

theorem padded_digest_byte (state : MachineState) (address : Nat) (nonce : BitVec 192)
    (aligned : address%8=0) (digest : readBuffer state address 32=expandNonce192 nonce)
    (index : Nat) (small : index<8) :
    state.getByte (BitVec.ofNat 64 (address+24+index))=0 := by
  have high := padded_digest_high state address nonce aligned digest
  obtain ⟨base,rfl⟩ : ∃ base,address=8*base := ⟨address/8,by omega⟩
  rw [show 8*base+24+index=8*base+(24+index) by omega,aligned_byte _ _ _ (by omega)]
  have div : (24+index)/8=3 := by omega
  rw [div]
  change extractByte (state.getMem (BitVec.ofNat 64 (8*base+24))) _=0
  rw [high]
  simp [extractByte]
theorem opening_padding (td : BitVec (8*submission.sizes.trapdoor)) (positions : Positions)
    (ordinal : Nat) (inside : ordinal<positions.card) :
    ((submission.readProof (openingResult td positions)).drop (800*ordinal+24)).take 8=
      List.replicate 8 0 := by
  have record := (arbitrary_output_records td positions ordinal inside).1
  have padding (index : Nat) (small : index<8) :
      (openingResult td positions).state.getByte
        (BitVec.ofNat 64 (submission.layout.proof+800*ordinal+24+index))=0 := by
    apply padded_digest_byte _ (submission.layout.proof+800*ordinal)
      ((readBuffer (openingInitializedState (submission.initialState .opening (td,positions))) (5368713248+24*openingIndex positions ordinal) 32).extractLsb' 0 192)
      (by change (10334769184+800*ordinal)%8=0;omega) record index small
  apply List.ext_getElem
  · simp only [List.length_take,List.length_drop,List.length_replicate,opening_proof_length]
    omega
  · intro index hleft hright
    have small : index<8 := by simpa using hright
    simp only [List.getElem_take,List.getElem_drop,List.getElem_replicate]
    simp only [Submission.readProof,opening_result_succeeded,if_true,opening_result_length,
      List.getElem_map,List.getElem_range]
    convert padding index small using 1 <;> congr 2 <;> omega
end CommitGolfCandidate
