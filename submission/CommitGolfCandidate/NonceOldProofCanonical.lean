import CommitGolfCandidate.NonceCanonicalPadding
import CommitGolfCandidate.CapOpenLoadedBytes

/-! Every original loaded opening has zero nonce padding, even for arbitrary
private trapdoor bits. The codec therefore restores its full byte transcript. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 8192
set_option maxHeartbeats 500000

theorem nonce_old_proof_padding (trapdoor : BitVec (8*capProgram.sizes.trapdoor))
    (positions : Positions) (record byte : Nat) (present : record<positions.card) (inside : byte<8) :
    (capOpenLoadedBytes trapdoor positions)[544*record+24+byte]?.getD 0=0 := by
  have slotBound : 17*record<(capOpenLowerDigests trapdoor positions).length := by
    rw [cap_open_lower_digests_length]; omega
  have selected:=cap_encoding_byte (capOpenLowerDigests trapdoor positions)
    (capDigestEncoding (capOpenBoundaryDigests trapdoor positions)) (17*record) (24+byte) slotBound (by omega)
  have address : 32*(17*record)+(24+byte)=544*record+24+byte := by omega
  rw [address] at selected
  change (capOpenLoadedBytes trapdoor positions)[544*record+24+byte]?.getD 0=_ at selected
  rw [selected]
  have remainder : (17*record)%17=0 := by omega
  simp only [capOpenLowerDigests,List.getElem_ofFn,remainder,capLowerSlotPayload,ite_true]
  exact nonce_expanded_padding_byte _ byte inside

theorem nonce_old_proof_canonical (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions) :
    NonceCodec.Canonical (0:Byte) positions.card (capOpenLoadedBytes trapdoor positions) := by
  apply nonce_canonical_of_windows
  intro record present
  have lengthEq:=cap_open_loaded_bytes_length trapdoor positions
  apply List.ext_getElem
  · simp only [List.length_take,List.length_drop,List.length_replicate]
    omega
  · intro byte firstBound secondBound
    have bound : byte<8 := by simpa only [List.length_replicate] using secondBound
    have sourceBound : 544*record+24+byte<(capOpenLoadedBytes trapdoor positions).length := by omega
    have selected:=nonce_old_proof_padding trapdoor positions record byte present bound
    rw [List.getElem?_eq_getElem sourceBound,Option.getD_some] at selected
    simp only [List.getElem_take,List.getElem_drop,List.getElem_replicate]
    exact selected

theorem nonce_old_proof_roundtrip (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions) :
    NonceCodec.expand 0 positions.card (NonceCodec.compact positions.card (capOpenLoadedBytes trapdoor positions))=
      capOpenLoadedBytes trapdoor positions := by
  apply NonceCodec.canonical_roundtrip
  · rw [cap_open_loaded_bytes_length]; omega
  · exact nonce_old_proof_canonical trapdoor positions
end CommitGolfCandidate
