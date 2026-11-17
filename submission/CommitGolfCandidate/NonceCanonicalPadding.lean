import CommitGolfCandidate.NonceCodecRoundtrip
import CommitGolfCandidate.NonceEncoding

namespace CommitGolfCandidate
open CommitGolf
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

theorem nonce_expanded_padding_byte (nonce : Nonce192) (byte : Nat) (bound : byte<8) :
    (expandNonce192 nonce).extractLsb' (8*(24+byte)) 8=0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit inside
  have beyond : 192 ≤ 8*(24+byte)+bit := by omega
  simp only [BitVec.getLsbD_extractLsb',inside,decide_true,Bool.true_and,BitVec.getLsbD_zero]
  simp only [expandNonce192,BitVec.zeroExtend,BitVec.getLsbD_setWidth]
  rw [BitVec.getLsbD_of_ge nonce _ beyond]
  simp

theorem nonce_canonical_of_windows {α : Type} (zero : α) (count : Nat) (bytes : List α)
    (padding : ∀ record<count, (bytes.drop (544*record+24)).take 8=List.replicate 8 zero) :
    NonceCodec.Canonical zero count bytes := by
  induction count generalizing bytes with
  | zero => trivial
  | succ count ih =>
    constructor
    · simpa only [Nat.mul_zero,Nat.zero_add] using padding 0 (by omega)
    · apply ih
      intro record inside
      have next:=padding (record+1) (by omega)
      rw [List.drop_drop]
      have address : 544+(544*record+24)=544*(record+1)+24 := by omega
      simpa only [address] using next
end CommitGolfCandidate
