import CommitGolfCandidate.NonceCodec

/-! Expansion exactly recovers full proofs whose discarded padding bytes
are zero. No assumption is imposed on nonce, sibling or suffix contents. -/
namespace CommitGolfCandidate.NonceCodec
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

def Canonical {α : Type} (zero : α) : Nat → List α → Prop
  | 0,_ => True
  | count+1,bytes => (bytes.drop 24).take 8=List.replicate 8 zero ∧ Canonical zero count (bytes.drop 544)

theorem canonical_roundtrip {α : Type} (zero : α) (count : Nat) (bytes : List α)
    (enough : 544*count ≤ bytes.length) (canonical : Canonical zero count bytes) :
    expand zero count (compact count bytes)=bytes := by
  induction count generalizing bytes with
  | zero => rfl
  | succ count ih =>
    have padding:=canonical.1
    have nonceLength : (bytes.take 24).length=24 := by simp only [List.length_take]; omega
    have siblingLength : ((bytes.drop 32).take 512).length=512 := by
      simp only [List.length_take,List.length_drop]; omega
    let record : Record α:=⟨bytes.take 24,(bytes.drop 32).take 512,nonceLength,siblingLength⟩
    have decomposed : bytes=full zero record++bytes.drop 544 := by
      have parts : bytes.take 544=bytes.take 24++(bytes.drop 24).take 8++(bytes.drop 32).take 512 := by
        rw [show 544=32+512 by decide,List.take_add,show 32=24+8 by decide,List.take_add]
      calc
        bytes=bytes.take 544++bytes.drop 544 := (List.take_append_drop 544 bytes).symm
        _=full zero record++bytes.drop 544 := by rw [parts,padding]; rfl
    have tailEnough : 544*count ≤ (bytes.drop 544).length := by simp only [List.length_drop]; omega
    have recursion:=ih (bytes.drop 544) tailEnough canonical.2
    conv_lhs => rw [decomposed,compact_cons,expand_cons,recursion]
    exact decomposed.symm
end CommitGolfCandidate.NonceCodec
