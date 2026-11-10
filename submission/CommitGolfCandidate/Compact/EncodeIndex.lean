import CommitGolfCandidate.NonceCodec
/-! Exact byte-index correspondence for the nonce-padding removal codec, including record boundaries and authentication paths. -/
namespace CommitGolfCandidate.NonceCodec
open CommitGolf
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

def sourceIndex (index : Nat) : Nat :=
  800*(index/792)+(if index%792<24 then index%792 else index%792+8)

theorem encode_index (count : Nat) (proof : Proof) (length : proof.length=800*count)
    (index : Nat) (inside : index<792*count) :
    (encode count proof)[index]?=proof[sourceIndex index]? := by
  induction count generalizing proof index with
  | zero => omega
  | succ count ih =>
    have nonceLength : (proof.take 24).length=24 := by simp [length];omega
    have pathLength : ((proof.drop 32).take 768).length=768 := by simp [length];omega
    have recordLength : (proof.take 24++(proof.drop 32).take 768).length=792 := by
      simp [nonceLength,pathLength]
    rw [encode]
    by_cases first : index<792
    · rw [List.getElem?_append_left (by omega)]
      by_cases nonce : index<24
      · rw [List.getElem?_append_left (by omega),List.getElem?_take_of_lt nonce]
        congr 1
        simp [sourceIndex,Nat.div_eq_of_lt first,Nat.mod_eq_of_lt first,nonce]
      · rw [List.getElem?_append_right (by omega),nonceLength,
          List.getElem?_take_of_lt (by omega),List.getElem?_drop]
        congr 1
        simp [sourceIndex,Nat.div_eq_of_lt first,Nat.mod_eq_of_lt first,nonce]
        omega
    · rw [List.getElem?_append_right (by omega),recordLength]
      rw [ih (proof.drop 800) (by simp [length];omega) (index-792) (by omega),List.getElem?_drop]
      congr 1
      unfold sourceIndex
      have div : index/792=(index-792)/792+1 := by omega
      have mod : index%792=(index-792)%792 := by omega
      rw [div,mod]
      omega
end CommitGolfCandidate.NonceCodec
