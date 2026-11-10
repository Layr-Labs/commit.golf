import CommitGolfCandidate.FastOpeningCertificate
/-! A byte-list codec removes each record’s eight zero nonce-padding bytes, retaining its 24-byte nonce and 768-byte authentication path. -/
namespace CommitGolfCandidate.NonceCodec
open CommitGolf
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def encode : Nat → Proof → Proof
  | 0,_ => []
  | count+1,proof => proof.take 24 ++ (proof.drop 32).take 768 ++ encode count (proof.drop 800)

def pad : Nat → Proof → Proof
  | 0,_ => []
  | count+1,proof => proof.take 24 ++ List.replicate 8 0 ++
      (proof.drop 24).take 768 ++ pad count (proof.drop 792)

def decode (count : Nat) (proof : Proof) : Proof :=
  if proof.length=792*count then pad count proof else [0]

def Good : Nat → Proof → Prop
  | 0,proof => proof=[]
  | count+1,proof => proof.length=800*(count+1) ∧
      (proof.drop 24).take 8=List.replicate 8 0 ∧ Good count (proof.drop 800)

theorem encode_length (count : Nat) (proof : Proof) (length : proof.length=800*count) :
    (encode count proof).length=792*count := by
  induction count generalizing proof with
  | zero => rfl
  | succ count ih =>
    have tailLength : (proof.drop 800).length=800*count := by simp [length];omega
    simp only [encode,List.length_append,List.length_take,List.length_drop,length,ih _ tailLength]
    rw [Nat.min_eq_left (by omega),Nat.min_eq_left (by omega)]
    omega

theorem pad_length (count : Nat) (proof : Proof) (length : proof.length=792*count) :
    (pad count proof).length=800*count := by
  induction count generalizing proof with
  | zero => rfl
  | succ count ih =>
    have tailLength : (proof.drop 792).length=792*count := by simp [length];omega
    simp only [pad,List.length_append,List.length_take,List.length_drop,
      List.length_replicate,length,ih _ tailLength]
    rw [Nat.min_eq_left (by omega),Nat.min_eq_left (by omega)]
    omega

theorem good_length (count : Nat) (proof : Proof) (good : Good count proof) :
    proof.length=800*count := by
  cases count with
  | zero => rw [show proof=[] from good];rfl
  | succ count => exact good.1

theorem reconstruct_record (proof : Proof) (zero : (proof.drop 24).take 8=List.replicate 8 0) :
    proof.take 24 ++ List.replicate 8 0 ++ (proof.drop 32).take 768 ++ proof.drop 800=proof := by
  rw [←zero,←List.take_add]
  change proof.take 32 ++ (proof.drop 32).take 768 ++ proof.drop 800=proof
  rw [←List.take_add]
  exact List.take_append_drop 800 proof

theorem pad_encode (count : Nat) (proof : Proof) (good : Good count proof) :
    pad count (encode count proof)=proof := by
  induction count generalizing proof with
  | zero => exact good.symm
  | succ count ih =>
    obtain ⟨length,zero,tailGood⟩ := good
    have firstLength : (proof.take 24).length=24 := by simp [length];omega
    have pathLength : ((proof.drop 32).take 768).length=768 := by simp [length];omega
    have takeFirst (a b c : Proof) (ha : a.length=24) : (a++b++c).take 24=a := by
      rw [List.take_append_of_le_length (by rw [List.length_append,ha];omega),
        List.take_append_of_le_length (by omega)]
      simpa [←ha] using List.take_length a
    have dropFirst (a b c : Proof) (ha : a.length=24) : (a++b++c).drop 24=b++c := by
      rw [List.append_assoc,←ha,List.drop_append_length]
    have takePath (b c : Proof) (hb : b.length=768) : (b++c).take 768=b := by
      simpa [←hb] using (List.take_append_length (l₁:=b) (l₂:=c))
    have dropRecord (a b c : Proof) (ha : a.length=24) (hb : b.length=768) :
        (a++b++c).drop 792=c := by
      have hab : (a++b).length=792 := by simp [ha,hb]
      rw [←hab,List.drop_append_length]
    simp only [encode,pad]
    rw [takeFirst _ _ _ firstLength,dropFirst _ _ _ firstLength,
      takePath _ _ pathLength,dropRecord _ _ _ firstLength pathLength,ih _ tailGood]
    exact reconstruct_record proof zero

theorem decode_encode (count : Nat) (proof : Proof) (good : Good count proof) :
    decode count (encode count proof)=proof := by
  rw [decode,if_pos (encode_length count proof (good_length count proof good))]
  exact pad_encode count proof good
theorem good_of_records (count : Nat) (proof : Proof)
    (length : proof.length=800*count)
    (zeros : ∀ ordinal < count,
      (proof.drop (800*ordinal+24)).take 8=List.replicate 8 0) : Good count proof := by
  induction count generalizing proof with
  | zero => simpa [Good] using List.length_eq_zero_iff.mp (by omega : proof.length=0)
  | succ count ih =>
    refine ⟨length, ?_, ?_⟩
    · simpa using zeros 0 (by omega)
    · apply ih
      · simp only [List.length_drop,length];omega
      · intro ordinal inside
        simpa only [List.drop_drop, show 800+(800*ordinal+24)=800*(ordinal+1)+24 by omega]
          using zeros (ordinal+1) (by omega)
end CommitGolfCandidate.NonceCodec
