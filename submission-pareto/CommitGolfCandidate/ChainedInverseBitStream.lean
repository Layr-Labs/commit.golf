import CommitGolfCandidate.ChainedInverseRows

/-! Relate the inverse stream's consumed bytes to the codec's bit addresses. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf SplitCodec

def byteBits (byte : BitVec 8) : List Bool := List.ofFn fun bit : Fin 8 => byte.getLsbD bit.val

@[simp] theorem byte_bits_length (byte : BitVec 8) : (byteBits byte).length=8 := by simp [byteBits]

theorem byte_bits_getD (byte : BitVec 8) (bit : Nat) (inside : bit<8) :
    (byteBits byte).getD bit false=byte.getLsbD bit := by
  simp only [byteBits,List.getD_eq_getElem?_getD,List.getElem?_ofFn,inside,↓reduceDIte,Option.getD_some]

theorem byte_bits_word (byte : BitVec 8) : tailBitsWord 8 (byteBits byte)=byte := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit inside
  rw [tail_bits_word_bit 8 _ bit inside,byte_bits_getD byte bit inside]

theorem pull_bit_bytes_length (input : Nat → List Bool) (count : Nat)
    (byteSize : ∀ i, (input i).length=8) : (pullBitBytes input count).length=8*count := by
  induction count generalizing input with
  | zero => rfl
  | succ count ih =>
    simp only [pullBitBytes,List.length_append,byteSize]
    rw [ih _ (fun i => byteSize _)]
    omega

theorem pull_bit_bytes_getD (input : Nat → BitVec 8) (count bit : Nat) (inside : bit<8*count) :
    (pullBitBytes (fun i => byteBits (input i)) count).getD bit false=
      (input (bit/8)).getLsbD (bit%8) := by
  induction count generalizing input bit with
  | zero => omega
  | succ count ih =>
    change (byteBits (input 0)++pullBitBytes (fun i => byteBits (input (1+i))) count).getD bit false=_
    by_cases before : bit<8
    · rw [List.getD_append _ _ false bit (by simpa using before),
        byte_bits_getD _ bit before,Nat.div_eq_of_lt before,Nat.mod_eq_of_lt before]
    · rw [List.getD_append_right _ _ false bit (by simp only [byte_bits_length]; omega),byte_bits_length]
      rw [ih (fun i => input (1+i)) (bit-8) (by omega)]
      rw [show 1+(bit-8)/8=bit/8 by omega,show (bit-8)%8=bit%8 by omega]

theorem pull_proof_bits (proof : Proof) (count : Nat) :
    pullBitBytes (fun i => byteBits (proof.getD i 0)) count=unpackBits (8*count) proof := by
  apply List.ext_getElem
  · rw [pull_bit_bytes_length _ _ (by simp)]
    simp [unpackBits]
  · intro bit left right
    have inside : bit<8*count := by
      simpa only [pull_bit_bytes_length (fun i => byteBits (proof.getD i 0)) count
        (fun i => byte_bits_length _)] using left
    have result := pull_bit_bytes_getD (fun i => proof.getD i 0) count bit inside
    simp only [unpackBits,List.getElem_ofFn,readBit]
    rw [←List.getD_eq_getElem _ _ left]
    exact result

theorem inverse_plan_read_exact (widths : List Nat) (input : Nat → List Bool)
    (byteSize : ∀ i, (input i).length=8) (small : ∀ width ∈ widths, width≤6) :
    (tailParsePlan widths [] input).read=(widths.sum+7)/8 := by
  have shape := tail_parse_plan_widths widths [] input byteSize small
  have rows : (tailParsePlan widths [] input).fields.flatten.length=widths.sum := by
    rw [List.length_flatten,shape]
  have bits := congrArg List.length (tail_parse_plan_bits widths [] input)
  simp only [List.length_append,List.nil_append,pull_bit_bytes_length _ _ byteSize,rows] at bits
  have pending := tail_parse_plan_pending widths [] input (by simp) byteSize
  omega

end CommitGolfCandidate.Chained.Native
