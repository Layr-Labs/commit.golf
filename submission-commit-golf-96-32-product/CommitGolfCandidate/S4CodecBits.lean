import CommitGolfCandidate.S4CodecPrefix

set_option Elab.async false
namespace CommitGolfCandidate.S4.Codec
open CommitGolf RiscvZkvm.Rv64
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
def shifted (v : Byte) (p : Nat) : Word := v.zeroExtend 64 >>> (2*p)
theorem shiftMore (v : Byte) (p : Nat) (hp : p<4) : shifted v p >>> 2=shifted v (p+1) := by
  unfold shifted;rw [←BitVec.shiftRight_add] <;> congr 1 <;> omega
theorem storeBits (v orig : Byte) (p : Nat) (hp : p<4) :
    (loadedField false orig (shifted v p)).truncate 8=Carry.overlay orig (Carry.chunk v p) := by
  unfold loadedField shifted Carry.overlay Carry.chunk
  interval_cases p <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;> interval_cases i <;> simp (config:={decide:=true})
theorem storeLow (v : Byte) (x : Word) : (loadedField true v x).truncate 8=Carry.lower v := by
  unfold loadedField Carry.lower
  apply BitVec.eq_of_getLsbD_eq;intro i hi;interval_cases i <;> simp (config:={decide:=true})
theorem join (a v : Byte) (p : Nat) (hp : p<4) :
    a.zeroExtend 64 ||| (highWord v <<< (2*p))=(a ||| (Carry.upper v <<< (2*p))).zeroExtend 64 := by
  interval_cases p <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;> interval_cases i <;> simp (config:={decide:=true}) [highWord,Carry.upper]

end CommitGolfCandidate.S4.Codec
