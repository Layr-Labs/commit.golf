import CommitGolfCandidate.ReconstructedWire

namespace CommitGolfCandidate.Reconstruction.Wire
open CommitGolf

def unpackBytes : List Byte → Nat
  | [] => 0
  | b::bs => b.toNat+256*unpackBytes bs

theorem unpack_append (a b : List Byte) :
    unpackBytes (a++b)=unpackBytes a+256^a.length*unpackBytes b := by
  induction a with
  | nil => simp [unpackBytes]
  | cons x xs ih =>
    simp only [List.cons_append,unpackBytes,ih,List.length_cons,pow_succ,Nat.mul_add]
    ac_rfl

private theorem digits (value n : Nat) :
    unpackBytes ((List.range n).map fun j => BitVec.ofNat 8 (value >>> (8*j))) = value % (256^n) := by
  induction n with
  | zero => simp [unpackBytes,Nat.mod_one]
  | succ n ih =>
    rw [List.range_succ,List.map_append,unpack_append,ih,List.length_map,List.length_range]
    simp only [List.map_cons,List.map_nil,unpackBytes,Nat.mul_zero,Nat.add_zero,BitVec.toNat_ofNat,Nat.shiftRight_eq_div_pow]
    have pw : 2^(8*n)=256^n := pow_mul 2 8 n
    rw [pw,show 256^(n+1)=256^n*256 from pow_succ _ _]
    exact (Nat.mod_mul ..).symm

theorem unpack_encoded (fs : List Field) : unpackBytes (bytes fs)=pack fs := by
  rw [bytes,digits]
  apply Nat.mod_eq_of_lt
  have h := pack_bound fs
  have size : bits fs ≤ 8*alignedBytes (bits fs) := by unfold alignedBytes;omega
  have pow := Nat.pow_le_pow_right (n:=2) (by decide) size
  rw [pow_mul] at pow
  exact h.trans_le pow

/-- Extract the field directly from the byte list returned by the encoder. -/
theorem read_encoded (a b : List Field) (f : Field) (width : f.width≤64) :
    HonestStream.get (unpackBytes (bytes (a++f::b))) (bits a) f.width=clipped f := by
  rw [unpack_encoded,field_read _ _ _ width]

end CommitGolfCandidate.Reconstruction.Wire
