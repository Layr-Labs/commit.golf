import CommitGolfCandidate.ReconstructedHonestStream
import CommitGolfCandidate.ReconstructedFrontier
import CommitGolf.Parameters

namespace CommitGolfCandidate.Reconstruction.Wire
open CommitGolf
universe u
variable {α : Type u}

structure Field where
  value : Nat
  width : Nat

def clipped (f : Field) := f.value % 2^f.width

def bits : List Field → Nat
  | [] => 0
  | f::rest => f.width+bits rest

def pack : List Field → Nat
  | [] => 0
  | f::rest => clipped f + 2^f.width*pack rest

theorem bits_append (a b : List Field) : bits (a++b)=bits a+bits b := by
  induction a with
  | nil => simp [bits]
  | cons x xs ih => simp [bits,ih,Nat.add_assoc]

theorem pack_append (a b : List Field) : pack (a++b) = pack a+2^(bits a)*pack b := by
  induction a with
  | nil => simp [pack,bits]
  | cons x xs ih =>
    simp only [List.cons_append,pack,bits,ih,pow_add,Nat.mul_add,Nat.mul_assoc,Nat.add_assoc]

theorem pack_bound (fs : List Field) : pack fs<2^(bits fs) := by
  induction fs with
  | nil => decide
  | cons x xs ih =>
    have hx : clipped x<2^x.width := Nat.mod_lt _ (Nat.two_pow_pos _)
    have m := Nat.mul_le_mul_left (2^x.width) ih
    simp only [bits,pack,pow_add]
    rw [Nat.mul_succ] at m
    omega

/-- Each emitted field is recovered even when it crosses a 64-bit word boundary. -/
theorem field_read (before after : List Field) (f : Field) (width : f.width≤64) :
    HonestStream.get (pack (before++f::after)) (bits before) f.width=clipped f := by
  rw [HonestStream.get_eq _ _ _ width,pack_append,Nat.shiftRight_eq_div_pow,
    Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),Nat.div_eq_of_lt (pack_bound before),Nat.zero_add,pack,
    Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (Nat.mod_lt _ (Nat.two_pow_pos _))

def bytes (fs : List Field) : Proof := (List.range (alignedBytes (bits fs))).map
  (fun j => BitVec.ofNat 8 (pack fs >>> (8*j)))

theorem byte_count (fs : List Field) : (bytes fs).length=alignedBytes (bits fs) := by simp [bytes]

theorem byte_at (fs : List Field) (i : Nat) (inside : i<alignedBytes (bits fs)) :
    (bytes fs)[i]? = some (BitVec.ofNat 8 (pack fs >>> (8*i))) := by
  simp [bytes,List.getElem?_range,inside]

theorem zero_padding (fs : List Field) : pack fs >>> bits fs=0 := by
  rw [Nat.shiftRight_eq_div_pow];exact Nat.div_eq_of_lt (pack_bound fs)

theorem flat_bits (xs : List α) (f : α → List Field) (n : Nat) (sz : ∀ x, bits (f x)=n) :
    bits (xs.flatMap f)=n*xs.length := by
  induction xs with
  | nil => simp [bits]
  | cons x xs ih => simp [bits_append,ih,sz,Nat.mul_succ,Nat.add_comm]

end CommitGolfCandidate.Reconstruction.Wire
