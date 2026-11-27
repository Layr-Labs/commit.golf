import CommitGolf.Statements
/-! Binary tree geometry of the ptr image: every level has radix two. -/
namespace CommitGolfCandidate.Geo
open CommitGolf

def span (h : Nat) : Nat := 2^h
def radix (_ : Nat) : Nat := 2
def width (h : Nat) := (LENGTH + span h - 1) / span h
def nodeIndex (i h : Nat) := i / span h

theorem span_succ (h : Nat) : span (h+1)=span h*radix h := by simp [span,radix,Nat.pow_succ]
theorem span_pos (h : Nat) : 0<span h := Nat.two_pow_pos h
theorem nextIndex (i h : Nat) : nodeIndex i (h+1)=nodeIndex i h / radix h := by
  rw [nodeIndex,nodeIndex,span_succ,Nat.div_div_eq_div_mul]
theorem levels : (List.range 25).map width =
    [16777216,8388608,4194304,2097152,1048576,524288,262144,131072,65536,32768,16384,8192,
      4096,2048,1024,512,256,128,64,32,16,8,4,2,1] := by decide
theorem width_le (h : Nat) (small : h≤24) : width h=2^(24-h) := by
  unfold width span
  have e : LENGTH=2^(24-h)*2^h := by rw [←Nat.pow_add,Nat.sub_add_cancel small];rfl
  have pos : 0<2^h := Nat.two_pow_pos h
  rw [e,show 2^(24-h)*2^h+2^h-1=(2^h-1)+2^(24-h)*2^h by omega,Nat.add_mul_div_right _ _ pos,
    Nat.div_eq_of_lt (by omega),Nat.zero_add]
theorem indexInside (i : Index) (h : Nat) : nodeIndex i.val h<width h := by
  have pos : 0<span h:=span_pos h
  unfold nodeIndex width
  exact (Nat.div_lt_iff_lt_mul pos).mpr (by
    have bound:=i.isLt
    have all:=Nat.mod_add_div (LENGTH+span h-1) (span h)
    have rem:=Nat.mod_lt (LENGTH+span h-1) pos
    rw [Nat.mul_comm];omega)
theorem nodeIndex_pow (i h : Nat) : nodeIndex i h=i/2^h := rfl
end CommitGolfCandidate.Geo
