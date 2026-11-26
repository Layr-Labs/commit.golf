import CommitGolfCandidate.LateOpenCopy
import CommitGolfCandidate.LateModel

namespace CommitGolfCandidate.Late.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

structure Copied (s t : MachineState) (src dst n : Nat) : Prop where
  outside : Outside s t dst (8*n)
  words : ∀ j<n, wordAt t (dst+8*j)=wordAt s (src+8*j)

theorem copied (s : MachineState) (src dst : Nat) (sp : s.getReg .x23=BitVec.ofNat 64 src)
    (dp : s.getReg .x25=BitVec.ofNat 64 dst) (n : Nat) (small : n≤4)
    (sa : AddrOK src (8*n)) (da : AddrOK dst (8*n)) (sep : src+8*n≤dst) :
    Copied s (copyWords s n) src dst n := by
  induction n with
  | zero => exact ⟨fun _ _ _ _ => rfl,fun j H => by omega⟩
  | succ n ih =>
    have sb := sa.2; have db := da.2
    have prev := ih (by omega) ⟨sa.1,by omega⟩ ⟨da.1,by omega⟩ (by omega)
    let r := copyWords s n
    have atWord (a : Nat) (h : a<MEMORY_BYTES) :
        wordAt (copyWords s (n+1)) a =
        if a=dst+8*n then wordAt r (src+8*n) else wordAt r a :=
      copy_word_effect r n (by omega) src dst a ((copy_keeps s n _ (by decide)).trans sp)
        ((copy_keeps s n _ (by decide)).trans dp) (by unfold MEMORY_BYTES at h; omega)
        (by unfold MEMORY_BYTES at db;omega)
    constructor
    · intro a h al away
      rw [atWord a h,if_neg (by omega)]
      exact prev.outside a h al (by omega)
    · intro j hj
      rw [atWord _ (by omega)]
      by_cases last : j=n
      · subst j; rw [if_pos rfl]
        exact prev.outside _ (by omega) (by have := sa.1;omega) (Or.inl (by omega))
      · rw [if_neg (by omega)]
        exact prev.words j (by omega)

private theorem aligned_read (s : MachineState) (a k : Nat) (align : a%8=0) :
    byteAt s (a+k) = extractByte (wordAt s (a+8*(k/8))) (k%8) := by
  rw [byte_word,show 8*((a+k)/8)=a+8*(k/8) by omega,show (a+k)%8=k%8 by omega]

theorem Copied.data {s t : MachineState} {src dst n : Nat} (copy : Copied s t src dst n)
    (sa : src%8=0) (da : dst%8=0) (k : Nat) (hi : k<8*n) :
    byteAt t (dst+k)=byteAt s (src+k) := by
  rw [aligned_read _ _ _ da,aligned_read _ _ _ sa,copy.words (k/8) (by omega)]

theorem copied_bytes {s t : MachineState} {src dst n : Nat} (copy : Copied s t src dst n)
    (sa : src%8=0) (da : dst%8=0) (v : BitVec (8*(8*n))) (read : readBuffer s src (8*n)=v) :
    Written s t dst (bytes (n:=8*n) v) := by
  have len : (bytes (n:=8*n) v).length=8*n := by simp only [bytes,List.length_ofFn]
  refine ⟨?_,?_⟩
  · rw [len];exact copy.outside
  · intro j hj
    have bounded : j<8*n := len ▸ hj
    exact (copy.data sa da j bounded).trans ((read_bytes s src (8*n) v read) j hj)

end CommitGolfCandidate.Late.Open
