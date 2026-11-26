import CommitGolfCandidate.S4Machine
import CommitGolfCandidate.MemoryCore

namespace CommitGolfCandidate.S4.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

abbrev W (a : Nat) := BitVec.ofNat 64 a
def byte (s : MachineState) (a : Nat) := s.getByte (W a)

/-- Source bytes are observed before the write. The frame is byte precise even
when a halfword at one end shares a doubleword with the surrounding proof. -/
def Moved (s t : MachineState) (src dst n : Nat) := ∀ q,q<2^64 →
  byte t q=if dst≤q ∧ q<dst+n then byte s (src+(q-dst)) else byte s q

theorem Moved.empty (s : MachineState) (src dst : Nat) : Moved s s src dst 0 := by
  intro q _;rw [if_neg (by omega)]

theorem Moved.append {s t u : MachineState} {src dst m n : Nat}
    (l : Moved s t src dst m) (r : Moved t u (src+m) (dst+m) n)
    (source : src+(m+n)≤2^64) (away : src+(m+n)≤dst ∨ dst+(m+n)≤src) :
    Moved s u src dst (m+n) := by
  intro q bq
  rw [r q bq]
  by_cases tail : dst+m≤q ∧ q<dst+m+n
  · rw [if_pos tail,if_pos (by omega)]
    have eqv : src+m+(q-(dst+m))=src+(q-dst):=by omega
    rw [eqv,l _ (by omega),if_neg (by omega)]
  · rw [if_neg tail,l _ bq]
    by_cases before : dst≤q ∧ q<dst+m
    · rw [if_pos before,if_pos (by omega)]
    · rw [if_neg before,if_neg (by omega)]

theorem Moved.congr {s s' t t' : MachineState} {a b n : Nat} (m : Moved s t a b n)
    (l : s'.mem=s.mem) (r : t'.mem=t.mem) : Moved s' t' a b n := by
  intro q h
  simpa only [byte,MachineState.getByte,MachineState.getMem,l,r] using m q h

theorem Moved.read {s t : MachineState} {a b n : Nat} (move : Moved s t a b n)
    (bounded : b+n≤2^64) : readBuffer t b n=readBuffer s a n := by
  unfold readBuffer
  apply congrArg (BitVec.ofNat _)
  apply Finset.sum_congr rfl
  intro j inside
  have hj:=Finset.mem_range.mp inside
  have h:=move (b+j) (by omega)
  rw [if_pos (by omega),Nat.add_sub_cancel_left] at h
  exact congrArg (fun x : Byte=>x.toNat*2^(8*j)) h

theorem Moved.away {s t : MachineState} {a b n i k : Nat} (move : Moved s t a b n)
    (bounded : i+k≤2^64) (out : i+k≤b ∨ b+n ≤ i) : readBuffer t i k=readBuffer s i k := by
  unfold readBuffer
  apply congrArg (BitVec.ofNat _)
  apply Finset.sum_congr rfl
  intro j inside
  have hj:=Finset.mem_range.mp inside
  exact congrArg (fun x : Byte=>x.toNat*2^(8*j)) ((move (i+j) (by omega)).trans (if_neg (by omega)))

def copyByte (s : MachineState) (src dst : Nat) := s.setByte (W dst) (byte s src)
theorem movedByte (s : MachineState) (src dst : Nat) (bd : dst<2^64) : Moved s (copyByte s src dst) src dst 1 := by
  intro q bq
  by_cases eqv : q=dst
  · subst q;simp only [byte,copyByte,set_byte_read,ite_true,le_refl,Nat.lt_succ_self,and_self,tsub_self,Nat.add_zero]
  · have distinct : W q≠W dst:=by
      intro e;have h:=congrArg BitVec.toNat e
      simp only [W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt bq,Nat.mod_eq_of_lt bd] at h
      exact eqv h
    simp only [byte,copyByte,set_byte_read,if_neg distinct,if_neg (by omega : ¬(dst≤q ∧ q<dst+1))]

end CommitGolfCandidate.S4.Machine
