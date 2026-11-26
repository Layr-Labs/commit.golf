import CommitGolfCandidate.S4Stores
import CommitGolfCandidate.S4Frames
namespace CommitGolfCandidate.S4.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (Digest)

private theorem pastEnd {n : Nat} (v : BitVec n) (start : Nat) (out : n≤start) : v.extractLsb' start 8=0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb',hi,decide_true,Bool.true_and,BitVec.getLsbD_zero]
  rw [BitVec.getLsbD_of_ge v (start+i) (by omega)];exact BitVec.getLsbD_zero.symm

theorem readPadded {s t : MachineState} {src dst n : Nat} (lim : n≤32) (bound : dst+32≤2^64)
    (move : Moved s t src dst n) (high : ∀ j,n≤j → j<32 → byte s (dst+j)=0) :
    readBuffer t dst 32=(readBuffer s src n).setWidth 256 := by
  have bytes (j : Nat) (bj : j<32) : t.getByte (W (dst+j))=
      ((readBuffer s src n).setWidth 256).extractLsb' (8*(0+j)) 8 := by
    rw [Nat.zero_add,BitVec.extractLsb'_setWidth_of_le (by omega)]
    by_cases low : j<n
    · have eqv:=move (dst+j) (by omega);rw [if_pos (by omega),Nat.add_sub_cancel_left] at eqv
      exact eqv.trans (read_buffer_byte s src n j low).symm
    · have eqv:=move (dst+j) (by omega);rw [if_neg (by omega)] at eqv
      exact eqv.trans ((high j (by omega) bj).trans (pastEnd _ _ (by omega)).symm)
  exact (read_serialized_slice t ((readBuffer s src n).setWidth 256) dst 0 32 bytes).trans BitVec.extractLsb'_eq_self

theorem afterClear {s t : MachineState} {src dst n : Nat} (size : n=30 ∨ n=32) (bound : dst+32≤2^64)
    (clear : Wrote s t (dst+24) 8 (fun _=>0)) : ∀ j,n≤j → j<32 → byte t (dst+j)=0 := by
  intro j small high;exact (clear (dst+j) (by omega)).trans (if_pos (by omega))

/-- Inputs and machine scratch surviving a read or digest write are described bytewise. -/
def SameOutside (s t : MachineState) (a n : Nat) := ∀ q,q<2^64 → (q<a ∨ a+n≤q) → byte t q=byte s q

theorem Moved.frame {s t : MachineState} {src dst n : Nat} (m : Moved s t src dst n) : SameOutside s t dst n :=
  fun q b away=>(m q b).trans (if_neg (by omega))
theorem Wrote.frame {s t : MachineState} {dst n : Nat} {v : Nat→Byte} (m : Wrote s t dst n v) : SameOutside s t dst n :=
  fun q b away=>(m q b).trans (if_neg (by omega))

theorem SameOutside.combined {s t u : MachineState} {a n b m l k : Nat}
    (first : SameOutside s t a n) (second : SameOutside t u b m)
    (within : l≤a ∧ a+n≤l+k ∧ l≤b ∧ b+m≤l+k) : SameOutside s u l k :=
  fun q bq away=>(second q bq (by omega)).trans (first q bq (by omega))

theorem SameOutside.read {s t : MachineState} {a n b m : Nat} (f : SameOutside s t a n)
    (bound : b+m≤2^64) (away : b+m≤a ∨ a+n≤b) : readBuffer t b m=readBuffer s b m := by
  unfold readBuffer;apply congrArg (BitVec.ofNat _);apply Finset.sum_congr rfl;intro j bj
  have h:=Finset.mem_range.mp bj
  exact congrArg (fun x : Byte=>x.toNat*2^(8*j)) (f (b+j) (by omega) (by omega))

theorem storeFrame (s : MachineState) (a : Nat) (v : Digest) (bound : a+32≤2^64) :
    SameOutside s (Late.store s a v) a 32 := by
  intro q bq away;unfold byte Late.store
  apply write_bits_byte_outside
  intro i hi eq
  change i<32 at hi
  have equal : W q=W (a+i):=eq.trans (BitVec.ofNat_add ..).symm
  have := wordNumber bq (by omega) equal;omega
end CommitGolfCandidate.S4.Machine
