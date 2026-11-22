import CommitGolfCandidate.Layout2Codec
import CommitGolfCandidate.Layout2Helpers
import RiscvZkvm.Rv64.Logic.MemRegionWrite

namespace CommitGolfCandidate.Layout2
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CommitGolfCandidate.Layout2Helpers
abbrev addr := BitVec.ofNat 64
def byte (s : MachineState) (a : Nat) : Byte := s.getByte (addr a)

theorem byte_store (s : MachineState) (a q : Word) (v : Byte) :
    (s.setByte a v).getByte q = if q=a then v else s.getByte q := by
  by_cases eq : q=a
  · subst q
    simp only [ite_true, MachineState.setByte, MachineState.getByte,MachineState.getMem_setMem_eq]
    exact extractByte_replaceByte_same _ ⟨_,byteOffset_lt_8⟩ _
  · rw [if_neg eq]
    unfold MachineState.setByte MachineState.getByte
    by_cases same : alignToDword q=alignToDword a
    · rw [same,MachineState.getMem_setMem_eq]
      apply extractByte_replaceByte_diff _ _ byteOffset_lt_8 byteOffset_lt_8
      intro e
      exact eq (by rw [←alignToDword_add_byteOffset q,same,e,alignToDword_add_byteOffset])
    · rw [MachineState.getMem_setMem_ne same]

/-- Bytewise frame valid across unaligned endpoints, including a shared partial dword. -/
def Writes (s t : MachineState) (base n : Nat) (data : Nat → Byte) :=
  ∀ q, q<MEMORY_BYTES → byte t q=if base≤q ∧ q<base+n then data (q-base) else byte s q

theorem writes_zero (s : MachineState) (base : Nat) (data : Nat→Byte) : Writes s s base 0 data := by
  intro q fit;simp [show ¬(base≤q ∧ q<base+0) by omega]

theorem Writes.atIndex {s t base n data} (h : Writes s t base n data) (j : Nat) (hj : j<n)
    (endFits : base+n≤MEMORY_BYTES) : byte t (base+j)=data j := by
  simpa [show base+j<base+n by omega] using h (base+j) (by omega)

theorem Writes.outside {s t base n data} (h : Writes s t base n data) (q : Nat)
    (fit : q<MEMORY_BYTES) (separate : q<base ∨ base+n≤q) : byte t q=byte s q := by
  simpa only [if_neg (show ¬(base≤q ∧ q<base+n) by omega)] using h q fit

theorem Writes.store {s t base n data} (h : Writes s t base n data)
    (v : Byte) (eq : v=data n) (inside : base+n<MEMORY_BYTES) :
    Writes s (t.setByte (addr (base+n)) v) base (n+1) data := by
  intro q hq
  have bound : MEMORY_BYTES ≤ 2^64 := by decide
  have same : addr q=addr (base+n) ↔ q=base+n := by
    constructor
    · intro e;have f:=congrArg BitVec.toNat e
      simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show q<2^64 by omega),
        Nat.mod_eq_of_lt (show base+n<2^64 by omega)] using f
    · rintro rfl;rfl
  unfold byte
  simp only [byte_store, same]
  change (if q=base+n then v else byte t q)=_
  rw [h q hq]
  split_ifs <;> first | omega | (congr 1 <;> omega) | exact eq | (rw [eq];congr 1;omega)

theorem Writes.move {s s' t t' base n data} (h : Writes s t base n data)
    (before : s'.mem=s.mem) (after : t'.mem=t.mem) : Writes s' t' base n data := by
  intro q fit
  simpa only [byte, MachineState.getByte, MachineState.getMem, before,after] using h q fit

theorem Writes.append {s t u base n m data} (h : Writes s t base n data)
    (h' : Writes t u (base+n) m (fun j=>data (n+j))) : Writes s u base (n+m) data := by
  intro q hq
  rw [h' q hq,h q hq]
  dsimp only
  split_ifs <;> first | omega | (congr 1 <;> omega) | rfl

theorem bword {s t : MachineState} (w : Nat) (fits : 8*w+8≤MEMORY_BYTES)
    (bytes : ∀ j, j<8 → byte s (8*w+j)=byte t (8*w+j)) :
    s.getMem (addr (8*w))=t.getMem (addr (8*w)) := by
  apply eq_of_forall_extractByte; intro j hj
  have fit : 8*w+8≤2^64 := by dsimp [MEMORY_BYTES] at fits;omega
  exact (byte_at s _ j (by omega) hj fit).symm.trans
    ((bytes j hj).trans (byte_at t _ j (by omega) hj fit))

end CommitGolfCandidate.Layout2
