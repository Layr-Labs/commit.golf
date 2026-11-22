import CommitGolfCandidate.Layout2Invariant
namespace CommitGolfCandidate.Layout2
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 TwoPermutationPrototype.GroupedOpening.Wide
open TwoPermutationPrototype.GroupedOpening (halfword_of_bytes)
set_option maxHeartbeats 1000000

/-- The temporary block is live during conversion. All other RAM follows the proof-prefix update. -/
def Outside (q : Nat) := q<scratchBase ∨ scratchBase+2136≤q
def Records (s t : MachineState) (base n : Nat) (f : Nat→Byte) :=
  ∀ q, q<MEMORY_BYTES → Outside q →
    byte t q=if base≤q ∧ q<base+n then f (q-base) else byte s q

theorem Records.zero (s : MachineState) (base : Nat) (f : Nat→Byte) : Records s s base 0 f := by
  intro q _ _;simp
theorem Records.outside {s t p n f} (h : Records s t p n f) (q : Nat) (fit : q<MEMORY_BYTES)
    (out : Outside q) (away : q<p ∨ p+n≤q) : byte t q=byte s q := by
  simpa only [if_neg (show ¬(p≤q ∧ q<p+n) by omega)] using h q fit out
theorem Records.move {s s' t t' p n f} (h : Records s t p n f)
    (pre : s'.mem=s.mem) (post : t'.mem=t.mem) : Records s' t' p n f := by
  intro q fit out
  simpa only [byte, MachineState.getByte, MachineState.getMem, pre,post] using h q fit out
theorem Records.append {s t u p n m f g} (first : Records s t p n f) (last : Records t u (p+n) m g)
    (consistent : ∀ j, j<m → g j=f (n+j)) : Records s u p (n+m) f := by
  intro q fit out
  rw [last q fit out,first q fit out]
  by_cases b : p+n≤q ∧ q<p+n+m
  · rw [if_pos b,if_pos (by omega),consistent _ (by omega),show n+(q-(p+n))=q-p by omega]
  · rw [if_neg b]
    by_cases a : p≤q ∧ q<p+n
    · simp [a,show p≤q ∧ q<p+(n+m) by omega]
    · simp [a,show ¬(p≤q ∧ q<p+(n+m)) by omega]

theorem copied_then_emitted {s t u p n f g} (temp : Writes s t scratchBase n f)
    (sized : n≤2136) (write : Writes t u p n g) : Records s u p n g := by
  intro q fit out
  rw [write q fit,temp.outside q fit (by unfold Outside at out;omega)]

theorem Records.table {s t p n f τ r tb} (rec : Records s t p n f) (read : Table τ r tb s)
    (below : p+n≤tb) (sep : scratchBase+2136≤tb) (even : tb%2=0) (room : tb+2*(4272*r)≤MEMORY_BYTES) :
    Table τ r tb t := by
  intro i hi
  have lim : MEMORY_BYTES+16<2^64 := by decide
  exact (halfword_of_bytes s t _ (by omega) (by omega)
    (rec.outside _ (by omega) (Or.inr (by omega)) (Or.inr (by omega)))
    (rec.outside _ (by omega) (Or.inr (by omega)) (Or.inr (by omega)))).trans (read i hi)

theorem zero_dword (s : MachineState) (a q : Nat) (even : a%8=0) (fit : a+8≤MEMORY_BYTES)
    (qfit : q<MEMORY_BYTES) :
    byte (s.setMem (addr a) 0) q=if a≤q ∧ q<a+8 then 0 else byte s q := by
  have mem : MEMORY_BYTES<2^64 := by decide
  by_cases inWord : a≤q ∧ q<a+8
  · rw [if_pos inWord]
    let i:=q-a
    have atQ : q=a+i := by dsimp [i];omega
    unfold byte
    rw [atQ,byte_at _ a i even (by dsimp [i];omega) (by omega), MachineState.getMem_setMem_eq]
    simp [extractByte]
  · rw [if_neg inWord]
    unfold byte MachineState.getByte
    rw [MachineState.getMem_setMem_ne]
    intro e
    have numbers:=congrArg BitVec.toNat e
    rw [align_nat q (by omega),BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show a<2^64 by omega)] at numbers
    omega

theorem Writes.storeZeroWord {s t base n} (h : Writes s t base n (fun _=>0))
    (alg : (base+n)%8=0) (fit : base+n+8≤MEMORY_BYTES) :
    Writes s (t.setMem (addr (base+n)) 0) base (n+8) (fun _=>0) := by
  intro q valid
  rw [zero_dword t _ q alg fit valid,h q valid];split_ifs <;> first | rfl | omega

end CommitGolfCandidate.Layout2
