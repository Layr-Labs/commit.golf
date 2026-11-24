import CommitGolfCandidate.Layout2Apply
import CommitGolfCandidate.Layout2CapPhysical
import CommitGolfCandidate.Layout2CapCodec
import CommitGolfCandidate.Layout2CapControl
import CommitGolfCandidate.Layout2Delivered
import CommitGolfCandidate.Layout2Clear
namespace CommitGolfCandidate.Layout2.Cap
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open CommitGolfCandidate.Layout2.Quartet (checkImage)

def OutsideCap (q : Nat) := q<scratchBase ∨ scratchBase+952≤q
def Output (s t : MachineState) (base n : Nat) (f : Nat→Byte) :=
  ∀ q,q<MEMORY_BYTES → OutsideCap q →
    byte t q=if base≤q ∧ q<base+n then f (q-base) else byte s q

theorem Output.zero (s p f) : Output s s p 0 f := by intro q _ _;simp
theorem Output.mem {s t u p n f} (a : Output s t p n f) (same : u.mem=t.mem) : Output s u p n f := by
  intro q h o;simpa only [byte,MachineState.getByte,MachineState.getMem,same] using a q h o
theorem Output.records {s t p n f} (a : Output s t p n f) : Records s t p n f := by
  intro q h o;exact a q h (by unfold OutsideCap;unfold Outside at o;omega)
theorem Output.append {s t u p n m f g} (prior : Output s t p n f) (next : Output t u (p+n) m g)
    (same : ∀ j,j<m → g j=f (n+j)) : Output s u p (n+m) f := by
  intro q fit out
  rw [next q fit out,prior q fit out]
  by_cases hit : p+n≤q ∧ q<p+n+m
  · rw [if_pos hit,if_pos (by omega),same _ (by omega),show n+(q-(p+n))=q-p by omega]
  · rw [if_neg hit];by_cases was : p≤q ∧ q<p+n
    · simp [was,show p≤q ∧ q<p+(n+m) by omega]
    · simp [was,show ¬(p≤q ∧ q<p+(n+m)) by omega]

theorem finish_scratch {s t u p n f} (prior : Output s t p n f) (clean : Writes t u scratchBase 952 (fun _=>0))
    (below : scratchBase+952≤p) (zeroed : ∀ j,j<952 → byte s (scratchBase+j)=0) : Writes s u p n f := by
  intro q fit
  by_cases outside : OutsideCap q
  · rw [clean.outside _ fit outside];exact prior q fit outside
  · have inside : scratchBase≤q ∧ q<scratchBase+952 := by unfold OutsideCap at outside;omega
    have z:=zeroed (q-scratchBase) (by omega)
    rw [show scratchBase+(q-scratchBase)=q by omega] at z
    simp only [clean q fit,if_pos inside,if_neg (by omega : ¬(p≤q ∧ q<p+n)),z]

def result (s : MachineState) (base n : Nat) := atByte dec n (fun j=>byte s (base+j))

theorem block_run {s u base n g m ret}
    (data : AtData s) (lo : 1≤m) (hi : m≤32) (selected : m=if g<n/952 then 32 else tag (n%952))
    (separate : scratchBase+2136≤base) (room : base+n≤tableBase) (inside : 952*g+size m≤n)
    (head : Output s u base (952*g) (result s base n))
    (pcU : u.pc=pc 759) (dst : u.getReg .x8=addr (base+952*g))
    (bytes : u.getReg .x18=addr (size m)) (tbl : u.getReg .x19=addr (tableBase+offset m))
    (scratch : u.getReg .x10=addr scratchBase) (eight : u.getReg .x21=8)
    (link : (u.getReg .x31 &&& ~~~1#64)=pc ret) :
    ∃ v, Runs checkImage u v (5+106*size m) (5+106*size m) ∧ v.pc=pc ret ∧
      Output s v base (952*g+size m) (result s base n) ∧ Kept callScratch u v := by
  have lim:=limits ⟨m,by omega⟩
  change size m≤952 ∧ offset m%2=0 ∧ offset m+16*size m≤337472 at lim
  have pos : 0<size m := by unfold size;omega
  have cfg : Span dec m (base+952*g) (tableBase+offset m) (size m) := by
    refine ⟨pos,by omega,by omega,by unfold tableBase;omega,by unfold tableBase MEMORY_BYTES;omega,?_⟩
    intro i h;have idx:=(checked_entry m i lo hi h).1;exact ⟨idx,by omega⟩
  have tab:=(data.records head.records (by omega)).bank m lo hi
  obtain ⟨v,ran,atEnd,⟨tmp,cp,emit⟩,kept⟩:=apply_span (I:=checkImage) concrete_program cfg u ret pcU dst bytes tbl scratch eight link tab
  refine ⟨v,ran,atEnd,head.append (g:=gather dec m (fun z=>byte u (base+952*g+z))) ?_ ?_,kept⟩
  · intro q fit out;rw [emit q fit,cp.outside q fit (by unfold OutsideCap at out;omega)]
  · intro j hj
    unfold result
    rw [at_chunk _ _ _ _ _ (by omega),←selected]
    apply BitVec.eq_of_getLsbD_eq
    intro b hb
    rw [gather_bit _ _ _ _ _ hb,gather_bit _ _ _ _ _ hb]
    have idx:=(checked_entry m (8*j+b) lo hi (by omega)).1
    have whereAt : base+952*g+dec m (8*j+b)/8<MEMORY_BYTES := by unfold tableBase MEMORY_BYTES at *;omega
    rw [head _ whereAt (Or.inr (by omega)),if_neg (by omega : ¬(base≤base+952*g+dec m (8*j+b)/8 ∧ base+952*g+dec m (8*j+b)/8<base+952*g)),Nat.add_assoc]

end CommitGolfCandidate.Layout2.Cap
