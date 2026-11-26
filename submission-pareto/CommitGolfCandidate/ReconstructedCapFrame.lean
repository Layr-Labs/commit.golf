import CommitGolfCandidate.ReconstructedCapEmitNode
import CommitGolfCandidate.ReconstructedCapScanMemory
import CommitGolfCandidate.ReconstructedCapControlMemory

namespace CommitGolfCandidate.Reconstruction.CapFrame
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel OpeningPut OpeningCursor
open TwoPermutationPrototype.RV64
open HonestRanges (Contains)
open CapEmitNode (outside)
set_option maxRecDepth 16000
set_option maxHeartbeats 1500000

abbrev state (s : MachineState) : Model := ⟨s.getReg,memoryView s⟩
theorem fits (s : MachineState) : Fits s (state s) := ⟨fun _ => rfl,fun _ _ => rfl⟩

def clear (q : Nat) := (q<532480 ∨ 532607<q) ∧ (q<8589934272 ∨ 8589934527<q)
def same (s t : MachineState) := ∀ q, q<2^33 → clear q → outside q → memoryView t q=memoryView s q

theorem stored (s t : MachineState) (whole : t.mem=s.mem) : same s t :=
  fun j _ _ _ => CapScanMemory.read_congr whole j

theorem emitted (s t : MachineState) (m out : Model) (a : Fits s m) (b : Fits t out) (c d id j : Nat)
    (valid : CapEmitNode.Result m out c d id j) (room : (c+192)/64<capacity) :
    ∀ q, q<2^33 → outside q → memoryView t q=memoryView s q := by
  intro q bound loc
  exact (b.memory q bound).trans ((congrFun valid.data q).trans
    ((CapEmitNode.keep _ _ _ _ room q loc).trans (a.memory q bound).symm))

private theorem align_away (q : Nat) (bound : q<2^33) (x : Word)
    (flag : Contains HonestCapSpan.flags x) (span : q<532480 ∨ 532607<q) :
    wordAddress q≠alignToDword x := by
  intro bad
  have eq := congrArg BitVec.toNat bad
  have around := HonestMemoryRanges.aligned_window x
  change 4259840≤x.toNat ∧ x.toNat≤4260863 at flag
  change (8*q)%2^64=(alignToDword x).toNat at eq
  omega

theorem scan (s t : MachineState) (x : Word) (flag : Contains HonestCapSpan.flags x) (p : Fin 257)
    (k : Nat) (l r : Bool) (effect : t.mem=(CapScanMemory.scanned s x p.val k l r).mem) :
    ∀ q, q<2^33 → clear q → memoryView t q=memoryView s q := by
  intro q bound span
  let m := CapScanMemory.marked s x (l||r)
  have mark : memoryView m q=memoryView s q := by
    cases h : l||r with
    | false => simp only [m,CapScanMemory.marked,h,Bool.false_eq_true,ite_false]
    | true =>
      simp only [m,CapScanMemory.marked,h,ite_true]
      exact MachineState.getMem_setMem_ne (align_away q bound x flag span.1)
  have z := CapScanMemory.read_congr effect q
  by_cases eq : l=r
  · simpa only [CapScanMemory.scanned,ite_eq_left eq] using z.trans (by
      change memoryView (if l=r then m else _) q=memoryView s q
      rwa [ite_eq_left eq])
  · simp only [CapScanMemory.scanned,ite_eq_right eq] at z
    have num := p.isLt
    have apart : q≠CapSlots.cell p.val := by change q≠8589934272+p.val/2;have v := span.2;omega
    exact z.trans ((CapSlots.store_id m ⟨p.val,by omega⟩ _ q bound).trans ((CapSlots.unchanged _ _ _ _ apart).trans mark))

theorem transfer (s t : MachineState) (trap : CommitStorage.Trapdoor) (ps : Positions) (src : CapEntry.Source s trap ps)
    (stack : t.getReg .x2=s.getReg .x2) (frame : t.getReg .x8=s.getReg .x8) (stable : same s t) :
    CapEntry.Source t trap ps := by
  have word (n : Nat) (aligned : n%8=0) (size : n/8<2^33) (one : clear (n/8)) (two : outside (n/8)) :
      t.getMem (W n)=s.getMem (W n) := by
    have h := stable (n/8) size one two
    change t.getMem (W (8*(n/8)))=s.getMem (W (8*(n/8))) at h
    rwa [show 8*(n/8)=n by omega] at h
  refine ⟨stack.trans src.stack,frame.trans src.frame,?_,?_,?_,?_,?_,?_⟩
  · exact (word 68719476328 (by decide) (by decide) (by unfold clear;decide) (by unfold outside;decide)).trans src.saved
  · exact (word 68719474112 (by decide) (by decide) (by unfold clear;decide) (by unfold outside;decide)).trans src.shiftMask
  · exact (word 68719474104 (by decide) (by decide) (by unfold clear;decide) (by unfold outside;decide)).trans src.headerMask
  · intro d
    have bound := d.isLt
    exact (word _ (by omega) (by omega) (by unfold clear;omega) (by unfold outside base;omega)).trans (src.lows d)
  · intro d
    have bound := d.isLt
    exact (word _ (by omega) (by omega) (by unfold clear;omega) (by unfold outside base;omega)).trans (src.widths d)
  · intro d j k pos depth cell offset
    have cap : 2^(d+1)≤2^10 := Nat.pow_le_pow_right (by decide) (by omega)
    have id : j<1024 := cell.2.2.trans_le cap
    have addr : 4294971424≤CommitParents.addr d j+8*k ∧ CommitParents.addr d j+8*k≤4295004480 := by unfold CommitParents.addr;omega
    exact (word _ (by unfold CommitParents.addr;omega) (by omega) (by unfold clear;omega) (by unfold outside base;omega)).trans
      (src.tree d j k pos depth cell offset)

end CommitGolfCandidate.Reconstruction.CapFrame
