import CommitGolfCandidate.ReconstructedCheckInitLower

namespace CommitGolfCandidate.Reconstruction.CheckRecordFrame
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CheckLayout CheckRecordABI
open TwoPermutationPrototype.RV64
set_option maxRecDepth 17000
set_option maxHeartbeats 1600000
abbrev W:=BitVec.ofNat 64

def fpWord:=8589934466

def Safe (a : Nat) := (a<68719473152 ∨ 68719473296≤a) ∧
  a≠68719473352 ∧ (a<68719473368 ∨ 68719475616≤a)

def Frame (s t : MachineState) := ∀ a,a<2^36→a%8=0→Safe a→t.getMem (W a)=s.getMem (W a)

theorem trans {s t u : MachineState} (h : Frame s t) (k : Frame t u) : Frame s u :=
  fun a x y z=>(k a x y z).trans (h a x y z)

theorem word (a : Nat) (align : a%8=0) : wordAddress (a/8)=W a := by unfold wordAddress;congr 1;omega

theorem fromHeader {s t : MachineState}
    (h : ∀ w,w<2^33→w≠fpWord-297→(w<fpWord-295 ∨ fpWord-14≤w)→t.getMem (wordAddress w)=s.getMem (wordAddress w)) :
    Frame s t := by
  intro a small align safe;rw [←word a align]
  obtain ⟨_,away,ends⟩:=safe;apply h <;> (try simp only [fpWord]) <;> omega

theorem fromWords {s t : MachineState} (m : ∀ w,w<2^33→t.getMem (wordAddress w)=s.getMem (wordAddress w)) : Frame s t := by
  intro a small align _;rw [←word a align];apply m;omega

theorem fromWalk {s t : MachineState} (h : Untouched s t) : Frame s t := by
  intro a small align safe
  obtain ⟨stack,_,body⟩:=safe
  apply readFrame s t h a align small;apply outside <;> (try simp only [geo]) <;> omega

theorem persistent {s t : MachineState} {input : CheckInput} (h : Frame s t) (p : Persistent s input) : Persistent t input := by
  have card : input.positions.card≤2^24:=by simpa only [Fintype.card_fin,LENGTH,LOG_LENGTH] using Finset.card_le_univ input.positions
  have below (a : Nat) (small : a<68719473152) (align : a%8=0) :=
    h a (by omega) align (by simp only [Safe];omega)
  have same (w : Nat) (lim : w<8589934144) : t.getMem (wordAddress w)=s.getMem (wordAddress w) :=
    below (8*w) (by omega) (by omega)
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro j hj;exact (below _ (by unfold proofBase;omega) (by unfold proofBase;omega)).trans (p.stream j hj)
  · refine ⟨?_,?_,?_,?_⟩
    · intro i;have v:=i.isLt;exact (below _ (by unfold lowCell;omega) (by unfold lowCell;omega)).trans (p.tables.lows i)
    · intro i;have v:=i.isLt;exact (same _ (by unfold divCell;omega)).trans (p.tables.bases i)
    · exact (h _ (by decide) (by decide) (by unfold Safe maskCell;omega)).trans p.tables.mask
    · intro a v aligned known
      have lim : a<2098152:=by unfold CheckParentRun.ro at known;split_ifs at known <;> first | contradiction | omega
      exact (below _ (by omega) aligned).trans (p.tables.ro a v aligned known)
  · intro j hj;exact (below _ (by omega) (by omega)).trans (p.imageData j hj)
  · intro i;have hi:=i.isLt;exact (same _ (by unfold CheckEntry.indexBase;omega)).trans (p.indices i)
  · intro i j;have hi:=i.isLt;have hj:=j.isLt;exact (same _ (by unfold CheckEntry.valuesBase;omega)).trans (p.values i j)
  · intro j;have hj:=j.isLt;exact (below _ (by omega) (by omega)).trans (p.commitment j)
  all_goals first | exact (h _ (by decide) (by decide) (by unfold Safe CheckLayout.fp;omega)).trans p.length
                  | exact (h _ (by decide) (by decide) (by unfold Safe CheckLayout.fp;omega)).trans p.count
                  | exact (h _ (by decide) (by decide) (by unfold Safe CheckLayout.fp;omega)).trans p.widths
                  | exact (h _ (by decide) (by decide) (by unfold Safe CheckLayout.fp;omega)).trans p.valuesPtr
                  | exact (h _ (by decide) (by decide) (by unfold Safe CheckLayout.fp;omega)).trans p.indexPtr
                  | exact (h _ (by decide) (by decide) (by unfold Safe CheckLayout.fp;omega)).trans p.marker
                  | exact (h _ (by decide) (by decide) (by unfold Safe CheckLayout.fp;omega)).trans p.returnPC

end CommitGolfCandidate.Reconstruction.CheckRecordFrame
