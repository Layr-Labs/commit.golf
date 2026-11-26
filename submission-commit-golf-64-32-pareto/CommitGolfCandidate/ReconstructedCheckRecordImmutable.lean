import CommitGolfCandidate.ReconstructedCheckRecordFrame

namespace CommitGolfCandidate.Reconstruction.CheckRecordImmutable
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CheckLayout CheckRecordABI
open TwoPermutationPrototype.RV64
set_option maxRecDepth 12000
set_option maxHeartbeats 1250000
abbrev W:=BitVec.ofNat 64

def Outside (a : Nat) := a<4194304 ∨ 4260864≤a
def Fixed (s t : MachineState) := ∀ a,a<2^36→a%8=0→Outside a→t.getMem (W a)=s.getMem (W a)

theorem carry {s t : MachineState} {input : CheckInput} (h : Fixed s t) (p : Persistent s input) : Persistent t input := by
  have card : input.positions.card≤2^24:=by simpa only [Fintype.card_fin,LENGTH,LOG_LENGTH] using Finset.card_le_univ input.positions
  have below (a : Nat) (small : a<68719473152) (align : a%8=0) (gap : Outside a) :=
    h a (by omega) align gap
  have same (w : Nat) (lim : w<8589934144) (gap : Outside (8*w)) : t.getMem (wordAddress w)=s.getMem (wordAddress w) :=
    below (8*w) (by omega) (by omega) gap
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro j hj;exact (below _ (by unfold proofBase;omega) (by unfold proofBase;omega ) (by unfold Outside proofBase;omega)).trans (p.stream j hj)
  · refine ⟨?_,?_,?_,?_⟩
    · intro i;have v:=i.isLt;exact (below _ (by unfold lowCell;omega) (by unfold lowCell;omega ) (by unfold Outside lowCell;omega)).trans (p.tables.lows i)
    · intro i;have v:=i.isLt;exact (same _ (by unfold divCell;omega ) (by unfold Outside divCell;omega)).trans (p.tables.bases i)
    · exact (h _ (by decide) (by decide) (by unfold Outside maskCell;omega)).trans p.tables.mask
    · intro a v aligned known
      have lim : a<2098152:=by unfold CheckParentRun.ro at known;split_ifs at known <;> first | contradiction | omega
      exact (below _ (by omega) aligned (by unfold Outside;omega)).trans (p.tables.ro a v aligned known)
  · intro j hj;exact (below _ (by omega) (by omega ) (by unfold Outside;omega)).trans (p.imageData j hj)
  · intro i;have hi:=i.isLt;exact (same _ (by unfold CheckEntry.indexBase;omega ) (by unfold Outside CheckEntry.indexBase;omega)).trans (p.indices i)
  · intro i j;have hi:=i.isLt;have hj:=j.isLt;exact (same _ (by unfold CheckEntry.valuesBase;omega ) (by unfold Outside CheckEntry.valuesBase;omega)).trans (p.values i j)
  · intro j;have hj:=j.isLt;exact (below _ (by omega) (by omega ) (by unfold Outside;omega)).trans (p.commitment j)
  all_goals first | exact (h _ (by decide) (by decide) (by unfold Outside CheckLayout.fp;omega)).trans p.length
                  | exact (h _ (by decide) (by decide) (by unfold Outside CheckLayout.fp;omega)).trans p.count
                  | exact (h _ (by decide) (by decide) (by unfold Outside CheckLayout.fp;omega)).trans p.widths
                  | exact (h _ (by decide) (by decide) (by unfold Outside CheckLayout.fp;omega)).trans p.valuesPtr
                  | exact (h _ (by decide) (by decide) (by unfold Outside CheckLayout.fp;omega)).trans p.indexPtr
                  | exact (h _ (by decide) (by decide) (by unfold Outside CheckLayout.fp;omega)).trans p.marker
                  | exact (h _ (by decide) (by decide) (by unfold Outside CheckLayout.fp;omega)).trans p.returnPC

end CommitGolfCandidate.Reconstruction.CheckRecordImmutable
