import CommitGolfCandidate.ReconstructedCheckCapCopy
import CommitGolfCandidate.ReconstructedCheckCapScanData
import CommitGolfCandidate.ReconstructedCheckEdge
import CommitGolfCandidate.ReconstructedCheckLayout
import CommitGolfCandidate.ReconstructedCheckGroupControl

namespace CommitGolfCandidate.Reconstruction.CheckParentHeap
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CheckParentGeometry Binding CheckGroupRadix
open TwoPermutationPrototype TwoPermutationPrototype.RV64
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000

def base (p : Nat) := 4194304+32*p
def word (p : Nat) := 524288+4*p
def g (p : Nat) : Geometry:=⟨68719473152,base (2*p),68719475416⟩
abbrev temp : Nat:=8589934427
abbrev stackWord : Nat:=8589934144

theorem location (p : Nat) : W (base p)=wordAddress (word p) := by
  change W (4194304+32*p)=W (8*(524288+4*p));congr 1;omega

theorem next (p : Nat) : base (p+1)=base p+32:=by unfold base;omega

theorem placed (p : Nat) (small : p<512) : Placed (g p) := by
  constructor
  · intro i;fin_cases i
    · change 0%8=0;omega
    · change 68719473152%8=0;omega
    · change (4194304+32*(2*p))%8=0;omega
    · change 68719475416%8=0;omega
  · intro i;fin_cases i
    · change 0+2098152≤2^36;omega
    · change 68719473152+144≤2^36;omega
    · change (4194304+32*(2*p))+64≤2^36;omega
    · change 68719475416+32≤2^36;omega
  · intro i j diff;fin_cases i <;> fin_cases j
    · exact False.elim (diff rfl)
    · change 0+2098152≤68719473152+0 ∨ 68719473152+144≤0+2097560;omega
    · change 0+2098152≤(4194304+32*(2*p))+0 ∨ (4194304+32*(2*p))+64≤0+2097560;omega
    · change 0+2098152≤68719475416+0 ∨ 68719475416+32≤0+2097560;omega
    · change 68719473152+144≤0+2097560 ∨ 0+2098152≤68719473152+0;omega
    · exact False.elim (diff rfl)
    · change 68719473152+144≤(4194304+32*(2*p))+0 ∨ (4194304+32*(2*p))+64≤68719473152+0;omega
    · change 68719473152+144≤68719475416+0 ∨ 68719475416+32≤68719473152+0;omega
    · change (4194304+32*(2*p))+64≤0+2097560 ∨ 0+2098152≤(4194304+32*(2*p))+0;omega
    · change (4194304+32*(2*p))+64≤68719473152+0 ∨ 68719473152+144≤(4194304+32*(2*p))+0;omega
    · exact False.elim (diff rfl)
    · change (4194304+32*(2*p))+64≤68719475416+0 ∨ 68719475416+32≤(4194304+32*(2*p))+0;omega
    · change 68719475416+32≤0+2097560 ∨ 0+2098152≤68719475416+0;omega
    · change 68719475416+32≤68719473152+0 ∨ 68719473152+144≤68719475416+0;omega
    · change 68719475416+32≤(4194304+32*(2*p))+0 ∨ (4194304+32*(2*p))+64≤68719475416+0;omega
    · exact False.elim (diff rfl)

def Frame (lo hi : Nat) (s t : MachineState) :=
  ∀ w,w<2^33 → (w<word lo ∨ word hi≤w) → (w<stackWord ∨ stackWord+18≤w) →
    (w<temp ∨ temp+4≤w) → t.getMem (wordAddress w)=s.getMem (wordAddress w)

theorem identity (lo hi : Nat) (s : MachineState) : Frame lo hi s s := fun _ _ _ _ _=>rfl

theorem same {s t : MachineState} (mem : t.mem=s.mem) (lo hi : Nat) : Frame lo hi s t:=fun w _ _ _ _=>congrFun mem _

theorem trans {a b c : Nat} {s t u : MachineState} (step : Frame a b s t) (more : Frame b c t u)
    (left : a≤b) (right : b≤c) : Frame a c s u := by
  intro w fit away st out
  have ab : word a≤word b:=by unfold word;omega
  have bc : word b≤word c:=by unfold word;omega
  exact (more w fit (by omega) st out).trans (step w fit (by omega) st out)

theorem values {s t : MachineState} (a b : Nat) (aa : a%8=0) (ab : b%8=0)
    (copy : ∀ i : Fin 4,t.getMem (W (a+8*i.val))=s.getMem (W (b+8*i.val))) :
    CommitParents.cell t a=CommitParents.cell s b := by
  rw [CommitParents.cell_words _ _ aa,CommitParents.cell_words _ _ ab]
  unfold CommitParents.atWord
  have z:=copy 0;have one:=copy 1;have two:=copy 2;have th:=copy 3
  change t.getMem (W (a+16))=s.getMem (W (b+16)) at two
  change t.getMem (W (a+24))=s.getMem (W (b+24)) at th
  simp only [Fin.val_zero,Fin.val_one,Nat.mul_zero,Nat.add_zero,Nat.mul_one] at z one
  rw [z,one,two,th]

theorem words (p : Nat) (i : Fin 4) : W (base p+8*i.val)=wordAddress (word p+i.val) := by
  change W (4194304+32*p+8*i.val)=W (8*(524288+4*p+i.val));congr 1;omega

theorem cell {s t : MachineState} {lo hi : Nat} (fr : Frame lo hi s t) (p : Nat) (small : p<1024) (outside : p<lo ∨ hi≤p) :
    CommitParents.cell t (base p)=CommitParents.cell s (base p) := by
  apply values _ _ (by unfold base;omega) (by unfold base;omega)
  intro i
  have f:=i.isLt;rw [words]
  apply fr <;> simp only [word,stackWord,temp] <;> omega

theorem constants {s t : MachineState} {lo hi : Nat} (fr : Frame lo hi s t) (ro : CheckParentGeometry.constants s) :
    CheckParentGeometry.constants t := by
  intro a v aligned key
  have lim : 2097560≤a ∧ a<2098152:=by unfold CheckParentRun.ro at key;split_ifs at key <;> first | contradiction | omega
  have atWord : W a=wordAddress (a/8):=by change W a=W (8*(a/8));congr 1;omega
  change t.getMem (W a)=v
  rw [atWord]
  refine (fr (a/8) (by omega) (.inl (by unfold word;omega)) (.inl (by unfold stackWord;omega)) (.inl (by unfold temp;omega))).trans ?_
  rw [←atWord];exact ro a v aligned key

theorem flag {s t : MachineState} {lo hi : Nat} (fr : Frame lo hi s t) (topBound : hi≤512) (p : Nat) (small : p<512) :
    t.getByte (CheckCapScanData.flag p)=s.getByte (CheckCapScanData.flag p) := by
  have val : alignToDword (CheckCapScanData.flag p)=wordAddress ((4259840+p)/8):=by
    unfold CheckCapScanData.flag;rw [OpeningCursor.aligned];rfl
  unfold MachineState.getByte;rw [val]
  rw [fr _ (by omega) (.inr (by unfold word;omega)) (.inl (by unfold stackWord;omega)) (.inl (by unfold temp;omega))]

end CommitGolfCandidate.Reconstruction.CheckParentHeap

