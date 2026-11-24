import CommitGolfCandidate.Layout2CapChecked
import CommitGolfCandidate.Layout2Table
import CommitGolfCandidate.Layout2Regions

namespace CommitGolfCandidate.Layout2.Cap
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Layout2Helpers TwoPermutationPrototype.RV64
set_option maxRecDepth 12000
set_option maxHeartbeats 1600000

def AtData (s : MachineState) := ∀ k,k<337472 → byte s (tableBase+k)=BitVec.ofNat 8 (pget K1Artifact.checkData k)
def entryBase (m : Nat) := tableBase+85440+8*m
def entryWord (m : Nat) := addr (size m+2^32*offset m)

private theorem directory_bytes : ∀ j : Fin 32, ∀ b : Fin 8,
    extractByte (entryWord j.val) b.val = BitVec.ofNat 8 (pget K1Artifact.checkData (85440+8*j.val+b.val)) := by
  decide +kernel
private theorem dir_low : ∀ j : Fin 32, extractHalfword (entryWord j.val) 0=BitVec.ofNat 16 (size j.val) := by decide +kernel
private theorem dir_high : ∀ j : Fin 32, extractWord32 (entryWord j.val) 1=BitVec.ofNat 32 (offset j.val) := by decide +kernel

attribute [local irreducible] ArtifactEncoding.decode K1Artifact.checkData

theorem initial_data (input : CheckInput) (fits : input.proof.length≤8959041024) :
    AtData (candidate.initialState .check input) := by
  intro k inside
  have c0 : input.positions.card≤LENGTH := by simpa [Index] using Finset.card_le_univ input.positions
  have c : input.positions.card≤16777216 := c0
  let a:=tableBase+k
  have root : ¬(candidate.layout.commitment≤a ∧ a<candidate.layout.commitment+(DIGEST_BITS+7)/8) := by
    change ¬(4294971392≤68719139264+k ∧ 68719139264+k<4294971424);omega
  have ix : ¬(candidate.layout.indices≤a ∧ a<candidate.layout.indices+8*input.positions.card) := by
    change ¬(9395245088≤68719139264+k ∧ 68719139264+k<9395245088+8*input.positions.card);omega
  have vs : ¬(candidate.layout.values≤a ∧ a<candidate.layout.values+(LEAF_SIZE/8)*input.positions.card) := by
    change ¬(9529462880≤68719139264+k ∧ 68719139264+k<9529462880+256*input.positions.card);omega
  have pr : ¬(candidate.layout.proof≤a ∧ a<candidate.layout.proof+input.proof.length) := by
    change ¬(13824430176≤68719139264+k ∧ 68719139264+k<13824430176+input.proof.length);omega
  refine (initial_input_byte candidate .check input a (by dsimp [a,tableBase];omega)).trans ?_
  have get:=raw_data_read k inside
  simpa [inputByte,Submission.inputBuffers,fixedBuffer,positionsBuffer,valuesBuffer,root,ix,vs,pr,data_base,a] using get

theorem AtData.mem {s t} (data : AtData s) (same : t.mem=s.mem) : AtData t := by
  intro k h;simpa only [byte,MachineState.getByte,MachineState.getMem,same] using data k h

theorem AtData.records {s t base n f} (data : AtData s) (rec : Records s t base n f) (room : base+n≤tableBase) : AtData t := by
  intro k h
  exact (rec.outside _ (by unfold tableBase MEMORY_BYTES;omega) (Or.inr (by unfold scratchBase tableBase;omega))
    (Or.inr (by omega))).trans (data k h)

theorem AtData.directory {s} (data : AtData s) (m : Nat) (hi : m<32) :
    s.getHalfword (addr (entryBase m))=BitVec.ofNat 16 (size m) ∧
    s.getWord32 (addr (entryBase m+4))=BitVec.ofNat 32 (offset m) := by
  let a:=entryBase m
  have fit : a+8≤2^64 := by dsimp [a,entryBase,tableBase];omega
  have alg : a%8=0 := by dsimp [a,entryBase,tableBase];omega
  have wd : s.getMem (addr a)=entryWord m := by
    apply eq_of_forall_extractByte
    intro j hj
    have b:=data (85440+8*m+j) (by omega)
    have read:=byte_at s a j alg hj fit
    rw [show a+j=tableBase+(85440+8*m+j) by dsimp [a,entryBase];omega] at read
    exact read.symm.trans (b.trans (directory_bytes ⟨m,hi⟩ ⟨j,hj⟩).symm)
  change s.getHalfword (addr a)=_ ∧ s.getWord32 (addr (a+4))=_
  constructor
  · unfold MachineState.getHalfword
    rw [align_eq _ (by omega),offset_nat _ (by omega),alg,Nat.sub_zero,wd]
    exact dir_low ⟨m,hi⟩
  · unfold MachineState.getWord32
    rw [align_eq _ (by omega),offset_nat _ (by omega),show (a+4)%8=4 by omega,show a+4-4=a by omega,wd]
    exact dir_high ⟨m,hi⟩

theorem AtData.bank {s} (data : AtData s) (m : Nat) (lo : 1≤m) (hi : m≤32) :
    SpanTable dec m (tableBase+offset m) (size m) s := by
  intro j inside
  have limit:=limits ⟨m,by omega⟩
  change size m≤952 ∧ offset m%2=0 ∧ offset m+16*size m≤337472 at limit
  let k:=offset m+2*j
  let a:=tableBase+k
  have kfit : k+1<337472 := by dsimp [k];omega
  have even : a%2=0 := by dsimp [a,tableBase,k];omega
  have read:=halfword_bytes s a even (by dsimp [a,tableBase];omega)
  have e:=(checked_entry m j lo hi inside).2.2.2.2
  let x:=pget K1Artifact.checkData k
  let y:=pget K1Artifact.checkData (k+1)
  have byteFit (u : Nat) (fit : u<337472) : pget K1Artifact.checkData u<256 := by
    rw [←pget_get K1Artifact.checkData ⟨u,fit⟩];exact BitVec.isLt _
  have xf : x<256 := byteFit k (by omega)
  have yf : y<256 := byteFit (k+1) kfit
  change x+256*y=dec m j at e
  have sm : dec m j<65536 := by omega
  have h0:=data k (by omega)
  have h1:=data (k+1) kfit
  rw [←Nat.add_assoc] at h1
  rw [show tableBase+offset m+2*j=a by dsimp [a,k];omega]
  apply half_ext
  · rw [read.1];apply h0.trans;apply BitVec.eq_of_toNat_eq
    change (BitVec.ofNat 8 x).toNat=_
    simp only [BitVec.toNat_ofNat,BitVec.extractLsb'_toNat,Nat.mod_eq_of_lt sm,Nat.shiftRight_zero]
    omega
  · rw [read.2];apply h1.trans;apply BitVec.eq_of_toNat_eq
    change (BitVec.ofNat 8 y).toNat=_
    simp only [BitVec.toNat_ofNat,BitVec.extractLsb'_toNat,Nat.mod_eq_of_lt sm,Nat.shiftRight_eq_div_pow]
    omega

end CommitGolfCandidate.Layout2.Cap
