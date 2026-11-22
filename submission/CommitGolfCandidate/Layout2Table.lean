import CommitGolfCandidate.Layout2Invariant
import CommitGolfCandidate.Layout2TableData
import CommitGolfCandidate.TwoPermutationCheckLoader

namespace CommitGolfCandidate.Layout2
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open CommitGolfCandidate.Layout2Helpers (pget pget_get halfword_bytes half_ext)
set_option maxRecDepth 32000
set_option maxHeartbeats 1500000
set_option exponentiation.threshold 2048
theorem high_input (τ : Tables) (physical : ∀ k, k<85440 → pget K1Artifact.checkData k=tableByte τ k)
    (input : CheckInput) (fits : input.proof.length≤8959041024) (k : Nat) (inside : k<85440) :
    byte (candidate.initialState .check input) (tableBase+k)=BitVec.ofNat 8 (tableByte τ k) := by
  have c0 : input.positions.card≤LENGTH := by simpa [Index] using Finset.card_le_univ input.positions
  have c : input.positions.card≤16777216 := c0
  refine (initial_input_byte candidate .check input (tableBase+k) (by unfold tableBase;omega)).trans ?_
  let a:=tableBase+k
  have root : ¬(candidate.layout.commitment≤a ∧ a<candidate.layout.commitment+(DIGEST_BITS+7)/8) := by
    change ¬(4294971392≤68719139264+k ∧ 68719139264+k<4294971424);omega
  have ix : ¬(candidate.layout.indices≤a ∧ a<candidate.layout.indices+8*input.positions.card) := by
    change ¬(9395245088≤68719139264+k ∧ 68719139264+k<9395245088+8*input.positions.card);omega
  have vs : ¬(candidate.layout.values≤a ∧ a<candidate.layout.values+(LEAF_SIZE/8)*input.positions.card) := by
    change ¬(9529462880≤68719139264+k ∧ 68719139264+k<9529462880+256*input.positions.card);omega
  have pr : ¬(candidate.layout.proof≤a ∧ a<candidate.layout.proof+input.proof.length) := by
    change ¬(13824430176≤68719139264+k ∧ 68719139264+k<13824430176+input.proof.length);omega
  change inputByte candidate .check input a=_
  simpa [inputByte,Submission.inputBuffers,fixedBuffer,positionsBuffer,valuesBuffer,root,ix,vs,pr,data_base,a] using data_read physical k inside

theorem initial_tables (τ : Tables) (wf : WellFormed τ)
    (physical : ∀ k, k<85440 → pget K1Artifact.checkData k=tableByte τ k)
    (input : CheckInput) (fits : input.proof.length≤8959041024) :
    TablesAt τ (candidate.initialState .check input) := by
  intro r lo hi i bound
  let a:=tableBase+tableOffset r+2*i
  let k:=tableOffset r+2*i
  let z:=τ r i
  have zr : z<65536 := by have:=wf r lo hi i bound;omega
  have ends : k+1<85440 := by unfold k;interval_cases r <;> simp [tableOffset] <;> omega
  have even : a%2=0 := by unfold a;interval_cases r <;> simp [tableOffset,tableBase] <;> omega
  have bank (b : Nat) (hb : b<2) : multiplicity (k+b)=r := by
    unfold k multiplicity
    interval_cases r <;> norm_num [tableOffset] <;> split_ifs <;> omega
  have ek : k%2=0 := by unfold k;interval_cases r <;> norm_num [tableOffset] <;> omega
  have bank0 : multiplicity k=r := by simpa using bank 0 (by decide)
  have e0 : tableByte τ k=z%256 := by
    simp only [tableByte,bank0,ek,ite_true,show (k-tableOffset r)/2=i by unfold k;omega,z]
  have e1 : tableByte τ (k+1)=z/256%256 := by
    simp only [tableByte,bank 1 (by decide),if_neg (show ¬(k+1)%2=0 by omega),show (k+1-tableOffset r)/2=i by unfold k;omega,z]
  have h0:=high_input τ physical input fits k (by omega)
  have h1:=high_input τ physical input fits (k+1) ends
  rw [e0] at h0;rw [e1] at h1
  have fit : a+16≤2^64 := by change tableBase+tableOffset r+2*i+16≤_;unfold k at ends;unfold tableBase;omega
  have lanes:=halfword_bytes (candidate.initialState .check input) a even fit
  change (candidate.initialState .check input).getHalfword (addr a)=BitVec.ofNat 16 z
  apply half_ext
  · rw [lanes.1]
    change byte _ (tableBase+(tableOffset r+2*i))=_ at h0
    rw [show a=tableBase+(tableOffset r+2*i) by unfold a;omega]
    apply h0.trans;apply BitVec.eq_of_toNat_eq
    simp [BitVec.extractLsb'_toNat,Nat.mod_eq_of_lt zr]
  · rw [lanes.2]
    change byte _ (tableBase+(tableOffset r+2*i+1))=_ at h1
    rw [show a+1=tableBase+(tableOffset r+2*i+1) by unfold a;omega]
    apply h1.trans;apply BitVec.eq_of_toNat_eq
    simp [BitVec.extractLsb'_toNat,Nat.mod_eq_of_lt zr,Nat.shiftRight_eq_div_pow]

end CommitGolfCandidate.Layout2
