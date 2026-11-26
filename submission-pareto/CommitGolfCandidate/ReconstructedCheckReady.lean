import CommitGolfCandidate.ReconstructedCheckCopy
import CommitGolfCandidate.ReconstructedCheckLoaderImage
import CommitGolfCandidate.ReconstructedCheckLoaderBytes
import CommitGolfCandidate.ReconstructedCheckLaunch

namespace CommitGolfCandidate.Reconstruction.CheckReady
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CheckLoader CheckCopy CheckRecordABI CheckRecorded
open TwoPermutationPrototype.RV64
set_option maxRecDepth 18000
set_option maxHeartbeats 1400000
attribute [local irreducible] ArtifactEncoding.decode execute

private theorem ready (t : MachineState) (input : CheckInput) (valid : input.proof.length≤8355061248)
    (copy : Copy input) (post : CheckLaunchBody.Positive (body input) t input.positions.card input.proof.length) :
    Start t input := by
  have unchanged (a : Nat) (hi : a<68719473296) :
      t.getMem (W a)=(body input).getMem (W a) := by
    apply post.frame;left;change a%2^64<68719473296;omega
  have orig (a : Nat) (lo : 2098160≤a) (hi : a<68719473296) :
      t.getMem (W a)=(initial input).getMem (W a) := (unchanged a hi).trans (copy.frame a lo (by omega))
  have table (j : Nat) (h : j<126) : t.getMem (W (2097152+8*j))=tableWord j :=
    (unchanged _ (by omega)).trans ((copy.image j h).trans (image_word input valid j h))
  refine ⟨⟨?_,tables t table post.slots.mask,table,?_,?_,?_,post.slots.length,post.slots.countWord,
    post.slots.widths,post.slots.values,post.slots.indices,post.slots.marker,post.slots.ret⟩,post.registers,?_⟩
  · intro i h;exact (orig (10334769248+8*i) (by omega) (by omega)).trans (stream input i h)
  · intro i
    have h := i.isLt
    have lim := positions_card_bound input.positions
    exact (orig (8*(CheckEntry.indexBase+i.val)) (by unfold CheckEntry.indexBase;omega)
      (by unfold CheckEntry.indexBase;omega)).trans (index input i)
  · intro i j
    have h := i.isLt;have w := j.isLt;have lim := positions_card_bound input.positions
    exact (orig (8*(CheckEntry.valuesBase+32*i.val+j.val)) (by unfold CheckEntry.valuesBase;omega)
      (by unfold CheckEntry.valuesBase;omega)).trans (value input i j)
  · intro j;have h := j.isLt;exact (orig (4294971392+8*j.val) (by omega) (by omega)).trans (root input j)
  · intro k hk
    have byte := aligned_byte t (532480+k/8) (k%8) (by omega)
    have eq : 4259840+k=8*(532480+k/8)+k%8 := by omega
    have word := (orig (4259840+8*(k/8)) (by omega) (by omega)).trans (zero_flag input valid (k/8) (by omega))
    have loc : 8*(532480+k/8)+8*(k%8/8)=4259840+8*(k/8) := by omega
    rw [loc] at byte
    change t.getByte (W (4259840+k))=0
    rw [eq,byte,word];simp [extractByte]

theorem start (o : Oracle) (input : CheckInput) (pos : 0 < input.positions.card) (valid : input.proof.length≤8355061248) :
    if input.proof.length%8=0 ∧ CheckLaunchGate.minimum input.positions.card ≤ input.proof.length then
      ∃ t, Segment o 835 (initial input) t [] ∧ Start t input ∧ t.getReg .x5=W input.positions.card
    else ∃ n,n≤819 ∧ CheckLaunchGate.Reject o n (initial input) := by
  obtain ⟨prefixRun,copy⟩ := CheckCopy.start o input pos
  have h := CheckLaunch.run o (body input) input.positions.card input.proof.length (positions_card_bound input.positions)
    valid copy.pc copy.returnPC copy.stack copy.count copy.length
  split <;> rename_i cond
  · rw [ite_eq_left cond] at h
    obtain ⟨t,seg,post⟩ := h
    exact ⟨t,compose prefixRun seg,ready t input valid copy post,post.x5⟩
  · rw [ite_eq_right cond] at h
    obtain ⟨n,lim,bad⟩ := h
    exact ⟨767+n,by omega,CheckLaunchGate.extend prefixRun bad⟩

end CommitGolfCandidate.Reconstruction.CheckReady
