import CommitGolfCandidate.RungAPrefix
import CommitGolfCandidate.RungACache
namespace CommitGolfCandidate.RungA
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 R4 Late
set_option Elab.async false
set_option maxHeartbeats 1400000
set_option maxRecDepth 12000

def Early (s : MachineState) := ∀ h,h<4 → ∀ i,i<levelCount h → readBuffer s (nodeAddress h i) 32=0
def Unused (a : Nat) := nodeAddress LOG_LENGTH 0+32≤a ∧ a<tdAddress+3355443200 ∧
  (a<rowBase ∨ rowBase+184*(LENGTH/2)≤a)
structure Ground (o : Oracle) (m : Message) (r : Tape) (s : MachineState) : Prop where
  rows : ∀ i : Index, readBuffer s (finalRowAddress i.val) 96=finalRow o m r i
  salts : ∀ i : Index, readBuffer s (sharedSaltAddr i.val) 24=pairSalts r i
  omitted : Early s
  gaps : Gaps s
  tail : ∀ a,Unused a → readBuffer s a 1=0

theorem earlyRange (h i : Nat) (lo : h<4) (valid : i<levelCount h) :
    tdAddress≤nodeAddress h i ∧ nodeAddress h i+32≤5301604576 := by
  have e:=nodeEnd h i (by omega) valid
  have m:=levelOffset_mono (a:=h+1) (b:=4) (by omega)
  change levelOffset (h+1)≤1006633152 at m
  exact ⟨by dsimp [nodeAddress,tdAddress];omega,by omega⟩

theorem beginGround {o m r s} (data : Inputs o m r s) : Ground o m r s := by
  refine ⟨data.rows,data.salts,?_,?_,?_⟩
  · intro h lh i hi
    obtain ⟨b,e⟩:=earlyRange h i lh hi
    apply readBuffer_zero_of_bytes;intro j hj
    apply data.fresh _ (by dsimp [MEMORY_BYTES];omega)
    right;change 4294971424≤_ at b;exact ⟨by dsimp [C_TD];omega,Or.inl (by dsimp [C_ROW];omega)⟩
  · intro h p k pad
    have end_:=padValid _ _ _ pad
    have lo : C_TD≤unusedSlotAddr h p k:=by dsimp [unusedSlotAddr,rowAddress,C_TD];omega
    change unusedSlotAddr h p k+32≤5905584160 at end_
    apply readBuffer_zero_of_bytes;intro j hj
    exact data.fresh _ (by dsimp [MEMORY_BYTES];omega) (Or.inr ⟨by omega,Or.inl (by unfold C_ROW;omega)⟩)
  · intro a range
    change 5368714368≤a ∧ a<7650414624 ∧ (a<5905584160 ∨ 7449088032≤a) at range
    apply readBuffer_zero_of_bytes;intro j hj;have eq:j=0:=by omega
    subst j;exact data.fresh a (by dsimp [MEMORY_BYTES];omega) (Or.inr ⟨by unfold C_TD;omega,range.2.2⟩)

theorem Ground.kept {o m r s t} (data : Ground o m r s)
    (keep : ∀ a n,4096≤a → a+n≤2^64 → (a+n≤5301604576 ∨ 5368714368≤a) →
      readBuffer t a n=readBuffer s a n) (gaps : Gaps t) : Ground o m r t := by
  refine ⟨?_,?_,?_,gaps,?_⟩
  · intro i;have fit : i.val<16777216:=i.isLt
    apply (keep _ _ ?_ ?_ (Or.inr ?_)).trans (data.rows i) <;> dsimp [finalRowAddress,rowBase] <;> omega
  · intro i;have fit : i.val<16777216:=i.isLt
    apply (keep _ _ ?_ ?_ (Or.inr ?_)).trans (data.salts i) <;> dsimp [sharedSaltAddr,rowBase] <;> omega
  · intro h lh i hi;obtain ⟨lo,end_⟩:=earlyRange h i lh hi
    change 4294971424≤_ at lo
    exact (keep _ _ (by omega) (by omega) (Or.inl end_)).trans (data.omitted _ lh _ hi)
  · intro a p
    have z:=p
    change 5368714368≤a ∧ a<7650414624 ∧ _ at z
    exact (keep a 1 (by omega) (by omega) (Or.inr z.1)).trans (data.tail a p)
end CommitGolfCandidate.RungA
