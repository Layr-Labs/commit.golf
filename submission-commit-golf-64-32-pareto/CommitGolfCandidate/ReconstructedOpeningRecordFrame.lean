import CommitGolfCandidate.ReconstructedOpeningRowEffect
import CommitGolfCandidate.ReconstructedOpeningRecordSalt

namespace CommitGolfCandidate.Reconstruction.OpeningRecordFrame
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OpeningPut OpeningRowEffect OpeningCursor
open TwoPermutationPrototype.RV64 LeafModel OpeningQuery OpeningReply OpeningRecordSalt CommitWindows
open TwoPermutationPrototype (Memory writeWord writeWindow)
set_option maxRecDepth 14000
attribute [local irreducible] atQuery ArtifactEncoding.decode

/-- Words used by the next record that stay untouched throughout the encoder. -/
def stable (w : Nat) := outside w ∧ w≠generatorBase+1 ∧ (w<8589934265 ∨ 8589934297≤w) ∧
  (w<532480 ∨ 532608≤w)

instance (w : Nat) : Decidable (stable w) := by unfold stable outside;infer_instance

def Agrees (m a : Memory) := ∀ w, stable w → m w=a w

theorem salt_frame (o : Oracle) (m t : Model) (k : Generator.Key) (ord c : Nat) (i : Index)
    (entry : Entry m ord i) (result : Result o m t k ord c i) (room : (c+64)/64<capacity) (w : Nat)
    (away : outside w) (window : ¬(replyBase≤w ∧ w<replyBase+25)) (counter : w≠generatorBase+1) :
    t.mem w=(saves m).mem w := by
  have h := (setup o m ord i entry).2.2
  rw [result.memory,put_frame _ (c+64) _ _ _ room away,put_frame _ c _ _ _ (by omega) away]
  simp only [answer,Model.permute,writeWindow,window,dite_false,h,writeWord,counter,ite_false]

theorem salt_stable (o : Oracle) (m t : Model) (k : Generator.Key) (ord c : Nat) (i : Index)
    (entry : Entry m ord i) (result : Result o m t k ord c i) (room : (c+64)/64<capacity) : Agrees t.mem m.mem := by
  intro w pw
  obtain ⟨away,h,stack,_⟩ := pw
  rw [salt_frame o m t k ord c i entry result room w away (by unfold replyBase;omega) h]
  simp only [saves,Model.store,writeWord,ite_eq_right (by unfold savePtr;omega : w≠savePtr),
    ite_eq_right (by unfold saveCount;omega : w≠saveCount)]

theorem salt_saves (o : Oracle) (m t : Model) (k : Generator.Key) (ord c : Nat) (i : Index)
    (entry : Entry m ord i) (result : Result o m t k ord c i) (room : (c+64)/64<capacity) :
    t.mem saveCount=m.reg .x12 ∧ t.mem savePtr=m.reg .x11 := by
  constructor
  · rw [salt_frame o m t k ord c i entry result room _ (Or.inr (by decide)) (by decide) (by decide)]
    rfl
  · rw [salt_frame o m t k ord c i entry result room _ (Or.inr (by decide)) (by decide) (by decide)]
    rfl

theorem heap_of_agrees (m : Memory) (trap : CommitStorage.Trapdoor) (ps : Positions)
    (h : Agrees m (memoryView (HonestInputs.first trap ps))) : OpeningWordFields.Heap m trap ps := by
  intro d j b w sm
  have lim := b.2.2.trans_le (Nat.pow_le_pow_right (n:=2) (by decide) (show d+1≤25 by have := b.1;omega))
  have depth := b.1
  let idx := CommitParents.addr d j/8+w
  have range : 536871428 ≤ idx ∧ idx < 704643500 := by unfold idx CommitParents.addr;omega
  have owned : stable idx := by unfold stable outside base capacity generatorBase;omega
  have physical : 8*idx=CommitParents.addr d j+8*w := by unfold idx CommitParents.addr;omega
  rw [h _ owned];change (HonestInputs.first trap ps).getMem (W (8*idx))=_;rw [physical]

theorem key_of_agrees (m : Memory) (trap : CommitStorage.Trapdoor) (ps : Positions) (nonempty : 0<ps.card)
    (o : Oracle) (k : Generator.Key) (msg : Message) (stored : CommitStorage.Stored o k msg trap)
    (h : Agrees m (memoryView (HonestInputs.first trap ps))) : LeafContent.KeyRegion m k := by
  intro w lo hi ex
  have owned : stable w := by unfold stable outside base capacity generatorBase at *;omega
  rw [h _ owned];exact OpeningTrap.first_generator o k msg trap stored ps nonempty w lo hi ex

end CommitGolfCandidate.Reconstruction.OpeningRecordFrame
