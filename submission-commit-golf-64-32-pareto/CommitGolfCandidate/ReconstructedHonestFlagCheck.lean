import CommitGolfCandidate.ReconstructedHonestFlagEffect
import CommitGolfCandidate.ReconstructedHonestRecordExecution

namespace CommitGolfCandidate.Reconstruction.HonestFlagCheck
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open HonestRecordShapes HonestRecordMemory HonestProtected HonestFlagEffect
open CommitBlocks (addr)

set_option maxRecDepth 32768
attribute [local irreducible] ArtifactEncoding.decode

def checked (i k : Nat) := match current i k with
  | none => true
  | some a => HonestFlagEffect.check 64 (addr k) (a.model context) false

def ValidChecks := ∀ (i : Fin 128) (k : Nat), checked i.val k=true

private theorem finer (pc : Word) (cut : HonestRecordCost.cut pc=true) : stopAt pc=true := by
  simp only [HonestRecordCost.cut,Bool.or_eq_true,beq_iff_eq] at cut
  rcases cut with rfl|rfl <;> decide

theorem record_marks (observes : ValidChecks) (i : Fin 128) (s t : MachineState) (coins : Bool)
    (startPC : s.pc=addr 143) (ready : Holds context (start i.val) s)
    (walk : HonestCuts.Reaches (Artifact.submission.image .opening) coins HonestRecordCost.cut s t) :
    ∃ event, Valid event ∧ Effect s t event := by
  let Mid (u : MachineState) := ∃ k pre, u.pc=addr k ∧ current i.val k=some pre ∧ Holds context pre u ∧ Effect s u none
  apply HonestNested.carry finer Mid (fun u => ∃ event, Valid event ∧ Effect s u event) (s:=s) (t:=t)
    _ ⟨143,start i.val,startPC,rfl,ready,reflexive s⟩ walk
  intro u v pre path
  obtain ⟨k,shape,loc,atShape,holds,prior⟩ := pre
  have cert := observes i k
  simp only [checked,atShape] at cert
  obtain ⟨event,allowed,acts,ending⟩ := HonestFlagEffect.sound 64 (addr k) _ s u v none
    trivial prior cert coins loc (models_shape holds) path
  constructor
  · intro _; exact ⟨event,allowed,acts⟩
  · intro inner
    have eventNone : event=none := by cases event <;> first | rfl | (have impossible := ending rfl; simp_all)
    subst event
    have checked := HonestRecordExecution.all_checked i k
    simp only [HonestRecordCheck.checked,atShape] at checked
    obtain ⟨b,target,body⟩ := HonestRegionBlocks.from_shape context Artifact.openingCode (Artifact.submission.image .opening)
      (Eq.refl (ArtifactEncoding.decode 32 _)) (by decide) stopAt (nextShape i.val) 64 (addr k) shape checked
      u v coins loc holds path
    let j := HonestBinaryRank.index v.pc
    have aligned : v.pc=addr j := by
      by_contra no
      simp only [nextShape,show HonestBinaryRank.index v.pc=j from rfl,ite_eq_left no,reduceCtorEq] at target
    have noRecord : j≠143 := by intro eq; rw [aligned,eq] at inner; cases inner
    have noCap : j≠1429 := by intro eq; rw [aligned,eq] at inner; cases inner
    have ok : ¬v.pc≠addr j := fun h => h aligned
    simp only [nextShape,show HonestBinaryRank.index v.pc=j from rfl,ite_eq_right ok,ite_eq_right noRecord,ite_eq_right noCap] at target
    exact ⟨j,b,aligned,target,body,acts⟩

end CommitGolfCandidate.Reconstruction.HonestFlagCheck
