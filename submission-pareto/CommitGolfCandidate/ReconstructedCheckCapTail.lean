import CommitGolfCandidate.ReconstructedCheckHonestEndpoint
import CommitGolfCandidate.ReconstructedCheckTail
import CommitGolfCandidate.ReconstructedCheckCapIterate
import CommitGolfCandidate.ReconstructedCheckRecordSlots

namespace CommitGolfCandidate.Reconstruction.CheckCapTail
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding CheckCapLevel CheckCapIterate CheckHonestEndpoint
open TwoPermutationPrototype.Sampling
set_option maxRecDepth 11000
set_option maxHeartbeats 900000
abbrev W:=BitVec.ofNat 64

theorem cursorBound {o f bits d c s out t rs} (trail : Trail o f bits d c s out t rs) :
    ∀ finalCursor,out=some finalCursor→finalCursor≤c+70000*d := by
  induction trail with
  | finish c s h=>intro v eq;exact Option.some.inj eq ▸ Nat.le_refl _
  | stopped=>intro v eq;cases eq
  | level k c s u t rs tail m out base good rest ih=>
    intro e eq;have remaining:=ih e eq;have delta:=good.cursor;omega

theorem entry {s t : MachineState} {input : CheckInput} {c : Nat} {f : Nat→Bool}
    (ready : Boundary f (Wire.unpackBytes input.proof) 0 c t) (frame : Frame s t) (p : CheckRecordABI.Persistent s input) :
    CheckTail.Entry t c input.proof.length (Wire.unpackBytes input.proof) := by
  have h:=transfer frame p
  exact ⟨ready.ready.pc,ready.ready.static.sp,ready.ready.static.fp,ready.ready.static.bits,h.ret,h.length,h.stream⟩

theorem root {t : MachineState} {input : CheckInput} (info : TailData t input) (cmp : ∀ j : Fin 4,CheckRoot.EqualAt t j) :
    node t 1=unpack input.commitment := by
  change CommitParents.cell t (4194304+32*1)=_
  apply CheckRecordSlots.physical
  intro j
  have addr : TwoPermutationPrototype.RV64.wordAddress (CheckRecordAccess.capWord 1 j)=W (CheckRootPlan.cap+8*j.val):=by
    unfold TwoPermutationPrototype.RV64.wordAddress CheckRecordAccess.capWord CheckRootPlan.cap;congr 1;omega
  rw [addr];apply (cmp j).trans;apply (info.root j).trans
  exact (congrArg (fun x : BitVec 256=>x.extractLsb' (64*j.val) 64) (pack_unpack input.commitment)).symm

end CommitGolfCandidate.Reconstruction.CheckCapTail
