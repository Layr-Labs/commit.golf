import CommitGolfCandidate.ReconstructedCheckCapArith
import CommitGolfCandidate.ReconstructedCheckLoader
import CommitGolfCandidate.ReconstructedEmpty

namespace CommitGolfCandidate.Reconstruction.CheckEmptyTrace
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding.Machine CheckRecorded CommitBlocks CheckCapArith
open TwoPermutationPrototype.Sampling TwoPermutationPrototype.Checker
set_option maxRecDepth 10000
set_option maxHeartbeats 850000
attribute [local irreducible] execute ArtifactEncoding.decode

def code : List Line := [(.x10,.op (.sltu .x0 .x17)),(.x11,.op (.addi .x0 0)),(.x5,.op (.addi .x0 1))]
private theorem listedCode : listed 1 code=true:=by decide

theorem complete (o : Oracle) (s : MachineState) (pc : s.pc=addr 0) (count : s.getReg .x16=0#64) (fuel : Nat) :
    (observation o (5+fuel) s).1.1.exit≠.unfinished ∧ (observation o (5+fuel) s).1.2=[] ∧ (observation o (5+fuel) s).2=0 := by
  have b:=CheckBranch.event o s 0 5 .ne .x16 .x0 20 (by decide) pc (CheckDecode.same_sound (by decide)) (by decide)
  let u:=s.setPC (addr 1)
  have first : Segment o 1 s u []:=by
    change Segment o 1 s (s.setPC (if (s.getReg .x16 != 0#64)=true then _ else _)) [] at b
    rw [count] at b;exact b
  let v:=effect u code
  have next : Segment o 3 u v []:=CheckCapArith.positive o u 1 code rfl listedCode
  have halt : execute image (fuel+1) v false = pure (⟨if v.getReg .x10=0 then .success else .failure,v,1,0⟩ : Execution):=by
    rw [execute,CheckMemoryOps.parsed (n:=4) (ins:=.base .ECALL) (by decide) v (location u 1 code rfl)]
    have c : v.getReg .x5=1#64:=by rw [register];rfl
    rw [c];rfl
  have obs : observation o (fuel+1) v=((⟨if v.getReg .x10=0 then .success else .failure,v,1,0⟩,[]),0):=by
    unfold observation;rw [halt,record_rows_pure];rfl
  obtain ⟨cost,all⟩:=compose first next
  rw [show 5+fuel=(1+3)+(fuel+1) by omega,all,obs];refine ⟨?_,rfl,rfl⟩
  change (if v.getReg .x10=0 then Exit.success else Exit.failure)≠.unfinished;split <;> decide

theorem terminal (o : Oracle) (s : MachineState) (pc : s.pc=addr 0) (count : s.getReg .x16=0#64) (fuel : Nat) :
    (observation o (5+fuel) s).1.2=[] ∧ (observation o (5+fuel) s).2=0 := (complete o s pc count fuel).2

theorem within (o : Oracle) (input : CheckInput) (fits : input.proof.length≤Artifact.submission.sizes.proof) :
    checkObservation Artifact.submission o input=observation o 274877906944 (CheckLoader.initial input) := by
  unfold checkObservation observation;simp [Submission.run,fits,CheckLoader.initial];rfl

theorem oversized (o : Oracle) (input : CheckInput) (big : ¬input.proof.length≤Artifact.submission.sizes.proof) :
    (checkObservation Artifact.submission o input).1.1.exit=.failure := by
  unfold checkObservation;simp [Submission.run,big,record_rows_pure,check_evaluation_pure]

theorem traces (o : Oracle) (input : CheckInput) (empty : input.positions.card=0) (fits : input.proof.length≤Artifact.submission.sizes.proof) :
    (checkObservation Artifact.submission o input).1.2=[] ∧ (checkObservation Artifact.submission o input).2=0 := by
  rw [within o input fits]
  apply terminal o (CheckLoader.initial input) rfl _ (274877906944-5)
  change BitVec.ofNat 64 input.positions.card=0#64;rw [empty]

theorem finishes (o : Oracle) (input : CheckInput) (empty : input.positions.card=0) (fits : input.proof.length≤Artifact.submission.sizes.proof) :
    (checkObservation Artifact.submission o input).1.1.exit≠.unfinished := by
  rw [within o input fits]
  exact (complete o (CheckLoader.initial input) rfl (by change BitVec.ofNat 64 input.positions.card=0#64;rw [empty]) (274877906944-5)).1

end CommitGolfCandidate.Reconstruction.CheckEmptyTrace
