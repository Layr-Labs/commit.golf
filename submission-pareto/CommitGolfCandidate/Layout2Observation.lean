import CommitGolfCandidate.Layout2CapLoaded
import CommitGolfCandidate.Layout2QuartetLoaded
import CommitGolfCandidate.Layout2Loaded
import CommitGolfCandidate.Layout2Delivered
import CommitGolfCandidate.QuartetManifest
import CommitGolfCandidate.TwoPermutationPackedCheckerBody
import CommitGolfCandidate.TwoPermutationPackedHeaderAssembly
import CommitGolfCandidate.TwoPermutationPackedTrustedInput

import CommitGolfCandidate.TwoPermutationPackedHonestInput

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Checker (checkObservation check_recorded_map checker_positions_bound RecordInputFrame)
open TwoPermutationPrototype.QuartetCertificate (honestCheckInput)
open TwoPermutationPrototype.PackedHonest (honest_input_empty honest_input_records_fit honest_input_admitted)
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000

attribute [local irreducible] execute checkEvaluation
private abbrev machine (o : Oracle) (fuel : Nat) (s : MachineState) :=
  checkEvaluation o (recordRows (execute packedImage fuel s false))

private theorem check_start (sub : Submission) (i : CheckInput) :
    (sub.initialState .check i).pc=Layout2.pc 0 := rfl

private theorem admitted_run (sub : Submission) (i : CheckInput) (fits : i.proof.length ≤ sub.sizes.proof) :
    sub.run .check i=execute (sub.image .check) (sub.steps .check) (sub.initialState .check i) false := by
  simp only [Submission.run,fits,decide_true,ite_true] <;> rfl

private theorem oversized_run (sub : Submission) (i : CheckInput) (large : sub.sizes.proof < i.proof.length) :
    sub.run .check i=pure ⟨.failure,initialMachine,0,0⟩ := by
  simp only [Submission.run,Nat.not_le_of_lt large,decide_false,Bool.false_eq_true,ite_false]

attribute [local irreducible] Submission.initialState ArtifactEncoding.decode

private theorem observation_admitted (oracle : Oracle) (input : CheckInput)
    (admitted : input.proof.length ≤ K1Artifact.submission.sizes.proof) :
    checkObservation K1Artifact.submission oracle input =
      machine oracle (2^41) (K1Artifact.submission.initialState .check input) := by
  unfold checkObservation machine
  rw [admitted_run _ _ admitted,Layout2.delivered_image] <;> rfl

private theorem observation_oversized (oracle : Oracle) (input : CheckInput)
    (oversized : K1Artifact.submission.sizes.proof < input.proof.length) :
    checkObservation K1Artifact.submission oracle input = ((⟨.failure,initialMachine,0,0⟩,[]),0) := by
  unfold checkObservation
  rw [oversized_run _ _ oversized,record_rows_pure,check_evaluation_pure]

private theorem observation_hop (oracle : Oracle) (input : CheckInput)
    (before after : MachineState) (steps cycles fuel : Nat) (hop : Hop before after steps cycles)
    (body : CheckerObservationFacts oracle input
      (checkEvaluation oracle (recordRows (execute packedImage fuel after false)))) :
    CheckerObservationFacts oracle input
      (checkEvaluation oracle (recordRows (execute packedImage (steps+fuel) before false))) := by
  rw [hop fuel,bind_pure_comp,check_recorded_map]
  exact body.charge cycles

private theorem empty_body (oracle : Oracle) (i : CheckInput) (e : HeaderEntry i) (fits : i.proof.length≤8959041024)
    (empty : i.positions.card=0) (fuel : Nat) (reserve : 7 ≤ fuel) :
    CheckerObservationFacts oracle i (machine oracle fuel e.state) := by
  have ⟨z,run,term,accept⟩:=header_empty i e fits empty (fuel-7)
  rw [show 7+(fuel-7)=fuel by omega] at run
  unfold machine
  rw [run,record_rows_pure,check_evaluation_pure]
  refine ⟨term,Nat.zero_le _,?_,?_,?_⟩
  · intro _ j
    have h:=Finset.card_pos.mpr ⟨j.val,j.property⟩
    omega
  · intro msg salts canonical;apply accept
    exact canonical.symm ▸ honest_input_empty oracle msg i.positions salts empty
  · intro _ _ _ k128 _
    omega

private theorem positive_body (record : Oracle → Nat → Index → MachineState → RecordBlock)
    (verified : RecordRefines record)
    (cap : ∀ (oracle : Oracle) (input : CheckInput), input.positions.card ≠ 0 →
      ∀ state rows rest, 80000 ≤ rest → RecordCursor input input.positions.card state →
      RecordInputFrame input input.positions.card state →
      CollectedTable oracle input input.positions.card state rows → CheckerCapFacts oracle input state rest)
    (oracle : Oracle) (i : CheckInput) (e : HeaderEntry i) (fits : i.proof.length≤8959041024)
    (nonempty : i.positions.card≠0) (long : 534*i.positions.card ≤ i.proof.length)
    (framed : RecordInputFrame i 0 e.state) (marks : ∀ g<512, Opening.machineMarks e.state g=0)
    (fuel : Nat) (reserve : 34359900000 ≤ fuel) : CheckerObservationFacts oracle i (machine oracle fuel e.state) := by
  obtain ⟨state,cursor,memory,run⟩:=header_positive i e fits nonempty long
  have k:=checker_positions_bound i
  have frame : RecordInputFrame i 0 state := by
    intro q bound used;exact (congrFun memory (wordAddress q)).trans (framed q bound used)
  have table:=collected_table_empty oracle i state (by
    intro g hg;exact (congrFun memory _).trans (marks g hg))
  have body:=checker_body_facts record verified oracle i state ⟨long,fits⟩ cursor frame table (fuel-21) (by omega) (cap oracle i nonempty)
  simpa only [show 21+(fuel-21)=fuel by omega] using observation_hop oracle i e.state state 21 24 (fuel-21) run body

/-- The physical checker's trace and exit refine the canonical checker facts on the converted effective input
(one-byte search: a k = 128 proof of 72,159 bytes is read as 72,160 bytes ending in 0). The gather table need only be
bounded. -/
theorem converted_observation (τ : Layout2.Tables) (wf : Layout2.WellFormed τ)
    (physical : ∀ k, k<85440 → CommitGolfCandidate.Layout2Helpers.pget K1Artifact.checkData k=Layout2.tableByte τ k)
    (record : Oracle → Nat → Index → MachineState → RecordBlock) (verified : RecordRefines record)
    (cap : ∀ (oracle : Oracle) (input : CheckInput), input.positions.card ≠ 0 →
      ∀ state rows rest, 80000 ≤ rest → RecordCursor input input.positions.card state →
      RecordInputFrame input input.positions.card state →
      CollectedTable oracle input input.positions.card state rows → CheckerCapFacts oracle input state rest)
    (oracle : Oracle) (i : CheckInput) :
    CheckerObservationFacts oracle (Layout2.converted τ (Layout2.Quartet.prepared (Layout2.Cap.prepared
      (Layout2.Cap.effective i)))) (checkObservation K1Artifact.submission oracle i) := by
  let e:=Layout2.Cap.effective i
  let v:=Layout2.converted τ (Layout2.Quartet.prepared (Layout2.Cap.prepared e))
  let s:=K1Artifact.submission.initialState .check i
  let k:=i.positions.card
  have ePos : e.positions=i.positions := Layout2.Cap.effective_positions i
  have eqL : v.proof.length=e.proof.length :=
    (Layout2.convert_length ..).trans ((Layout2.Quartet.prepared_len _).trans (Layout2.Cap.prepared_len e))
  have vPos : v.positions=i.positions := ePos
  have nearLen (msg : Message) (salts : CompleteSaltTape) (near : v = nearCheckInput oracle msg v.positions salts)
      (f : (honestNodes oracle msg v.positions salts).length = 128) :
      v.proof.length=(honestCheckInput oracle msg v.positions salts).proof.length := by
    have close := near_honest_input oracle msg v.positions salts (by omega)
    rw [← near] at close
    exact close.length
  change CheckerObservationFacts oracle v _
  by_cases good : i.proof.length ≤ K1Artifact.submission.sizes.proof
  · rw [observation_admitted oracle i good]
    change i.proof.length≤8959041024 at good
    have eFits : e.proof.length≤8959041024 := by
      rw [Layout2.Cap.effective_length]
      split <;> omega
    obtain ⟨t,h,c,left,run,endState⟩:=Layout2.Cap.prepare_run τ wf physical i good
    change Layout2.Runs packedImage s t h c at run
    by_cases legal : Layout2.Cap.Good k e.proof.length
    · rw [if_pos legal] at endState
      have long := legal.1
      let en:=Layout2.header_entry (show Layout2.Normalized τ (K1Artifact.submission.initialState .check
        (Layout2.Quartet.prepared (Layout2.Cap.prepared e))) t (Layout2.Quartet.prepared (Layout2.Cap.prepared e)).positions.card
        from by simpa [show (Layout2.Quartet.prepared (Layout2.Cap.prepared e)).positions=e.positions from rfl, ePos] using endState)
      let spare:=2^41-h
      have room : 34359900000 ≤ spare := by dsimp [spare];omega
      have body : CheckerObservationFacts oracle v (machine oracle spare t) := by
        by_cases empty : k=0
        · exact empty_body oracle v en (eqL.trans_le eFits) (by rw [vPos]; exact empty) spare (by omega)
        · obtain ⟨frame,marks⟩:=Layout2.record_entry wf (Layout2.Quartet.prepared (Layout2.Cap.prepared e))
            (by simpa using eFits)
            (by simpa only [Layout2.Quartet.prepared_len,Layout2.Cap.prepared_len,
              show (Layout2.Quartet.prepared (Layout2.Cap.prepared e)).positions=e.positions from rfl, ePos] using long) t
            (by simpa [show (Layout2.Quartet.prepared (Layout2.Cap.prepared e)).positions=e.positions from rfl, ePos]
              using endState)
          exact positive_body record verified cap oracle v en (eqL.trans_le eFits) (by rw [vPos]; exact empty)
            (by change 534*v.positions.card ≤ v.proof.length; rw [vPos, eqL]; exact long) frame marks spare room
      exact (show h+spare=2^41 by dsimp [spare];omega) ▸
        observation_hop oracle v s t _ _ spare run body
    · rw [if_neg legal] at endState
      let spare:=2^41-(h+3)
      have sum : h+(3+spare)=2^41 := by dsimp [spare];omega
      have go:=run (3+spare)
      rw [execute_header_reject _ endState spare,pure_bind] at go
      unfold machine;rw [←sum,go,record_rows_pure,check_evaluation_pure]
      refine ⟨(by change Exit.failure ≠ Exit.unfinished;decide),Nat.zero_le _,?_,?_,?_⟩
      · intro no;cases no
      · intro msg salts canonical
        have ok:=Layout2.Cap.honest_good oracle msg v.positions salts
        rw [←canonical,eqL,vPos] at ok
        exact False.elim (legal ok)
      · intro msg salts near _ f
        have ok:=Layout2.Cap.honest_good oracle msg v.positions salts
        rw [←nearLen msg salts near f,eqL,vPos] at ok
        exact False.elim (legal ok)
  · rw [observation_oversized oracle i (Nat.lt_of_not_ge good)]
    have eSame : e = i := by
      unfold e Layout2.Cap.effective
      rw [if_neg]
      intro fire
      exact good (by have := fire.2; change i.proof.length ≤ 8959041024; omega)
    have vLen : v.proof.length = i.proof.length := eqL.trans (by rw [eSame])
    refine ⟨(by change Exit.failure ≠ Exit.unfinished;decide),Nat.zero_le _,?_,?_,?_⟩
    · intro no;cases no
    · intro msg salts canonical
      have honestFit : (honestCheckInput oracle msg v.positions salts).proof.length ≤ 8959041024 :=
        honest_input_admitted oracle msg v.positions salts
      have vFit := (congrArg (fun x : CheckInput=>x.proof.length) canonical).trans_le honestFit
      exact (good (vLen.symm.trans_le vFit)).elim
    · intro msg salts near _ f
      have honestFit : (honestCheckInput oracle msg v.positions salts).proof.length ≤ 8959041024 :=
        honest_input_admitted oracle msg v.positions salts
      exact (good (vLen.symm.trans_le ((nearLen msg salts near f).trans_le honestFit))).elim

end TwoPermutationPrototype.Packed.Checker
