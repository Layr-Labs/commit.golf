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
  refine ⟨term,Nat.zero_le _,?_,?_⟩
  · intro _ j
    have h:=Finset.card_pos.mpr ⟨j.val,j.property⟩
    omega
  · intro msg salts canonical;apply accept
    exact canonical.symm ▸ honest_input_empty oracle msg i.positions salts empty

private theorem positive_body (record : Oracle → Nat → Index → MachineState → RecordBlock)
    (verified : RecordRefines record)
    (cap : ∀ (oracle : Oracle) (input : CheckInput), input.positions.card ≠ 0 →
      ∀ state rows rest, 40000 ≤ rest → RecordCursor input input.positions.card state →
      RecordInputFrame input input.positions.card state →
      CollectedTable oracle input input.positions.card state rows → CheckerCapFacts oracle input state rest)
    (oracle : Oracle) (i : CheckInput) (e : HeaderEntry i) (fits : i.proof.length≤8959041024)
    (nonempty : i.positions.card≠0) (long : 534*i.positions.card ≤ i.proof.length)
    (framed : RecordInputFrame i 0 e.state) (marks : ∀ g<512, Opening.machineMarks e.state g=0)
    (fuel : Nat) (reserve : 34359803904 ≤ fuel) : CheckerObservationFacts oracle i (machine oracle fuel e.state) := by
  obtain ⟨state,cursor,memory,run⟩:=header_positive i e fits nonempty long
  have k:=checker_positions_bound i
  have frame : RecordInputFrame i 0 state := by
    intro q bound used;exact (congrFun memory (wordAddress q)).trans (framed q bound used)
  have table:=collected_table_empty oracle i state (by
    intro g hg;exact (congrFun memory _).trans (marks g hg))
  have body:=checker_body_facts record verified oracle i state ⟨long,fits⟩ cursor frame table (fuel-21) (by omega) (cap oracle i nonempty)
  simpa only [show 21+(fuel-21)=fuel by omega] using observation_hop oracle i e.state state 21 24 (fuel-21) run body

/-- The physical checker's trace and exit refine the canonical checker facts on converted input.
The gather table need only be bounded. -/
theorem converted_observation (τ : Layout2.Tables) (wf : Layout2.WellFormed τ)
    (physical : ∀ k, k<85440 → GroupedOpening.pget K1Artifact.checkData k=Layout2.tableByte τ k)
    (record : Oracle → Nat → Index → MachineState → RecordBlock) (verified : RecordRefines record)
    (cap : ∀ (oracle : Oracle) (input : CheckInput), input.positions.card ≠ 0 →
      ∀ state rows rest, 40000 ≤ rest → RecordCursor input input.positions.card state →
      RecordInputFrame input input.positions.card state →
      CollectedTable oracle input input.positions.card state rows → CheckerCapFacts oracle input state rest)
    (oracle : Oracle) (i : CheckInput) :
    CheckerObservationFacts oracle (Layout2.converted τ i) (checkObservation K1Artifact.submission oracle i) := by
  let v:=Layout2.converted τ i
  let s:=K1Artifact.submission.initialState .check i
  let k:=i.positions.card
  have eqL : v.proof.length=i.proof.length := Layout2.convert_length _ _ _
  change CheckerObservationFacts oracle v _
  by_cases good : i.proof.length ≤ K1Artifact.submission.sizes.proof
  · rw [observation_admitted oracle i good]
    have args:=Layout2.initial_args i good
    have base : s.pc=Layout2.pc 0 := check_start _ _
    by_cases short : i.proof.length<534*k
    · obtain ⟨t,pre,atBad⟩:=Layout2.short_run Layout2.concrete_program s k _ base args short
      have head:=pre (3+(2^41-7))
      rw [execute_header_reject _ atBad (2^41-7),pure_bind] at head
      unfold machine;rw [show (2^41:Nat)=4+(3+(2^41-7)) by decide,head,record_rows_pure,check_evaluation_pure]
      refine ⟨(by change Exit.failure ≠ Exit.unfinished;decide),Nat.zero_le _,?_,?_⟩
      · intro no;cases no
      · intro msg salts canonical
        have h : 534*v.positions.card ≤ v.proof.length := canonical.symm ▸ honest_input_records_fit oracle msg v.positions salts
        change 534*k≤_ at h;omega
    · have long:=Nat.le_of_not_gt short
      obtain ⟨t,run,endState⟩:=Layout2.prologue Layout2.concrete_program wf s k _ base args long (Layout2.initial_tables τ wf physical i good) (Layout2.scratch_clean i)
      let e:=Layout2.header_entry endState
      have left:=Layout2.fuel_reserve k args.count
      let spare:=2^41-Layout2.prologueSteps k
      have room : 34359803904 ≤ spare := by dsimp [spare];omega
      have body : CheckerObservationFacts oracle v (machine oracle spare t) := by
        by_cases empty : k=0
        · exact empty_body oracle v e (eqL.trans_le good) empty spare (by omega)
        · obtain ⟨frame,marks⟩:=Layout2.record_entry wf i good long t endState
          exact positive_body record verified cap oracle v e (eqL.trans_le good) empty (by change 534*k ≤ v.proof.length;omega)
            frame marks spare room
      exact (show Layout2.prologueSteps k+spare=2^41 by dsimp [spare];omega) ▸
        observation_hop oracle v s t _ _ spare run body
  · rw [observation_oversized oracle i (Nat.lt_of_not_ge good)]
    refine ⟨(by change Exit.failure ≠ Exit.unfinished;decide),Nat.zero_le _,?_,?_⟩
    · intro no;cases no
    · intro msg salts canonical
      have honestFit : (honestCheckInput oracle msg v.positions salts).proof.length ≤ 8959041024 :=
        honest_input_admitted oracle msg v.positions salts
      have vFit := (congrArg (fun x : CheckInput=>x.proof.length) canonical).trans_le honestFit
      exact (good (eqL.symm.trans_le vFit)).elim

end TwoPermutationPrototype.Packed.Checker
