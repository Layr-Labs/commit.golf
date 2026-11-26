import CommitGolfCandidate.R4Tree
import CommitGolfCandidate.S4OpeningLaw
import CommitGolfCandidate.S4CheckLaw
import CommitGolfCandidate.S4HonestCarry
import CommitGolfCandidate.S4HidingTransfer
namespace CommitGolfCandidate.R4
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec
open S4
set_option maxRecDepth 10000
attribute [local irreducible] execute readBuffer List.finRange List.range
abbrev Draw := Fin (LENGTH/2) → PairRand
def issued (s : MachineState) : Execution := ⟨.success,s,847964651,78293686⟩
def actualTree (o : Oracle) (m : Message) (r : Draw) := S4Hiding.tree o.compression m (pairSalts r)
def rootOf (o : Oracle) (m : Message) (r : Draw) := Late.node (actualTree o m r) LOG_LENGTH 0
def CommitLaw := ∀ o m,∃ state : Draw→MachineState,
  (o.run (Late.submission.run .commit m) =ᵈ (($ᵗ Draw) >>= fun r=>pure (issued (state r),78293686))) ∧
  ∀ r,(Late.submission.readCommit (issued (state r))).1=rootOf o m r ∧
    Late.TrapdoorAgrees (Late.submission.readCommit (issued (state r))).2 (actualTree o m r) (pairSalts r)
noncomputable abbrev op := S4.Open.machineOpening
abbrev ch := S4.Machine.machineChecker
private theorem supported {α : Type} {p q : ProbComp α} (h : p =ᵈ q) : support p=support q := support_eq_of_evalDistEq h
theorem saltsAgree (r : Draw) : pairSalts r=LateHiding.unpackTape r := by
  funext i
  simp only [pairSalts,LateHiding.unpackTape,Late.pairSalts,Nat.testBit_eq_decide_div_mod_eq,Nat.pow_zero,Nat.div_one]
  have lor : i.val%2=0 ∨ i.val%2=1:=by omega
  rcases lor with z|z <;> simp only [z,ite_true,ite_false,decide_true,decide_false,Bool.false_eq_true,Nat.one_ne_zero] <;> rfl

private def viewOf (o : Oracle) (m : Message) (ps : Positions) (r : Draw) :=
    actualInput m ps (actualTree o m r) (pairSalts r)
private def outcome (o : Oracle) (m : Message) (ps : Positions) (r : Draw) : Scheme.HonestResult :=
  let i:=viewOf o m ps r
  let ev:=o.eval (Late.submission.scheme.check i.commitment ps (m.restrict ps) i.proof)
  ⟨ev.1,78293686,0,ev.2,i.proof.length⟩

private theorem prEvent_uniform_bind_pure_eq_one {α β : Type} [SampleableType α]
    (f : α → β) (p : β → Prop) (h : ∀ a, p (f a)) :
    Pr{let y ← (($ᵗ α) >>= fun a => pure (f a))}[p y] = 1 := by
  have h1 : Pr{let y ← (($ᵗ α) >>= fun a => pure (f a))}[p y] =
      Pr{let y ← (($ᵗ α) >>= fun _ => (pure () : ProbComp Unit))}[True] := by
    apply prEvent_bind_congr ($ᵗ α) (fun a => pure (f a)) (fun _ => pure ()) p (fun _ => True)
    intro a
    classical
    rw [prEvent_pure, prEvent_pure]; simp [h a]
  rw [h1]
  have h2 : (fun _ : Unit => True) <$> (($ᵗ α) >>= fun _ => (pure () : ProbComp Unit)) =
      (($ᵗ α) >>= fun _ => (pure True : ProbComp Prop)) := by
    simp only [map_bind, map_pure]
  change prEvent ((fun _ : Unit => True) <$> (($ᵗ α) >>= fun _ => (pure () : ProbComp Unit))) = 1
  rw [h2, prEvent_def, OracleComp.evalDist_bind_const]
  change prEvent (pure True : ProbComp Prop) = 1
  rw [prEvent_pure_prop]; simp

private theorem distOfEq {α : Type} {p q : ProbComp α} (h : p=q) : p =ᵈ q:=h ▸ EvalDistEq.refl p
private theorem commitView (law : CommitLaw) (o : Oracle) (m : Message) :
    ∃ td : Draw→Late.Trapdoor,
      (o.run (Late.submission.scheme.commit m) =ᵈ (($ᵗ Draw) >>= fun r=>pure ((rootOf o m r,td r),78293686))) ∧
      ∀ r,Late.TrapdoorAgrees (td r) (actualTree o m r) (pairSalts r) := by
  obtain ⟨s,run,works⟩:=law o m
  let td (r : Draw):=(Late.submission.readCommit (issued (s r))).2
  let f (x : Execution×Nat):=(Late.submission.readCommit x.1,x.2)
  refine ⟨td,?_,fun r=>(works r).2⟩
  change (o.run (Late.submission.readCommit <$> Late.submission.run .commit m)) =ᵈ _
  rw [oracle_run_map]
  refine (run.map f).trans (distOfEq ?_)
  rw [map_bind];apply bind_congr;intro r
  rw [map_pure];apply congrArg pure
  exact Prod.ext (Prod.ext (works r).1 rfl) rfl

private theorem honest (law : CommitLaw) (o : Oracle) (m : Message) (ps : Positions) :
    Late.submission.scheme.honest o m ps =ᵈ (($ᵗ Draw) >>= fun r=>pure (outcome o m ps r)) := by
  obtain ⟨td,comm,valid⟩:=commitView law o m
  unfold Scheme.honest
  refine (comm.bind_left _).trans (distOfEq ?_)
  rw [bind_assoc];apply bind_congr;intro r
  simp only [pure_bind,S4.openScheme op]
  rw [op.output _ _ _ ps (valid r)];rfl

private theorem hiddenTranscript (law : CommitLaw) : Late.submission.scheme.Hiding HIDING_ERROR := by
  apply S4Hiding.machine_hiding_of_words
  intro o m ps
  obtain ⟨td,comm,valid⟩:=commitView law o m
  unfold S4Hiding.transcript
  rw [LateHiding.run_bind]
  unfold fixedOracleRun
  refine ((comm.map Prod.fst).bind_left _).trans (distOfEq ?_)
  rw [map_bind,bind_assoc];apply bind_congr;intro r
  simp only [map_pure,pure_bind,oracle_run_bind,S4.openScheme op,oracle_run_pure,Nat.zero_add]
  rw [op.output _ _ _ ps (valid r),←saltsAgree];rfl

private theorem term (law : CommitLaw) : Late.submission.Termination := by
  intro o prog input
  cases prog with
  | commit=>
    obtain ⟨s,run,_⟩:=law o input
    rw [run.prEvent_eq (fun x=>x.1.exit≠Riscv.Exit.unfinished)]
    exact prEvent_uniform_bind_pure_eq_one (fun r=>(issued (s r),78293686)) (fun x=>x.1.exit≠Riscv.Exit.unfinished)
      (fun _=>by exact (by decide : Riscv.Exit.success≠.unfinished))
  | opening=>
    rcases input with ⟨td,ps⟩;rw [op.run,oracle_run_pure]
    apply (prEvent_eq_one_iff _ _).mpr;intro x hx;rw [support_pure,Set.mem_singleton_iff] at hx;subst x;rw [op.exit];decide
  | check=>
    have det : o.run (Late.submission.run .check input)=pure (Machine.checkEvaluation o (Late.submission.run .check input)) := by
      by_cases fit : input.proof.length≤Late.submission.sizes.proof
      · simp only [Submission.run,fit,decide_true,ite_true];exact Machine.execute_check_evaluation ..
      · simp only [Submission.run,fit,decide_false,Bool.false_eq_true,ite_false,oracle_run_pure,Machine.check_evaluation_pure]
    rw [det];apply (prEvent_eq_one_iff _ _).mpr;intro x hx
    rw [support_pure,Set.mem_singleton_iff] at hx;subst x;exact ch.terminates o input

private theorem machineProperty (law : CommitLaw) (o : Oracle) (m : Message) (ps : Positions) :
    ∃ f : Draw→MachineResult, (o.run (Late.submission.honestMachine m ps) =ᵈ (($ᵗ Draw) >>= fun r=>pure (f r,78293686))) ∧
        ∀ r,(f r).success=true ∧ (f r).commitCycles≤847964651 ∧ (ps.card=BATCH → (f r).openingCycles≤96415) := by
  obtain ⟨s,run,_⟩:=law o m
  let td (r : Draw):=(Late.submission.readCommit (issued (s r))).2
  let oe (r : Draw):=op.result (td r) ps
  let f (r : Draw) : MachineResult:=⟨true,847964651,(oe r).cycles,(Late.submission.readProof (oe r)).length⟩
  refine ⟨f,?_,fun r=>⟨rfl,le_rfl,op.priced _ _⟩⟩
  rw [Submission.honestMachine,oracle_run_bind]
  refine (run.bind_left _).trans (distOfEq ?_)
  rw [bind_assoc];apply bind_congr;intro r
  simp only [pure_bind,op.run,oracle_run_pure,Nat.add_zero]
  change pure ((⟨true && Late.submission.openingSucceeded (oe r),847964651,(oe r).cycles,(Late.submission.readProof (oe r)).length⟩ : MachineResult),78293686)=_
  rw [show Late.submission.openingSucceeded (oe r)=true from op.success ..];rfl

private theorem honestSupport (law : CommitLaw) (o : Oracle) (m : Message) (ps : Positions) (x : Scheme.HonestResult)
    (hx : x∈support (Late.submission.scheme.honest o m ps)) : ∃ r,x=outcome o m ps r:=by
  rw [supported (honest law o m ps),mem_support_bind_iff] at hx
  obtain ⟨r,_,h⟩:=hx;exact ⟨r,by simpa only [support_pure,Set.mem_singleton_iff] using h⟩

theorem certified (law : CommitLaw) : Certificate Late.submission 70080 847964651 96415 where
  admission:=Late.admission
  termination:=term law
  machineSuccess:=by
    intro o m p;obtain ⟨f,run,ok⟩:=machineProperty law o m p
    rw [run.prEvent_eq (fun x=>x.1.success=true)]
    exact prEvent_uniform_bind_pure_eq_one (fun r=>(f r,78293686)) _ (fun r=>(ok r).1)
  proverCycles:=by
    intro o m p b;obtain ⟨f,run,ok⟩:=machineProperty law o m p
    rw [run.prEvent_eq (fun x=>x.1.commitCycles≤847964651 ∧ x.1.openingCycles≤96415)]
    exact prEvent_uniform_bind_pure_eq_one (fun r=>(f r,78293686)) _ (fun r=>⟨(ok r).2.1,(ok r).2.2 b⟩)
  completeness:=by
    intro o m p;apply (prEvent_eq_one_iff _ _).mpr;intro x hx
    obtain ⟨r,rfl⟩:=honestSupport law o m p x hx
    have t : HonestTree .packed o.compression m (pairSalts r) (actualTree o m r):=honestTree .. 
    apply (ch.valid o (viewOf o m p r)).mpr
    rw [viewOf,widenHonest _ _ _ _ _ t];exact honestValid _ _ _ _ _ t
  honestBudgets:=by
    intro o m p;apply (prEvent_eq_one_iff _ _).mpr;intro x hx
    obtain ⟨r,rfl⟩:=honestSupport law o m p x hx
    exact ⟨by exact (by decide : 78293686≤COMMIT_BUDGET),Nat.zero_le _,ch.calls o (viewOf o m p r)⟩
  proofSize:=by
    intro o m p b;apply (prEvent_eq_one_iff _ _).mpr;intro x hx
    obtain ⟨r,rfl⟩:=honestSupport law o m p x hx
    change (actualOpening _ _ p).length≤70080;rw [actualOpeningSize,if_pos b]
  binding:=trunc_submission_binding (fun o i=>(ch.valid o i).mp)
  hidingProperty:=hiddenTranscript law
end CommitGolfCandidate.R4
