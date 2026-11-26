import CommitGolfCandidate.TruncNormalStep
import CommitGolfCandidate.TruncStatic
namespace CommitGolfCandidate.Trunc.Normal
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 10000
set_option maxHeartbeats 140000
attribute [local irreducible] Late.Check.Normal.checkEvaluation execute Batch.obs mathRoot

theorem allRecords (o : Oracle) (i : CheckInput) (mode : i.positions.card≠BATCH) (left n : Nat)
    (len : n+left=i.positions.card) (s : MachineState) (f : Frame i n s) :
    ∃ k≤1480*left+3,∃ q≤28*left,∃ ex,Terminal o s k q ex ∧ ex≠.unfinished ∧
      (ex=.success ↔ ∀ j,n≤j → j < i.positions.card → mathRoot o i j=i.commitment) := by
  induction left generalizing n s with
  | zero=>
    have done : n=i.positions.card:=by omega
    refine ⟨3,by omega,0,by omega,.success,?_,by decide,?_⟩
    · intro fuel;rw [Batch.obs,check_exit s true (by rw [f.pc,if_pos done];rfl) fuel false,Late.Check.Normal.check_evaluation_pure];rfl
    · constructor
      · intro _ j bj ej;omega
      · intro _;rfl
  | succ left ih=>
    have here : n < i.positions.card:=by omega
    rcases oneRecord o i mode n here s f with ⟨bad,k,hk,rej⟩|⟨good,t,k,hk,run,nt⟩
    · exact ⟨k,by omega,28,by omega,.failure,rej,by decide,⟨by intro h;contradiction,fun h=>False.elim (bad (h n le_rfl here))⟩⟩
    · obtain ⟨j,bj,q,bq,ex,fin,term,v⟩:=ih (n+1) (by omega) t nt
      refine ⟨k+j,by omega,28+q,by omega,ex,runsThen run fin,term,?_⟩
      constructor
      · intro ok r nr br
        rcases Nat.eq_or_lt_of_le nr with eq|gt
        · simpa [←eq] using good
        · exact v.mp ok r gt br
      · intro h;exact v.mpr (fun r nr br=>h r (by omega) br)

private theorem countPC (n : Nat) (bound : n≤16777216) :
    (if BitVec.ofNat 64 n=0 then (4420 : Word) else 4156)=(if 0=n then 4420 else 4156) := by
  by_cases zero : n=0
  · rw [zero];rfl
  · have nz : BitVec.ofNat 64 n≠0 := by
      intro e;have a:=congrArg BitVec.toNat e
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)] at a;exact zero a
    rw [if_neg nz,if_neg (Ne.symm zero)]

def readyInput (i : CheckInput) := checkReadyState (checkLengthState (Trunc.submission.initialState .check i))
theorem initialFrame (i : CheckInput) : Frame i 0 (readyInput i) := by
  let s:=Trunc.submission.initialState .check i
  have card:=positionCount i.positions
  change Frame i 0 (checkReadyState (checkLengthState s))
  have rest : (checkLengthState s).getReg .x27=BitVec.ofNat 64 i.positions.card :=
    (check_length_preserves s).1
  refine ⟨rfl,rfl,rfl,?_,rfl,rfl,rfl,rfl,?_,fun _ _ _ _=>rfl⟩
  · exact rest
  exact (congrArg (fun v : Word => if v=0 then (4420 : Word) else 4156) rest).trans
    (countPC i.positions.card card)

theorem evaluate (o : Oracle) (i : CheckInput) (mode : i.positions.card≠BATCH) :
    let out:=Late.Check.Normal.checkEvaluation o (Trunc.submission.run .check i)
    out.1.exit≠.unfinished ∧ out.2≤28*i.positions.card ∧
      (out.1.exit=.success ↔ i.proof.length=792*i.positions.card ∧ ∀ j < i.positions.card, mathRoot o i j=i.commitment) := by
  dsimp only
  let s:=Trunc.submission.initialState .check i
  have card:=positionCount i.positions
  have diff : s.getReg .x16≠128 := by
    intro e;have v:=congrArg BitVec.toNat e;change i.positions.card%2^64=128 at v
    rw [Nat.mod_eq_of_lt (by omega)] at v;exact mode v
  by_cases fits : i.proof.length≤Trunc.submission.sizes.proof
  · have start : Trunc.submission.run .check i=execute (Trunc.wireImage true) (Trunc.submission.steps .check) s false := by
      simp only [Submission.run,fits,decide_true,ite_true];rfl
    rw [start]
    have lengths : (s.getReg .x16*792=s.getReg .x17) ↔ i.proof.length=792*i.positions.card := by
      change (BitVec.ofNat 64 i.positions.card*BitVec.ofNat 64 792=BitVec.ofNat 64 i.proof.length) ↔ _
      change i.proof.length≤13421772800 at fits
      rw [←BitVec.ofNat_mul];constructor
      · intro e;have h:=congrArg BitVec.toNat e
        simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : i.positions.card*792<2^64),Nat.mod_eq_of_lt (by omega : i.proof.length<2^64)] at h
        omega
      · intro e;rw [e,Nat.mul_comm]
    by_cases good : i.proof.length=792*i.positions.card
    · obtain ⟨k,hk,q,hq,ex,fin,term,property⟩:=allRecords o i mode i.positions.card 0 (by omega) _ (initialFrame i)
      have fuel : 15+k≤Trunc.submission.steps .check := by change _≤1099511627776;omega
      have ctl : (checkLengthState s).pc=4144:=if_pos (lengths.mpr good)
      have gate : Batch.Runs o s (checkLengthState s) 12 0 :=
        Batch.pureBlockRuns (fun j=>check_length_gate s rfl diff j false)
      have enter : Batch.Runs o (checkLengthState s) (readyInput i) 3 0 :=
        Batch.pureBlockRuns (fun j=>check_ready _ ctl j false)
      have endRun:=runsThen (Batch.runs_trans gate enter) fin
      have endState:=endRun (Trunc.submission.steps .check-(15+k))
      rw [show 12+3+k+(Trunc.submission.steps .check-(15+k))=Trunc.submission.steps .check by omega] at endState
      unfold Batch.obs at endState
      change ((Late.Check.Normal.checkEvaluation o (execute _ _ s false)).1.exit,(Late.Check.Normal.checkEvaluation o (execute _ _ s false)).2)=(ex,0+0+q) at endState
      have exitEq : (Late.Check.Normal.checkEvaluation o (execute (Trunc.wireImage true) (Trunc.submission.steps .check) s false)).1.exit=ex:=congrArg Prod.fst endState
      have callsEq : (Late.Check.Normal.checkEvaluation o (execute (Trunc.wireImage true) (Trunc.submission.steps .check) s false)).2=q:=by simpa only [Nat.zero_add] using congrArg Prod.snd endState
      rw [exitEq,callsEq]
      exact ⟨term,hq,⟨fun yes=>⟨good,fun r hr=>property.mp yes r (Nat.zero_le _) hr⟩,
        fun h=>property.mpr (fun r _ hr=>h.2 r hr)⟩⟩
    · rw [show Trunc.submission.steps .check=15+(Trunc.submission.steps .check-15) by decide,check_wrong_length s rfl diff (fun e=>good (lengths.mp e)),Late.Check.Normal.check_evaluation_pure]
      simp [good]
  · have no : Trunc.submission.run .check i=pure ⟨.failure,initialMachine,0,0⟩ := by simp [Submission.run,fits]
    rw [no,Late.Check.Normal.check_evaluation_pure]
    have bad : i.proof.length≠792*i.positions.card := by intro eq;apply fits;change i.proof.length≤13421772800;omega
    simp [bad]

end CommitGolfCandidate.Trunc.Normal
