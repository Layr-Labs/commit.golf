import CommitGolfCandidate.RungADraw
import CommitGolfCandidate.RungAUniform
import CommitGolfCandidate.R4CommitBase
import CommitGolfCandidate.RungAInterface
namespace CommitGolfCandidate.RungA
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec
set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
attribute [local irreducible] execute readBuffer

private theorem selectedRun (ref : Submission) (m : Message) :
    ({ref with image:=fun | .commit=>ref.image .commit | .opening=>ref.image .opening | .check=>ref.image .check} : Submission).run .commit m =
    ref.run .commit m := rfl

private theorem fuelForm (s : Submission) (m : Message) (steps : Nat) (same : s.steps .commit=steps) :
    s.run .commit m=execute (s.image .commit) steps (s.initialState .commit m) true := by
  rw [←same];rfl

theorem commitLaw_of_suffix (price : Nat) (hpp : 58721306≤price)
    (suffix : FixedTapeCommit .twentyFour (R4.submission.image .commit) price) :
    CommitLaw .twentyFour (R4.submission.image .commit) (Late.submission.image .opening) price := by
  intro o m
  let fuel:=2^40-16778266
  obtain ⟨init,pre,valid⟩:=draw o m fuel
  have det (r : Tape):=suffix o m r (init r) (valid r)
  let state (r : Tape):=(det r).choose
  refine ⟨state,?_,fun r=>(det r).choose_spec.1⟩
  have end_ (r : Tape) : o.run (execute (R4.submission.image .commit) fuel (init r) true)=
      pure (commitExec (price-58721306) (state r),commitCalls):=(det r).choose_spec.2
  have chosen : (program (R4.submission.image .commit) (Late.submission.image .opening)).run .commit m =
      R4.submission.run .commit m:=selectedRun Late.submission m
  have countedFuel : R4.submission.steps .commit=16778266+fuel := by
    change 1099511627776=16778266+(1099511627776-16778266)
    omega
  rw [chosen,fuelForm R4.submission m (16778266+fuel) countedFuel]
  exact uniform o _ _ _ init state price hpp pre end_
end CommitGolfCandidate.RungA
