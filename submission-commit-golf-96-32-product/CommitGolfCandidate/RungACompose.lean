import CommitGolfCandidate.RungAArithmetic
import CommitGolfCandidate.RungAReadSet
import CommitGolfCandidate.S4OpeningLaw
set_option Elab.async false
namespace CommitGolfCandidate.RungA
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open S4.Open (ReadyAtOne Resumed initial)
private abbrev commit := Late.submission.image .commit
private abbrev sub := program commit image
def RebuildRun (o : Oracle) (td : Late.Trapdoor) (ps : Positions) : Prop :=
  ∃ s n c,DetRun o image (initial td ps) n s c (publicCalls .twentyFour ps) ∧
    n≤260*ps.card+50 ∧ (ps.card=BATCH → c≤70822) ∧ WriterEntry .twentyFour commit image o td ps s

private structure Complete (o : Oracle) (td : Late.Trapdoor) (ps : Positions) (e : Execution) : Prop where
  run : o.run (sub.run .opening (td,ps))=pure (e,publicCalls .twentyFour ps)
  exit : e.exit=.success
  succeeded : sub.openingSucceeded e=true
  counted : e.oracleCalls=publicCalls .twentyFour ps
  price : ps.card=BATCH → e.cycles≤136043
  bytes : ∀ m r,FusedTrapdoor .twentyFour o m r td → sub.readProof e=S4.actualOpening (tree o m r) (R4.pairSalts r) ps

private theorem rawABI (td : Late.Trapdoor) (ps : Positions) :
    sub.run .opening (td,ps)=execute image 1099511627776 (initial td ps) true:=by
  have abi (c : Submission) (a : BitVec (8*c.sizes.trapdoor)) :
    c.run .opening (a,ps)=execute (c.image .opening) (c.steps .opening) (c.initialState .opening (a,ps)) true:=rfl
  exact abi sub td

attribute [local irreducible] execute
private theorem complete {o td ps} (pre : RebuildRun o td ps) : ∃ e, Complete o td ps e := by
  obtain ⟨s,n,c,path,maxSteps,price,after,built,pc,regs,mem⟩:=pre
  have k : ps.card≤16777216:=by change ps.card≤LENGTH;simpa using Finset.card_le_univ ps
  have entry : ReadyAtOne after ps s:=⟨pc,regs,mem⟩
  let remaining:=1099511627776-n
  have fuel : 1099511627776=n+remaining:=by dsimp [remaining];omega
  have suffix : ∃ e,Resumed after ps s remaining e ∧ (ps.card=BATCH → e.cycles≤65221):=by
    by_cases batch:ps.card=BATCH
    · obtain ⟨e,run,cy⟩:=S4.Open.batchResumed after ps batch s entry remaining (by omega)
      exact ⟨e,run,fun _=>cy.le⟩
    · obtain ⟨e,run⟩:=S4.Open.ordinaryResumed after ps batch s entry remaining (by omega)
      exact ⟨e,run,fun h=>(batch h).elim⟩
  obtain ⟨e,tail,cy⟩:=suffix
  let q:=publicCalls .twentyFour ps
  refine ⟨e.charge c q,⟨?_,tail.exit,tail.success,?_,?_,?_⟩⟩
  · rw [rawABI,fuel,path remaining,tail.run,oracle_run_pure,map_pure];simp only [Nat.add_zero];rfl
  · change q+e.oracleCalls=q;rw [tail.noCalls,Nat.add_zero]
  · intro batch;change c+e.cycles≤136043;have:=price batch;have:=cy batch;omega
  · intro m r h;exact tail.bytes.trans (writerBytes h built)

noncomputable def openingOfPrelude (run : ∀ o td ps, RebuildRun o td ps) : RungAOpening commit image where
  result o td ps := (complete (run o td ps)).choose
  run o td ps := (complete (run o td ps)).choose_spec.run
  exit o td ps := (complete (run o td ps)).choose_spec.exit
  succeeded o td ps := (complete (run o td ps)).choose_spec.succeeded
  counted o td ps := (complete (run o td ps)).choose_spec.counted
  price o td ps := (complete (run o td ps)).choose_spec.price
  bytes o m r td ps h := (complete (run o td ps)).choose_spec.bytes m r h

theorem publicCalls24 (ps : Positions) : publicCalls .twentyFour ps =
    38*ps.card-11*(ps.filter (fun (i : Index) => (16777200 : Nat) ≤ i.val)).card := by
  classical
  suffices he : publicCalls .twentyFour ps+11*(ps.filter (fun (i : Index) => (16777200 : Nat) ≤ i.val)).card=38*ps.card by omega
  induction ps using Finset.induction_on with
  | empty=>simp [publicCalls]
  | @insert i ps hi ih=>
    have p:=perIndex_exact .twentyFour i
    change perIndex .twentyFour i=38-(if i.val≥16777200 then 11 else 0) at p
    unfold publicCalls at *
    rw [Finset.sum_insert hi, Finset.card_insert_of_notMem hi]
    by_cases last : (16777200 : Nat) ≤ i.val
    · simp only [Finset.filter_insert,if_pos last] 
      rw [Finset.card_insert_of_notMem (fun h=>hi (Finset.mem_filter.mp h).1)]
      rw [if_pos last] at p
      change perIndex _ i + ps.sum (perIndex .twentyFour) + 11*(_+1)=_ 
      rw [p,Nat.mul_add,Nat.mul_add,←ih];omega
    · simp only [Finset.filter_insert,if_neg last]
      rw [if_neg last] at p
      change perIndex _ i + ps.sum (perIndex .twentyFour) + 11*_=_
      rw [p,Nat.mul_add,←ih];omega
end CommitGolfCandidate.RungA
