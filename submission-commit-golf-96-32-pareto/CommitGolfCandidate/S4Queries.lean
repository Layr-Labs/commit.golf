import CommitGolfCandidate.LateReplay
import CommitGolfCandidate.QueryBudget
namespace CommitGolfCandidate.S4
open CommitGolf OracleComp OracleSpec
open Late (Digest Block)
structure Queries (n : Nat) (α : Type) where
  code : OracleComp World α
  eval : Oracle → α
  runs : ∀ o,o.run code=pure (eval o,n)
  bound : IsTotalQueryBound code n

namespace Queries
def done {α : Type} (x : α) : Queries 0 α :=
  ⟨pure x,fun _=>x,fun o=>oracle_run_pure o x,by trivial⟩
def query (x : Block) : Queries 1 Digest :=
  ⟨Late.hash x,fun o=>o.compression x,fun o=>oracle_run_public o (.inl x),⟨Nat.zero_lt_one,fun _=>trivial⟩⟩

def join {n m : Nat} {α β : Type} (x : Queries n α) (k : α→Queries m β) : Queries (n+m) β where
  code:=x.code >>= fun v=>(k v).code
  eval o:=(k (x.eval o)).eval o
  runs o:=by simp only [oracle_run_bind,x.runs,pure_bind,(k (x.eval o)).runs]
  bound:=isTotalQueryBound_bind x.bound (fun v=>(k v).bound)
def map {n : Nat} {α β : Type} (f : α→β) (x : Queries n α) : Queries n β where
  code:=f <$> x.code
  eval o:=f (x.eval o)
  runs o:=by rw [oracle_run_map,x.runs,map_pure]
  bound:=by simpa only [IsTotalQueryBound,isQueryBound_map_iff] using x.bound
def retime {n m : Nat} {α : Type} (e : n=m) (x : Queries n α) : Queries m α :=
  ⟨x.code,x.eval,fun o=>by rw [←e];exact x.runs o,e ▸ x.bound⟩

/-- Compute all entries once, in increasing index order. Values outside the table are zero. -/
def table {c : Nat} (f : Nat→Queries c Digest) : (n : Nat) → Queries (n*c) (Nat→Digest)
  | 0=>retime (Nat.zero_mul c).symm (done (fun _ : Nat=>(0 : Digest)))
  | n+1=>retime (Nat.succ_mul n c).symm (join (table f n) (fun prior=>map (fun (v : Digest) (j : Nat)=>if j=n then v else prior j) (f n)))

theorem tableValue {c : Nat} (f : Nat→Queries c Digest) (n j : Nat) (o : Oracle) :
    (table f n).eval o j=if j<n then (f j).eval o else 0 := by
  induction n with
  | zero=>simp [table,retime,done]
  | succ n ih=>
    change (if j=n then (f n).eval o else (table f n).eval o j)=_
    rw [ih];split_ifs <;> first | rfl | subst_vars; rfl | omega
end Queries
end CommitGolfCandidate.S4
