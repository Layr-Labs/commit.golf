import CommitGolfCandidate.S5Binding
namespace CommitGolfCandidate.S5.Replay
open CommitGolf OracleComp OracleSpec
open Chained (Input Output)
open Chained.Replay (recordRows PublicRow record_rows_pure record_rows_bind record_rows_query fixed_oracle_run_bind fixed_oracle_run_map)
def rows (H : Compression) (qs : List Input) :=qs.map fun q=>PublicRow.compression q (H q)
structure Code (n : Nat) (α : Type) where
  program : OracleComp World α
  value : Compression → α
  inputs : Compression → List Input
  cost : PublicQueryBound program n
  correct : ∀ o : Oracle,fixedOracleRun o (recordRows program)=pure (value o.compression,rows o.compression (inputs o.compression))

def done {α : Type} (a : α) : Code 0 α :=
  ⟨pure a,fun _=>a,fun _=>[],by trivial,fun o=>by rw [record_rows_pure,fixed_oracle_run_pure];rfl⟩
def ask (q : Input) : Code 1 Output where
  program:=Late.hash q
  value H:=H q
  inputs _:=[q]
  cost:=⟨le_rfl,fun _=>trivial⟩
  correct o:=by
    have unfoldQuery : Late.hash q=((liftM (World.query (.inr (.inl q))) : OracleComp World Output) >>= fun v=>pure v) := (bind_pure _).symm
    rw [unfoldQuery]
    erw [record_rows_query (.inr (.inl q)) (fun v=>pure v),fixed_oracle_run_public]
    simp only [record_rows_pure,map_pure,fixed_oracle_run_pure];rfl

def join {α β : Type} {a b : Nat} (x : Code a α) (k : α→Code b β) : Code (a+b) β where
  program:=x.program >>= fun val=>(k val).program
  value H:=(k (x.value H)).value H
  inputs H:=x.inputs H++(k (x.value H)).inputs H
  cost:=public_query_bound_bind x.cost (fun val=>(k val).cost)
  correct o:=by
    rw [record_rows_bind,fixed_oracle_run_bind,x.correct,pure_bind,fixed_oracle_run_bind,(k (x.value o.compression)).correct,pure_bind,fixed_oracle_run_pure]
    apply congrArg (fun qs : List PublicRow=>(pure ((k (x.value o.compression)).value o.compression,qs) : ProbComp _))
    exact List.map_append.symm
def widen {α : Type} {a b : Nat} (x : Code a α) (bound : a≤b) : Code b α :=
  ⟨x.program,x.value,x.inputs,x.cost.mono bound,x.correct⟩
def map {α β : Type} {a : Nat} (f : α→β) (x : Code a α) : Code a β:=join x (fun z=>done (f z))
theorem map_inputs {α β : Type} {n : Nat} (f : α→β) (x : Code n α) (H : Compression) :
    (map f x).inputs H=x.inputs H:=List.append_nil _
def tabulate {α : Type} (empty : α) {bound : Nat} (f : Nat→Code bound α) : (n : Nat)→Code (n*bound) (Nat→α)
  | 0=>widen (done (fun _=>empty)) (by omega)
  | n+1=>widen (join (tabulate empty f n) (fun table=>map (fun x i=>if i=n then x else table i) (f n))) (by rw [Nat.succ_mul])
theorem tab_value {α : Type} (empty : α) {bound : Nat} (f : Nat→Code bound α) (n j : Nat) (H : Compression) :
    (tabulate empty f n).value H j=if j<n then (f j).value H else empty := by
  induction n with
  | zero=>simp [tabulate,widen,done]
  | succ n ih=>
    change (if j=n then (f n).value H else (tabulate empty f n).value H j)=_;rw [ih];split_ifs <;> first | rfl | subst_vars;rfl | omega

def foreach {α : Type} {bound : Nat} (f : α→Code bound Unit) : (xs : List α) → Code (xs.length*bound) Unit
  | []=>widen (done ()) (by simp)
  | x::xs=>widen (join (f x) (fun _=>foreach f xs)) (by simp only [List.length_cons,Nat.succ_mul];omega)
theorem foreach_mem {α : Type} {bound : Nat} (f : α→Code bound Unit) (xs : List α) (H : Compression) {x : α}
    (inside : x∈xs) {q : Input} (read : q∈(f x).inputs H) : q∈(foreach f xs).inputs H := by
  induction xs with
  | nil=>simp at inside
  | cons y ys ih=>
    change q∈(f y).inputs H++(foreach f ys).inputs H
    rcases List.mem_cons.mp inside with eq|tail
    · subst x;exact List.mem_append_left _ read
    · exact List.mem_append_right _ (ih tail)
end CommitGolfCandidate.S5.Replay
