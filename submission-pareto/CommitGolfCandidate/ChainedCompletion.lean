import CommitGolfCandidate.ChainedGraphHazard

/-! Completions predicted from the old graph and the next input, before its reply. -/
namespace CommitGolfCandidate.Chained

namespace Evaluation
variable {enc : Encoding} {calls : Height → Nat} {trace : Trace}

def lift (e : Evaluation enc calls trace) (input : Input) (output : Output)
    (fresh : ∀ i, trace.input i ≠ input) : Evaluation enc calls (trace.append input output fresh) where
  height := e.height
  seed := e.seed
  positive := e.positive
  bounded := e.bounded
  row j := (e.row j).castSucc
  first := by
    simpa only [Trace.append,extend,Fin.val_castSucc,dif_pos (e.row 0).isLt] using e.first
  next j inside := by
    simpa only [Trace.append,extend,Fin.val_castSucc,dif_pos (e.row j).isLt,
      dif_pos (e.row (j+1)).isLt] using e.next j inside

theorem row_eq_of_identity (e f : Evaluation enc calls trace) (same : e.identity = f.identity)
    (j : Nat) (inside : j < calls e.height) : e.row j = f.row j := by
  have heights : e.height = f.height := congrArg Prod.fst same
  have seeds : e.seed = f.seed := congrArg Prod.snd same
  induction j with
  | zero =>
    apply trace.fresh
    rw [e.first,f.first,heights,seeds]
  | succ j ih =>
    have other : j+1 < calls f.height := by simpa only [heights] using inside
    apply trace.fresh
    rw [e.next j inside,f.next j other,heights,ih (by omega)]

variable {input : Input} {output : Output} {fresh : ∀ i, trace.input i ≠ input}

theorem nonfinal_old (e : Evaluation enc calls (trace.append input output fresh))
    (good : Good enc (trace.append input output fresh)) (j : Nat)
    (inside : j+1 < calls e.height) : (e.row j).val < trace.size := by
  have order := e.ordered good j inside
  have range : (e.row (j+1)).val < trace.size+1 := (e.row (j+1)).isLt
  omega

def changeReply (e : Evaluation enc calls (trace.append input output fresh)) (reply : Output)
    (earlier : ∀ j, j+1 < calls e.height → (e.row j).val < trace.size) :
    Evaluation enc calls (trace.append input reply fresh) where
  height := e.height
  seed := e.seed
  positive := e.positive
  bounded := e.bounded
  row := e.row
  first := e.first
  next j inside := by
    have relation := e.next j inside
    simpa only [Trace.append,extend,dif_pos (earlier j inside)] using relation

theorem old_row (e : Evaluation enc calls (trace.append input output fresh))
    (good : Good enc (trace.append input output fresh))
    (lastOld : (e.row (calls e.height-1)).val < trace.size)
    (j : Nat) (inside : j < calls e.height) : (e.row j).val < trace.size := by
  by_cases next : j+1 < calls e.height
  · exact e.nonfinal_old good j next
  · have last : j = calls e.height-1 := by omega
    simpa only [last] using lastOld

def oldIndex (e : Evaluation enc calls (trace.append input output fresh))
    (good : Good enc (trace.append input output fresh))
    (lastOld : (e.row (calls e.height-1)).val < trace.size) (j : Nat) : Fin trace.size :=
  if inside : j < calls e.height then ⟨(e.row j).val,e.old_row good lastOld j inside⟩
  else ⟨(e.row 0).val,e.old_row good lastOld 0 e.positive⟩

theorem oldIndex_input (e : Evaluation enc calls (trace.append input output fresh))
    (good : Good enc (trace.append input output fresh))
    (lastOld : (e.row (calls e.height-1)).val < trace.size) (j : Nat) (inside : j < calls e.height) :
    trace.input (e.oldIndex good lastOld j) = (trace.append input output fresh).input (e.row j) := by
  unfold oldIndex
  rw [dif_pos inside]
  change trace.input _ = extend trace.input input (e.row j)
  dsimp only [extend]
  rw [dif_pos (e.old_row good lastOld j inside)]

theorem oldIndex_output (e : Evaluation enc calls (trace.append input output fresh))
    (good : Good enc (trace.append input output fresh))
    (lastOld : (e.row (calls e.height-1)).val < trace.size) (j : Nat) (inside : j < calls e.height) :
    trace.output (e.oldIndex good lastOld j) = (trace.append input output fresh).output (e.row j) := by
  unfold oldIndex
  rw [dif_pos inside]
  change trace.output _ = extend trace.output output (e.row j)
  dsimp only [extend]
  rw [dif_pos (e.old_row good lastOld j inside)]

def restrict (e : Evaluation enc calls (trace.append input output fresh))
    (good : Good enc (trace.append input output fresh))
    (lastOld : (e.row (calls e.height-1)).val < trace.size) : Evaluation enc calls trace where
  height := e.height
  seed := e.seed
  positive := e.positive
  bounded := e.bounded
  row := e.oldIndex good lastOld
  first := (e.oldIndex_input good lastOld 0 e.positive).trans e.first
  next j inside := by
    rw [e.oldIndex_input good lastOld (j+1) inside,e.next j inside,
      e.oldIndex_output good lastOld j (by omega)]

end Evaluation

structure Prospective (enc : Encoding) (calls : Height → Nat) (trace : Trace) (input : Input)
    (fresh : ∀ i, trace.input i ≠ input) where
  evaluation : Evaluation enc calls (trace.append input 0 fresh)
  last : evaluation.row (calls evaluation.height-1) = Fin.last trace.size
  earlier : ∀ j, j+1 < calls evaluation.height → (evaluation.row j).val < trace.size

namespace Prospective
variable {enc : Encoding} {calls : Height → Nat} {trace : Trace} {input : Input}
  {fresh : ∀ i, trace.input i ≠ input}

def identity (p : Prospective enc calls trace input fresh) : Height × Seed := p.evaluation.identity

def evaluate (p : Prospective enc calls trace input fresh) (reply : Output) :
    Evaluation enc calls (trace.append input reply fresh) := p.evaluation.changeReply reply p.earlier

def ofEvaluation {reply : Output} (e : Evaluation enc calls (trace.append input reply fresh))
    (good : Good enc (trace.append input reply fresh))
    (last : e.row (calls e.height-1) = Fin.last trace.size) : Prospective enc calls trace input fresh where
  evaluation := e.changeReply 0 (e.nonfinal_old good)
  last := last
  earlier := e.nonfinal_old good

theorem fresh_identity (p : Prospective enc calls trace input fresh) (e : Evaluation enc calls trace) :
    p.identity ≠ e.identity := by
  intro same
  have inside : calls p.evaluation.height-1 < calls p.evaluation.height := by
    have := p.evaluation.positive
    omega
  have rows := p.evaluation.row_eq_of_identity (e.lift input 0 fresh) same _ inside
  rw [p.last] at rows
  have values := congrArg (fun i : Fin (trace.size+1) => i.val) rows
  change trace.size = (e.row _).val at values
  have := (e.row (calls p.evaluation.height-1)).isLt
  omega

end Prospective

def Completed (enc : Encoding) (calls : Height → Nat) (trace : Trace) (id : Height × Seed) : Prop :=
  ∃ e : Evaluation enc calls trace, e.identity = id

theorem completion_step {enc : Encoding} {calls : Height → Nat} {trace : Trace}
    {input : Input} {fresh : ∀ i, trace.input i ≠ input} (reply : Output)
    (good : Good enc (trace.append input reply fresh)) (id : Height × Seed) :
    Completed enc calls (trace.append input reply fresh) id ↔
      Completed enc calls trace id ∨ ∃ p : Prospective enc calls trace input fresh, p.identity = id := by
  constructor
  · rintro ⟨e,same⟩
    by_cases old : (e.row (calls e.height-1)).val < trace.size
    · exact Or.inl ⟨e.restrict good old,same⟩
    · have range : (e.row (calls e.height-1)).val < trace.size+1 := (e.row _).isLt
      have last : e.row (calls e.height-1) = Fin.last trace.size := Fin.ext (by simp; omega)
      exact Or.inr ⟨Prospective.ofEvaluation e good last,same⟩
  · rintro (⟨e,same⟩ | ⟨p,same⟩)
    · exact ⟨e.lift input reply fresh,same⟩
    · exact ⟨p.evaluate reply,same⟩

theorem exists_safe_output (enc : Encoding) (trace : Trace) (small : 2*trace.size < 2^256) :
    ∃ reply : Output, reply ∉ badTargets enc trace := by
  classical
  by_contra! full
  have all : badTargets enc trace = Finset.univ := Finset.eq_univ_of_forall full
  have card := badTargets_card enc trace
  rw [all,Finset.card_univ,show Fintype.card Output = 2^256 by simp] at card
  omega

theorem prospective_unique {enc : Encoding} {calls : Height → Nat} {trace : Trace}
    {input : Input} {fresh : ∀ i, trace.input i ≠ input} (good : Good enc trace)
    (small : 2*trace.size < 2^256) (p q : Prospective enc calls trace input fresh) :
    p.identity = q.identity := by
  obtain ⟨reply,safe⟩ := exists_safe_output enc trace small
  have extended := good_append enc trace good input reply fresh safe
  have pi : calls p.evaluation.height-1 < calls p.evaluation.height := by have := p.evaluation.positive; omega
  have qi : calls q.evaluation.height-1 < calls q.evaluation.height := by have := q.evaluation.positive; omega
  exact Evaluation.identity_eq_of_shared extended (p.evaluate reply) (q.evaluate reply) _ _ pi qi
    (p.last.trans q.last.symm)

end CommitGolfCandidate.Chained
