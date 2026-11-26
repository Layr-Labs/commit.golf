import CommitGolfCandidate.ReconstructedHonestCapStages

namespace CommitGolfCandidate.Reconstruction.HonestCapCursor
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp HonestFlow HonestCuts
open CommitBlocks (addr)

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
attribute [local irreducible] ArtifactEncoding.decode

/-- Additive expressions over a segment's initial registers. Each cursor
increment is certified for all 64-bit starting counters simultaneously. -/
inductive Expr where
  | reg (r : Reg)
  | word (w : Word)
  | add (a b : Expr)
  deriving DecidableEq

def eval (s : MachineState) : Expr → Word
  | .reg r => s.getReg r
  | .word w => w
  | .add a b => eval s a+eval s b

abbrev File := Reg → Option Expr
def Meaning (entry s : MachineState) (m : File) := ∀ r e, m r=some e → s.getReg r=eval entry e

def next (m : File) (op : Instruction) (r : Reg) : Option Expr :=
  if r=.x0 then some (.word 0) else if writesReg op r then
    match op with
    | .base (.ADD _ a b) => match m a,m b with
      | some u,some v => some (.add u v)
      | _,_ => none
    | .base (.ADDI _ a n) => match m a with
      | some u => some (.add u (.word (signExtend12 n)))
      | none => none
    | _ => none
  else m r

theorem next_ok (e s t : MachineState) (m : File) (op : Instruction) (stable : Meaning e s m)
    (step : ordinaryStep s op=some t) : Meaning e t (next m op) := by
  intro r expr has
  by_cases zero : r=.x0
  · subst r; simp only [next,ite_true,Option.some.injEq] at has; subst expr; rfl
  · cases changed : writesReg op r with
    | false =>
      rw [ordinary_step_keeps _ _ _ _ step changed]
      exact stable _ _ (by simpa only [next,ite_eq_right zero,changed,Bool.false_eq_true,ite_false] using has)
    | true =>
      simp only [next,ite_eq_right zero,changed,ite_true] at has
      cases op with
      | word _ _ _ _ | sraiw _ _ _ => cases has
      | base op =>
        cases op <;> try cases has
        case ADD d a b =>
          have eq : d=r := by simpa only [writesReg,beq_iff_eq] using changed
          subst d
          cases u : m a <;> simp [u] at has
          cases v : m b <;> simp [v] at has
          subst expr
          simp only [ordinaryStep,memoryArgumentsValid,memAccess,ite_true,Option.some.injEq] at step
          subst t; simp only [execInstrBr,MachineState.getReg_setPC,MachineState.getReg_setReg_eq zero,eval,
            stable _ _ u,stable _ _ v]
        case ADDI d a n =>
          have eq : d=r := by simpa only [writesReg,beq_iff_eq] using changed
          subst d
          cases u : m a <;> simp [u] at has
          subst expr
          simp only [ordinaryStep,memoryArgumentsValid,memAccess,ite_true,Option.some.injEq] at step
          subst t; simp only [execInstrBr,MachineState.getReg_setPC,MachineState.getReg_setReg_eq zero,eval,
            stable _ _ u]

def keep (m : File) (r : Reg) : Option Expr := if r=.x7 ∨ r=.x23 then m r else none

def initial : File := keep (fun r => some (.reg r))
def check (expected : Expr) : Nat → Word → File → Bool
  | 0,_,_ => false
  | k+1,pc,m => match HonestBlocks.readOp Artifact.openingCode pc with
    | none => false
    | some op => HonestBlocks.plain op && direct op &&
      (targets pc op).all (fun target =>
        let file := keep (next m op)
        if HonestCapStages.stops target then decide (file .x7=some expected)
        else check expected k target file)

private theorem sound (entry : MachineState) (expected : Expr) (k : Nat) (pc : Word) (m : File)
    (checked : check expected k pc m=true) (s t : MachineState) (coins : Bool) (loc : s.pc=pc)
    (meaning : Meaning entry s m) (walk : Reaches (Artifact.submission.image .opening) coins HonestCapStages.stops s t) :
    t.getReg .x7=eval entry expected := by
  induction k generalizing pc m s with
  | zero => cases checked
  | succ k ih =>
    cases decoded : HonestBlocks.readOp Artifact.openingCode pc with
    | none => simp [check,decoded] at checked
    | some op =>
      simp only [check,decoded,Bool.and_eq_true] at checked
      obtain ⟨⟨plain,dir⟩,edges⟩ := checked
      have noCall : op≠.base .ECALL := by rintro rfl; cases plain
      have read := HonestBlocks.fetch_op Artifact.openingCode (Artifact.submission.image .opening)
        (Eq.refl (ArtifactEncoding.decode 32 _)) (by decide) s op (loc ▸ decoded)
      have hop (r : Execution) (run : r∈support (execute (Artifact.submission.image .opening) 1 s coins))
          (cont : r.exit=.unfinished) : r.state.pc ∈ targets pc op ∧ Meaning entry r.state (keep (next m op)) := by
        have route := ((charged_successors _ _ _ _ read dir (fun a => (noCall a).elim) r run).2 cont).1
        rw [loc] at route
        refine ⟨route,?_⟩
        intro x term test
        simp only [keep] at test
        split at test
        · exact next_ok entry s r.state m op meaning (HonestAbstract.continued_step _ _ _ _ read noCall r run cont) _ _ test
        · cases test
      cases walk with
      | @hit _ r run cont stop =>
        obtain ⟨target,held⟩ := hop r run cont
        have edge := List.all_eq_true.mp edges r.state.pc target
        simp only [stop,ite_true,decide_eq_true_eq] at edge
        exact held _ _ edge
      | @more _ _ r run cont inside tail =>
        obtain ⟨target,held⟩ := hop r run cont
        have edge := List.all_eq_true.mp edges r.state.pc target
        simp only [inside,Bool.false_eq_true,ite_false] at edge
        exact ih _ _ edge _ rfl held tail

private theorem initial_meaning (s : MachineState) : Meaning s s initial := by
  intro r e h
  simp only [initial,keep] at h
  split at h
  · obtain rfl := Option.some.inj h; rfl
  · cases h

theorem emit (s t : MachineState) (coins : Bool) (pc : s.pc=addr 1512)
    (walk : Reaches (Artifact.submission.image .opening) coins HonestCapStages.stops s t) :
    t.getReg .x7=s.getReg .x7+192+s.getReg .x23 := by
  exact sound s (.add (.add (.reg .x7) (.word 192)) (.reg .x23)) 59 (addr 1512) initial
    (by decide +kernel) s t coins pc (initial_meaning s) walk

theorem flush (s t : MachineState) (coins : Bool) (pc : s.pc=addr 1626)
    (walk : Reaches (Artifact.submission.image .opening) coins HonestCapStages.stops s t) :
    t.getReg .x7=s.getReg .x7+31 := by
  exact sound s (.add (.reg .x7) (.word 31)) 19 (addr 1626) initial
    (by decide +kernel) s t coins pc (initial_meaning s) walk

end CommitGolfCandidate.Reconstruction.HonestCapCursor
