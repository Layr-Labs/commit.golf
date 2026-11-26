import CommitGolfCandidate.ReconstructedCheckRecorded

namespace CommitGolfCandidate.Reconstruction.CheckValues
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxHeartbeats 900000

/-- A relocated address. Numbered regions let callers choose nonoverlapping
physical frame, input and output areas. Region zero is absolute memory. -/
structure Loc where
  region : Nat
  offset : Word
  deriving BEq,DecidableEq,Repr

inductive Bin where
  | add | bitOr | bitAnd | bitXor | shl | shr | add32 | sub32 | remu
  deriving BEq,DecidableEq,Repr

def Bin.run : Bin → Word → Word → Word
  | .add,x,y => x+y
  | .bitOr,x,y => x ||| y
  | .bitAnd,x,y => x &&& y
  | .bitXor,x,y => x ^^^ y
  | .shl,x,y => x <<< (y.toNat%64)
  | .shr,x,y => x >>> (y.toNat%64)
  | .add32,x,y => (x.truncate 32+y.truncate 32).signExtend 64
  | .sub32,x,y => (x.truncate 32-y.truncate 32).signExtend 64
  | .remu,x,y => rv64_remu x y

inductive Term where
  | lit (x : Word)
  | ptr (loc : Loc)
  | reg (r : Reg)
  | old (a : Loc)
  | answer (query word : Nat)
  | bin (op : Bin) (x y : Term)
  deriving BEq,DecidableEq,Repr

structure Env where
  initial : MachineState
  base : Nat → Word
  zero : base 0=0
  answer : Nat → Nat → Word

def physical (env : Env) (a : Loc) := env.base a.region + a.offset

def Term.val (env : Env) : Term → Word
  | .lit w => w
  | .ptr a => physical env a
  | .reg r => env.initial.getReg r
  | .old a => env.initial.getMem (physical env a)
  | .answer n i => env.answer n i
  | .bin op x y => op.run (x.val env) (y.val env)

def applyOp (op : Bin) (x y : Term) : Term :=
  match op,x,y with
  | op,.lit a,.lit b => .lit (op.run a b)
  | .add,.ptr a,.lit n | .add,.lit n,.ptr a => .ptr {a with offset:=a.offset+n}
  | .add,t,.lit 0 | .add,.lit 0,t => t
  | op,x,y => .bin op x y

theorem op_sound (env : Env) (op : Bin) (x y : Term) :
    (applyOp op x y).val env = op.run (x.val env) (y.val env) := by
  unfold applyOp
  split <;> simp_all [Term.val,Bin.run,physical,BitVec.add_assoc,BitVec.add_comm]

def address : Term → Option Loc
  | .lit x => some ⟨0,x⟩
  | .ptr a => some a
  | _ => none

theorem address_sound {t : Term} {a : Loc} (env : Env) (h : address t=some a) : physical env a=t.val env := by
  cases t <;> simp [address] at h <;> subst a <;> simp [physical,env.zero,Term.val]

structure Tables where
  allowed : Loc→Bool
  initial : Loc→Option Word

structure Layout (env : Env) (tab : Tables) : Prop where
  safe : ∀ a, tab.allowed a=true → accessValid (physical env a) 8=true
  unique : ∀ a b, tab.allowed a=true → tab.allowed b=true → physical env a=physical env b → a=b
  table : ∀ a w, tab.initial a=some w → env.initial.getMem (physical env a)=w

abbrev Writes := List (Loc×Term)

def look (tab : Tables) (a : Loc) : Writes → Term
  | [] => match tab.initial a with | some w=>.lit w | none=>.old a
  | (b,x)::xs => if a=b then x else look tab a xs

def memory (env : Env) (p : Word) : Writes→Word
  | [] => env.initial.getMem p
  | (b,x)::xs => if p=physical env b then x.val env else memory env p xs

def Safe (tab : Tables) (xs : Writes) := ∀ v∈xs, tab.allowed v.1=true

theorem look_sound (env : Env) (tab : Tables) (layout : Layout env tab) (xs : Writes) (a : Loc)
    (valid : tab.allowed a=true) (ok : Safe tab xs) :
    (look tab a xs).val env = memory env (physical env a) xs := by
  induction xs with
  | nil =>
    simp only [look,memory]
    split <;> rename_i h
    · exact (layout.table _ _ h).symm
    · rfl
  | cons v rest ih =>
    obtain ⟨b,x⟩ := v
    by_cases eq : a=b
    · subst b;simp [look,memory]
    · have ne : physical env a ≠ physical env b :=
        fun h => eq (layout.unique _ _ valid (ok (b,x) (by simp)) h)
      simp only [look,eq,ite_false,memory,ne]
      exact ih (fun w h=>ok w (List.mem_cons_of_mem _ h))

structure State where
  regs : Reg→Term
  writes : Writes
  pc : Word

def State.get (s : State) (r : Reg) := if r=.x0 then Term.lit 0 else s.regs r
def State.set (s : State) (r : Reg) (v : Term) : State :=
  {s with regs := fun k => if k=r then v else s.regs k}

structure Matches (env : Env) (m : State) (s : MachineState) : Prop where
  pc : s.pc=m.pc
  regs : ∀ r, s.getReg r=(m.get r).val env
  mem : ∀ q, s.getMem q=memory env q m.writes

theorem set_value (env : Env) (m : State) (s : MachineState) (h : Matches env m s)
    (r : Reg) (x : Term) (p : Word) :
    Matches env {m.set r x with pc:=p} ((s.setReg r (x.val env)).setPC p) := by
  refine ⟨rfl,?_,?_⟩
  · intro t;rw [MachineState.getReg_setPC]
    by_cases t0 : t=.x0
    · subst t;simp [State.get,Term.val,MachineState.getReg]
    by_cases same : t=r
    · subst r
      simp [State.get,State.set,t0,MachineState.getReg_setReg_eq t0]
    · rw [MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm same),h.regs]
      simp [State.get,State.set,same]
  · intro q;cases r <;> exact h.mem q

theorem set_word (env : Env) (m : State) (s : MachineState) (h : Matches env m s)
    (a : Loc) (x : Term) (p : Word) :
    Matches env {m with writes:=(a,x)::m.writes,pc:=p} ((s.setMem (physical env a) (x.val env)).setPC p) := by
  refine ⟨rfl,h.regs,?_⟩
  intro t
  by_cases eq : t=physical env a
  · subst t;change (s.setMem (physical env a) (x.val env)).getMem (physical env a)=_
    rw [MachineState.getMem_setMem_eq];simp [memory]
  · change (s.setMem (physical env a) (x.val env)).getMem t=_
    rw [MachineState.getMem_setMem_ne eq,h.mem];simp [memory,eq]

theorem set_pc (env : Env) (m : State) (s : MachineState) (h : Matches env m s) (p : Word) :
    Matches env {m with pc:=p} (s.setPC p) := ⟨rfl,h.regs,h.mem⟩

end CommitGolfCandidate.Reconstruction.CheckValues
