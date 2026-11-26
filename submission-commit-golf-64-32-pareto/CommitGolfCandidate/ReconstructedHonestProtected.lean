import CommitGolfCandidate.ReconstructedHonestRegionStep

namespace CommitGolfCandidate.Reconstruction.HonestProtected
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 HonestRanges HonestMemoryRanges HonestRegionStep

/-- Addresses in each inclusive zone have a fixed abstract description across
the entire loop. Scratch spill slots are represented separately. -/
structure Context where
  zones : List Range
  fixed : Word → Range
  slots : List Word

def protects (c : Context) (q : Word) := c.zones.any (fun z => z.lo≤q.toNat && q.toNat≤z.hi)
def disjoint (c : Context) (w : Range) := c.zones.all (fun z => z.hi+7<w.lo || w.hi<z.lo)

private theorem disjoint_ok {c : Context} {w : Range} {q : Word} (safe : disjoint c w=true)
    (present : protects c q=true) : away w q=true := by
  obtain ⟨z,member,inside⟩ := List.any_eq_true.mp present
  have outside := List.all_eq_true.mp safe _ member
  simp only [Bool.and_eq_true,decide_eq_true_eq] at inside
  simp only [Bool.or_eq_true,decide_eq_true_eq] at outside
  simp only [away,Bool.or_eq_true,decide_eq_true_eq]
  omega

def writes (a : Abstract) (op : Instruction) : Option Range :=
  if isQuery op then some (wrap (a.regs .x12).lo ((a.regs .x12).hi+199))
  else (store op).map (fun w => addressRange (a.regs w.base) w.offset)

def safe (c : Context) (a : Abstract) (op : Instruction) : Bool :=
  (writes a op).all (disjoint c)

theorem unchanged (c : Context) (a : Abstract) (s : MachineState) (op : Instruction)
    (meaning : Models s a) (checked : safe c a op=true) (q : Word) (old : protects c q=true) :
    (advance a op).ram q=a.ram q := by
  cases call : isQuery op with
  | true =>
    simp only [safe,writes,call,ite_true,Option.all_some] at checked
    simp only [advance,call,ite_true,afterQuery,disjoint_ok checked old]
  | false =>
    cases desc : store op with
    | none => simp only [advance,call,Bool.false_eq_true,ite_false,heapAfter,desc]
    | some w =>
      simp only [safe,writes,call,Bool.false_eq_true,ite_false,desc,Option.map_some,Option.all_some] at checked
      have out := disjoint_ok checked old
      have contained := address_ok (meaning.1 w.base) w.offset
      have miss : ¬(w.whole && singleton (addressRange (a.regs w.base) w.offset) == some q) = true := by
        intro hit
        simp only [Bool.and_eq_true,beq_iff_eq] at hit
        exact (away_ok _ _ _ contained out).1 (singleton_ok contained hit.2).symm
      simp only [advance,call,Bool.false_eq_true,ite_false,heapAfter,desc,ite_eq_right miss,out,ite_true]

abbrev RegFacts := List (Reg × Range)
abbrev MemFacts := List (Word × Range)

def lookup {ι : Type} [DecidableEq ι] (xs : List (ι × Range)) (k : ι) : Range :=
  match xs with
  | [] => any
  | (r,v)::tail => if r=k then v else lookup tail k

def RegFacts.hold (s : MachineState) (xs : RegFacts) := ∀ r v, (r,v)∈xs → Contains v (s.getReg r)
def MemFacts.hold (s : MachineState) (xs : MemFacts) := ∀ q v, (q,v)∈xs → Contains v (s.getMem q)

private theorem lookup_ok {ι : Type} [DecidableEq ι] (xs : List (ι × Range)) (get : ι → Word)
    (ok : ∀ k v, (k,v)∈xs → Contains v (get k)) (k : ι) : Contains (lookup xs k) (get k) := by
  induction xs with
  | nil => exact arbitrary _
  | cons head tail ih =>
    rcases head with ⟨r,v⟩
    simp only [lookup]
    split
    · rename_i eq; subst r; exact ok _ _ List.mem_cons_self
    · exact ih (fun _ _ mem => ok _ _ (List.mem_cons_of_mem _ mem))

structure Shape where
  regs : RegFacts
  cells : MemFacts

def Shape.model (c : Context) (a : Shape) : Abstract := ⟨lookup a.regs,fun q =>
  if protects c q then c.fixed q else lookup a.cells q⟩

def Holds (c : Context) (a : Shape) (s : MachineState) :=
  RegFacts.hold s a.regs ∧ MemFacts.hold s a.cells ∧ ∀ q, protects c q=true → Contains (c.fixed q) (s.getMem q)

theorem models_shape {s : MachineState} {c : Context} {a : Shape} (holds : Holds c a s) :
    Models s (a.model c) := by
  refine ⟨lookup_ok _ _ holds.1,fun q => ?_⟩
  simp only [Shape.model]; split
  · exact holds.2.2 _ (by assumption)
  · exact lookup_ok _ _ holds.2.1 _

def fits (a : Abstract) (b : Shape) := b.regs.all (fun (r,v) => narrow (a.regs r) v) &&
  b.cells.all (fun (q,v) => narrow (a.ram q) v)

theorem fits_ok {s : MachineState} {a : Abstract} {b : Shape} (ok : Models s a) (test : fits a b=true) :
    RegFacts.hold s b.regs ∧ MemFacts.hold s b.cells := by
  simp only [fits,Bool.and_eq_true] at test
  obtain ⟨regs,cells⟩ := test
  exact ⟨fun r v mem => weaken (List.all_eq_true.mp regs (r,v) mem) (ok.1 r),
    fun q v mem => weaken (List.all_eq_true.mp cells (q,v) mem) (ok.2 q)⟩

end CommitGolfCandidate.Reconstruction.HonestProtected
