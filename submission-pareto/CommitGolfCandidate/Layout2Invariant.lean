import CommitGolfCandidate.Layout2Blocks
import CommitGolfCandidate.Layout2Memory
import CommitGolfCandidate.GroupOpenSiblingRun

namespace CommitGolfCandidate.Layout2
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open TwoPermutationPrototype.GroupedOpening (halfword_of_bytes)
abbrev scratchBase : Nat := 4096
abbrev tableBase : Nat := 68719391296
abbrev proofBase : Nat := 13824430176

def Kept (except : List Reg) (s t : MachineState) := ∀ r, r∉except → t.getReg r=s.getReg r
theorem Kept.refl (rs : List Reg) (s : MachineState) : Kept rs s s := fun _ _=>rfl
theorem Kept.trans {rs s t u} (h : Kept rs s t) (g : Kept rs t u) : Kept rs s u :=
  fun r hr=>(g r hr).trans (h r hr)
theorem Kept.weaken {a b s t} (h : Kept a s t) (sub : ∀ r, r∈a → r∈b) : Kept b s t :=
  fun r hr=>h r (fun x=>hr (sub r x))

/-- All reads for a single table are 16-bit, aligned and bounded by RAM. -/
def Table (τ : Tables) (r tb : Nat) (s : MachineState) :=
  ∀ i, i < 4272*r → s.getHalfword (addr (tb+2*i))=BitVec.ofNat 16 (τ r i)
def TablesAt (τ : Tables) (s : MachineState) :=
  ∀ r, 1≤r → r≤4 → Table τ r (tableBase+tableOffset r) s
structure Config (τ : Tables) (r p tb : Nat) : Prop where
  positive : 1≤r
  small : r≤4
  separated : scratchBase+2136≤p
  tableAfter : p+534*r≤tb
  even : tb%2=0
  room : tb+2*(4272*r)≤MEMORY_BYTES
  well : WellFormed τ

theorem tableConfig (τ : Tables) (wf : WellFormed τ) (r p : Nat) (lo : 1≤r) (hi : r≤4)
    (room : p+534*r≤tableBase) (base : scratchBase+2136≤p) :
    Config τ r p (tableBase+tableOffset r) := by
  refine ⟨lo,hi,base,by omega,?_,?_,wf⟩ <;> first | exact wf | (interval_cases r <;> decide)

theorem Table.mem {τ r tb s t} (h : Table τ r tb s) (same : t.mem=s.mem) : Table τ r tb t := by
  intro i hi;simpa only [MachineState.getHalfword,MachineState.getMem,same] using h i hi

theorem Table.writes {τ r p tb s t base n data} (cfg : Config τ r p tb) (table : Table τ r tb s)
    (writes : Writes s t base n data) (below : base+n≤tb) : Table τ r tb t := by
  intro i hi
  have even:=cfg.even; have room:=cfg.room
  have bound : MEMORY_BYTES+16 ≤ 2^64 := by decide
  have eq:=halfword_of_bytes s t (tb+2*i) (by omega) (by omega)
    (writes.outside _ (by omega) (Or.inr (by omega)))
    (writes.outside _ (by omega) (Or.inr (by omega)))
  exact eq.trans (table i hi)

/-- Subroutine bounds independent of the outer V1 record format.
The caller selects the table bank, base addresses and byte count. -/
structure Span (τ : Tables) (tag p tb bytes : Nat) : Prop where
  nonempty : 0<bytes
  separated : scratchBase+bytes≤p
  tableAfter : p+bytes≤tb
  even : tb%2=0
  room : tb+2*(8*bytes)≤MEMORY_BYTES
  index : ∀ i, i<8*bytes → τ tag i<8*bytes ∧ τ tag i<65536

def SpanTable (τ : Tables) (tag tb bytes : Nat) (s : MachineState) :=
  ∀ i, i<8*bytes → s.getHalfword (addr (tb+2*i))=BitVec.ofNat 16 (τ tag i)

theorem Config.span {τ r p tb} (c : Config τ r p tb) : Span τ r p tb (534*r) := by
  have lo:=c.positive;have hi:=c.small;have gap:=c.separated;have room:=c.room
  refine ⟨by omega,by omega,c.tableAfter,c.even,by omega,?_⟩
  intro i bound
  have idx:=c.well r lo hi i (by omega);omega

theorem Table.span {τ r tb s} (h : Table τ r tb s) : SpanTable τ r tb (534*r) s :=
  fun i hi=>h i (by omega)

theorem SpanTable.mem {τ r tb bytes s t} (h : SpanTable τ r tb bytes s) (same : t.mem=s.mem) :
    SpanTable τ r tb bytes t := by
  intro i hi;simpa only [MachineState.getHalfword,MachineState.getMem,same] using h i hi

theorem SpanTable.writes {τ r p tb bytes s t base n data} (cfg : Span τ r p tb bytes)
    (table : SpanTable τ r tb bytes s) (writes : Writes s t base n data) (below : base+n≤tb) :
    SpanTable τ r tb bytes t := by
  intro i hi
  have even:=cfg.even;have room:=cfg.room;have lim : MEMORY_BYTES+16<2^64 := by decide
  exact (halfword_of_bytes s t _ (by omega) (by omega)
    (writes.outside _ (by omega) (Or.inr (by omega)))
    (writes.outside _ (by omega) (Or.inr (by omega)))).trans (table i hi)

theorem addr_add (a b : Nat) : addr a+addr b=addr (a+b) := (BitVec.ofNat_add ..).symm
theorem addr_ne {a b : Nat} (ha : a < 2^64) (hb : b < 2^64) : addr a≠addr b ↔ a≠b := by
  constructor
  · intro h eq;subst a;exact h rfl
  · intro h eq
    have f:=congrArg BitVec.toNat eq
    simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] at f
    exact h f

/-- Compose fixed-cost iterations while retaining a phase invariant on the concrete state. -/
theorem loop {I : Image} (N n c : Nat) (P : Nat → MachineState → Prop) (s : MachineState)
    (initial : P 0 s)
    (step : ∀ i, i<N → ∀ m, P i m → ∃ t, Runs I m t n c ∧ P (i+1) t) :
    ∃ t, Runs I s t (n*N) (c*N) ∧ P N t := by
  have go : ∀ k, k≤N → ∃ t, Runs I s t (n*k) (c*k) ∧ P k t := by
    intro k
    induction k with
    | zero => intro _;exact ⟨s,by simpa using runs_zero I s,initial⟩
    | succ k ih =>
      intro le
      obtain ⟨m,pre,inv⟩:=ih (by omega)
      obtain ⟨t,tail,out⟩:=step k (by omega) m inv
      exact ⟨t,by simpa only [Nat.mul_succ] using pre.thenDo tail,out⟩
  exact go N (Nat.le_refl _)

end CommitGolfCandidate.Layout2
