import CommitGolfCandidate.R1bExpressions
namespace CommitGolfCandidate.R1b.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open R1bPC (pcAt)
theorem preserved (ops : List Sym.Calc) (r : Reg) (f : Reg→Sym.Expr)
    (untouched : ∀ c∈ops,c.dst≠r) : (ops.foldl Sym.bump f) r=f r := by
  induction ops generalizing f with
  | nil=>rfl
  | cons c cs ih=>
    rw [List.foldl_cons,ih (Sym.bump f c) (fun a b=>untouched a (List.mem_cons_of_mem _ b))]
    exact if_neg (untouched c (List.mem_cons_self ..))
theorem calcGiven (site : Nat) (c : Code) (xs : List Sym.Calc) (s : MachineState) (pc : s.pc=pcAt site)
    (small : site+xs.length≤c.count) (words : Matches c site (xs.map Sym.Calc.instr))
    (nz : ∀ a∈xs,a.dst≠.x0) (valid : ∀ e∈Sym.requirements Sym.original xs,accessValid (e.1.eval s) e.2=true) :
    let t:=Sym.evaluated xs s
    Runs c s t xs.length (Sym.price xs) ∧ (∀ r,t.getReg r=((xs.foldl Sym.bump Sym.original) r).eval s) ∧
      t.mem=s.mem ∧ t.pc=pcAt (site+xs.length) := by
  have origin : Sym.live s s Sym.original:=by intro r;cases r <;> rfl
  exact Sym.evaluate_block c xs site s s Sym.original origin rfl pc small nz valid (fun j bj=>by
    have h:=words j (by simpa only [List.length_map] using bj);simpa only [List.getElem_map] using h)

theorem liveOriginal (s : MachineState) (r : Reg) : (Sym.original r).eval s=s.getReg r := by cases r <;> rfl

def registersPreserved (xs : List Sym.Calc) (allowed : List Reg) := xs.all fun op=>allowed.contains op.dst
theorem outsideCalc (xs : List Sym.Calc) (s t : MachineState)
    (regs : ∀ r,t.getReg r=((xs.foldl Sym.bump Sym.original) r).eval s) (allowed : List Reg)
    (writers : registersPreserved xs allowed) (r : Reg) (away : r∉allowed) : t.getReg r=s.getReg r := by
  rw [regs,preserved xs r Sym.original (fun op member e=>away (e ▸ (List.contains_iff_mem.mp (List.all_eq_true.mp writers op member))))]
  exact liveOriginal s r

def calcCode (xs : List Sym.Calc) := xs.map Sym.Calc.instr

theorem calcRegs (c : Code) (s : MachineState) (ops : List Sym.Calc) (pc : Nat) (site : s.pc=pcAt pc)
    (bound : pc+ops.length≤c.count) (code : Matches c pc (calcCode ops))
    (nz : ops.all (fun op=>op.dst != .x0)=true) (reads : Sym.requirements Sym.original ops=[]) :
    let t:=Sym.evaluated ops s
    Runs c s t ops.length (Sym.price ops) ∧ (∀ r,t.getReg r=((ops.foldl Sym.bump Sym.original) r).eval s) ∧
      t.mem=s.mem ∧ t.pc=pcAt (pc+ops.length) :=
  calcGiven pc c ops s site bound code (fun op h=>bne_iff_ne.mp (List.all_eq_true.mp nz op h))
    (fun _ h=>by rw [reads] at h;cases h)

end CommitGolfCandidate.R1b.Machine
