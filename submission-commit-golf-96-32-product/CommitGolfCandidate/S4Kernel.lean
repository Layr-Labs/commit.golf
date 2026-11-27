import CommitGolfCandidate.S4CompareLoop
import CommitGolfCandidate.S4Load
import CommitGolfCandidate.S4FieldExpr
namespace CommitGolfCandidate.S4.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (pcAt)
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
  rw [regs,Open.preserved xs r Sym.original (fun op member e=>away (e ▸ (List.contains_iff_mem.mp (List.all_eq_true.mp writers op member))))]
  exact liveOriginal s r

theorem pcOffset {c : Code} {site : Nat} {a b : List Instr} (h : Matches c site (a++b)) (n : Nat) (e : a.length=n) :
    Matches c (site+n) b:=e ▸ h.right

def checkedCopies (n : Nat) := doubleCopies .x14 .x15 0 0 n
def transferN (s : MachineState) (n : Nat) := copyBlock .x14 .x15 0 0 (dwords n) s
theorem copyN (s : MachineState) (site src dst n : Nat) (pc : s.pc=pcAt site)
    (bound : site+2*n≤Code.check.count) (code : Matches .check site (checkedCopies n))
    (r1 : s.getReg .x14=W src) (r2 : s.getReg .x15=W dst)
    (al : src%8=0) (dl : dst%8=0) (small : 8*n≤256) (bs : src+8*n≤MEMORY_BYTES) (bd : dst+8*n≤MEMORY_BYTES)
    (out : src+8*n≤dst ∨ dst+8*n≤src) :
    AfterCopy .check site s (transferN s n) src dst (8*n) (2*n) :=
  dwordBlock .check s .x14 .x15 site src dst 0 0 n (by decide) (by decide) pc bound code r1 r2 al dl (by simpa only [Nat.zero_add] using small) (by simpa only [Nat.zero_add] using small) bs bd out

end CommitGolfCandidate.S4.Machine
