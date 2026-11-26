import CommitGolfCandidate.S4Kernel
import CommitGolfCandidate.S4Address
namespace CommitGolfCandidate.S4.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (pcAt)
def digits (tern : Bool) : List Sym.Calc :=
  if tern then [.remu .x1 .x20 .x23,.divu .x20 .x20 .x23] else [.andi .x1 .x20 1,.srli .x20 .x20 1]
def rotate (tern : Bool) : List Sym.Calc :=
  if tern then [.addi .x1 .x1 1,.remu .x1 .x1 .x23] else [.xori .x1 .x1 1]
def radixOf (tern : Bool) := if tern then 3 else 2
def calcCode (xs : List Sym.Calc) := xs.map Sym.Calc.instr

theorem calcRegs (c : Code) (s : MachineState) (ops : List Sym.Calc) (pc : Nat) (site : s.pc=pcAt pc)
    (bound : pc+ops.length≤c.count) (code : Matches c pc (calcCode ops))
    (nz : ops.all (fun op=>op.dst != .x0)=true) (reads : Sym.requirements Sym.original ops=[]) :
    let t:=Sym.evaluated ops s
    Runs c s t ops.length (Sym.price ops) ∧ (∀ r,t.getReg r=((ops.foldl Sym.bump Sym.original) r).eval s) ∧
      t.mem=s.mem ∧ t.pc=pcAt (pc+ops.length) :=
  calcGiven pc c ops s site bound code (fun op h=>bne_iff_ne.mp (List.all_eq_true.mp nz op h))
    (fun _ h=>by rw [reads] at h;cases h)

theorem digitsRun (tern : Bool) (o : Oracle) (s : MachineState) (n j : Nat) (pc : s.pc=pcAt n)
    (bound : n+2≤Code.check.count) (code : Matches .check n (calcCode (digits tern)))
    (index : s.getReg .x20=W j) (small : j<2^64) (three : s.getReg .x23=3) :
    let t:=Sym.evaluated (digits tern) s
    CheckRuns o s t 2 0 ∧ t.pc=pcAt (n+2) ∧ t.mem=s.mem ∧
    t.getReg .x20=W (j/radixOf tern) ∧ t.getReg .x1=W (j%radixOf tern) ∧
    ∀ r,r≠.x20 → r≠.x1 → t.getReg r=s.getReg r := by
  have len : (digits tern).length=2:=by cases tern <;> rfl
  obtain ⟨run,regs,mem,last⟩:=calcRegs .check s (digits tern) n pc (len.symm ▸ bound) code
    (by cases tern <;> decide) (by cases tern <;> rfl)
  rw [len] at run last
  refine ⟨ofRuns o run,last,mem,?_,?_,?_⟩
  · apply (regs .x20).trans;cases tern
    · change s.getReg .x20 >>> 1=W (j/2);rw [index];exact shr j 1 small
    · change rv64_divu (s.getReg .x20) (s.getReg .x23)=_;rw [three,index];exact divThree j small
  · apply (regs .x1).trans;cases tern
    · change s.getReg .x20 &&& 1=W (j%2);rw [index];exact parity j
    · change rv64_remu (s.getReg .x20) (s.getReg .x23)=_;rw [three,index];exact modThree j small
  · intro r a b
    exact outsideCalc _ s _ regs [.x20,.x1] (by cases tern <;> rfl) r (by simpa using And.intro a b)

theorem rotateRun (tern : Bool) (o : Oracle) (s : MachineState) (n j : Nat) (pc : s.pc=pcAt n)
    (bound : n+(rotate tern).length≤Code.check.count) (code : Matches .check n (calcCode (rotate tern)))
    (index : s.getReg .x1=W j) (small : j<radixOf tern) (three : s.getReg .x23=3) :
    let t:=Sym.evaluated (rotate tern) s
    CheckRuns o s t (rotate tern).length 0 ∧ t.pc=pcAt (n+(rotate tern).length) ∧ t.mem=s.mem ∧
    t.getReg .x1=W ((j+1)%radixOf tern) ∧ ∀ r,r≠.x1 → t.getReg r=s.getReg r := by
  obtain ⟨run,regs,mem,last⟩:=calcRegs .check s (rotate tern) n pc bound code (by cases tern <;> decide) (by cases tern <;> rfl)
  refine ⟨ofRuns o run,last,mem,?_,?_⟩
  · apply (regs .x1).trans;cases tern
    · change j<2 at small;change s.getReg .x1 ^^^ 1=W ((j+1)%2)
      rw [index];interval_cases j <;> rfl
    · change j<3 at small;change rv64_remu (s.getReg .x1+1) (s.getReg .x23)=W ((j+1)%3)
      rw [index,three,oneMore];exact modThree _ (by omega)
  · intro r a;exact outsideCalc _ s _ regs [.x1] (by cases tern <;> rfl) r (by simpa)
end CommitGolfCandidate.S4.Machine
