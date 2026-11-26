import CommitGolfCandidate.S5OpenSetup
import CommitGolfCandidate.S5TableLoop
namespace CommitGolfCandidate.S5Machine.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def commonRegs : List Reg := [.x8,.x9,.x18,.x19,.x20,.x21,.x23,.x24,.x26,.x27,.x22,.x25]
theorem SeedRegs.congr {b k s t} (h : SeedRegs b k s) (keep : ∀ r∈commonRegs,t.getReg r=s.getReg r) : SeedRegs b k t := by
  constructor
  · exact (keep _ (by decide)).trans h.base
  · exact (keep _ (by decide)).trans h.indices
  · exact (keep _ (by decide)).trans h.start
  · exact (keep _ (by decide)).trans h.dest
  · exact (keep _ (by decide)).trans h.salts
  · exact fun yes=>(keep _ (by decide)).trans (h.marks yes)
  · exact fun yes=>⟨(keep _ (by decide)).trans (h.pending yes).1,(keep _ (by decide)).trans (h.pending yes).2⟩
  · exact fun yes=>⟨(keep _ (by decide)).trans (h.constants yes).1,(keep _ (by decide)).trans (h.constants yes).2⟩
  · exact fun no=>(keep _ (by decide)).trans (h.count no)
  · exact (keep _ (by decide)).trans h.radix

def loadGP : Bool→PathCode
  | true=>[(20,.JAL .x0 88),(42,.LUI .x3 1),(43,.ADDI .x3 .x3 2048)]
  | false=>[(400,.LUI .x3 1),(401,.ADDI .x3 .x3 2048)]

theorem prepare_table (b : Bool) (s : MachineState) (pc : s.pc=pcAt (if b then 20 else 400)) :
    let t:=pathEnd s (loadGP b)
    Runs s t (loadGP b).length (loadGP b).length ∧ t.pc=pcAt (if b then 44 else 402) ∧
    t.getReg .x3=W 2048 ∧ t.mem=s.mem ∧ (∀ r∈commonRegs,t.getReg r=s.getReg r) := by
  have ok : pathReady s (loadGP b) ∧ (pathEnd s (loadGP b)).pc=pcAt (if b then 44 else 402) ∧
    (pathEnd s (loadGP b)).getReg .x3=W 2048 ∧ (pathEnd s (loadGP b)).mem=s.mem := by
    cases b <;> simp +decide [loadGP,pathReady,pathEnd,execInstrBr,ordinaryStep,memAccess,memoryArgumentsValid,
      MachineState.getReg,MachineState.setReg,MachineState.setPC,signExtend12,signExtend21,pc,pcAt,W]
  have sites : (loadGP b).all (matchesWord .opening) := by cases b <;> decide +kernel
  refine ⟨path_run _ true _ _ sites ok.1,ok.2.1,ok.2.2.1,ok.2.2.2,?_⟩
  intro r mem
  cases b <;> cases r <;> simp [commonRegs] at mem <;> rfl

theorem enter_open (s : MachineState) (k : Nat) (nonempty : 0<k) (bounded : k≤LENGTH) (pc : s.pc=pcAt 0)
    (td : s.getReg .x12=W tdBase) (ix : s.getReg .x13=W indexBase) (out : s.getReg .x15=W proofBase) (count : s.getReg .x16=W k) :
    let b:=decide (k=128)
    ∃ t,Runs s t (if b then 117 else 113) (if b then 117 else 113) ∧ t.pc=pcAt (if b then 143 else 501) ∧
      SeedRegs b k t ∧ t.getReg .x3=W 2048 ∧ (∀ j<25,wordAt t (tableSlot j)=W (tdBase+levelOffset j)) ∧ Outside s t 2048 200 := by
  let b:=decide (k=128)
  let a:=pathEnd s (dispatch b)
  let u:=openSetup b a
  let v:=pathEnd u (loadGP b)
  have small : k<18446744073709551616 := by change k≤16777216 at bounded;omega
  have nz : s.getReg .x16 ≠ 0 := by rw [count];intro e;have h:=congrArg BitVec.toNat e;simp [W,Nat.mod_eq_of_lt small] at h;omega
  have flag : (s.getReg .x16==128)=b := by
    rw [count];by_cases yes : k=128
    · simp [yes,W,b]
    · have neq : W k≠128#64 := by intro e;have h:=congrArg BitVec.toNat e;simp [W,Nat.mod_eq_of_lt small] at h;omega
      simp [b,yes,neq]
  obtain ⟨r₁,p₁,m₁,f₁⟩:=dispatch_run s pc nz b flag
  obtain ⟨r₂,p₂,m₂⟩:=setup_run a b p₁
  have seed:=setup_regs a b k ((f₁ _ (by decide)).trans td) ((f₁ _ (by decide)).trans ix)
    ((f₁ _ (by decide)).trans out) ((f₁ _ (by decide)).trans count)
  obtain ⟨r₃,p₃,gp,m₃,f₃⟩:=prepare_table b u p₂
  have before:=seed.congr f₃
  obtain ⟨r₄,p₄,tab,keeps,frame⟩:=table_complete v b p₃ before.base gp
  have price : ∀ v : Bool,(dispatch v).length+(setupList v).length+(loadGP v).length+99=(if v then 117 else 113) := by decide
  have joined:=((r₁.trans r₂).trans r₃).trans r₄
  rw [price] at joined
  refine ⟨_,joined,p₄,before.congr (fun r mem=>keeps r (by intro e;subst r;exact (by decide : Reg.x6∉commonRegs) mem)),
    (keeps _ (by decide)).trans gp,tab,?_⟩
  intro q h al away
  exact (frame q h al away).trans (show wordAt v q=wordAt s q by
    simp only [wordAt,MachineState.getMem,show v.mem=s.mem from m₃.trans (m₂.trans m₁)])
end CommitGolfCandidate.S5Machine.Open
