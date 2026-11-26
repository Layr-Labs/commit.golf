import CommitGolfCandidate.ReconstructedHonestWideShapes
import CommitGolfCandidate.ReconstructedHonestPhysical

namespace CommitGolfCandidate.Reconstruction.HonestWideKernel
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp HonestRanges HonestProtected HonestRegionStep HonestMemoryRanges
open HonestWideMemory (capacity context Frozen)
open HonestRecordMemory (idx)
open CommitBlocks (addr)

def indexRange : Range := ⟨idx,idx+8*capacity-1⟩
def indexLoad (a : Abstract) : Instruction→Option Reg
  | .base (.LD d b off) => if d≠.x0 ∧ narrow (addressRange (a.regs b) off) indexRange then some d else none
  | _ => none

def after (a : Abstract) (op : Instruction) : Abstract :=
  let b := advance a op
  ⟨fun r => if indexLoad a op=some r then ⟨0,capacity-1⟩ else b.regs r,b.ram⟩

theorem step {a : Abstract} {s : MachineState} (op : Instruction) (coins : Bool) (meaning : Models s a)
    (frozen : Frozen s) (read : fetch (Artifact.submission.image .opening) s=some op)
    (out : Execution) (run : out∈support (execute (Artifact.submission.image .opening) 1 s coins)) (alive : out.exit=.unfinished)
    (old : Models out.state (advance a op)) : Models out.state (after a op) := by
  refine ⟨?_,old.2⟩
  intro r; simp only [after]; split
  · rename_i matched
    cases op with
    | word _ _ _ _ | sraiw _ _ _ => cases matched
    | base op =>
      cases op <;> try cases matched
      rename_i d b off
      simp only [indexLoad,Option.ite_none_right_eq_some,Option.some.injEq] at matched
      obtain ⟨⟨nonzero,test⟩,rfl⟩ := matched
      have bound := weaken test (address_ok (meaning.1 b) off)
      have ordinary := HonestAbstract.continued_step _ s _ coins read (by simp) out run alive
      simp only [ordinaryStep,Option.ite_none_right_eq_some,Option.some.injEq] at ordinary
      have guard := ordinary.1
      simp only [memoryArgumentsValid,memAccess,accessValid,Bool.and_eq_true,decide_eq_true_eq] at guard
      rw [←ordinary.2]; simp only [execInstrBr,MachineState.getReg_setPC,MachineState.getReg_setReg_eq nonzero]
      exact HonestWideMemory.index_bound frozen _ guard.2 bound.1 (by have upper := bound.2; change _ ≤ idx+8*capacity-1 at upper; dsimp [idx,capacity] at *; omega)
  · exact old.1 _

def check (clock : Nat) (pc : Word) (a : Abstract) : Bool := match clock with
  | 0 => false
  | k+1 => match HonestBlocks.readOp Artifact.openingCode pc with
    | none => false
    | some op => HonestRegionBlocks.callable a op && HonestFlow.direct op && safe context a op &&
      (HonestAbstract.destinations pc (exactFile a.regs) op).all (fun target =>
        let b := after a op
        if HonestWideShapes.cut target then (HonestWideShapes.target target).any (fits b) else check k target b)

def checked (i : Nat) := match HonestWideShapes.current i with
  | none => true
  | some shape => check 64 (addr i) (shape.model context)

theorem protected_word (a : Abstract) (op : Instruction) (known : safe context a op=true) (q : Word)
    (has : protects context q=true) : (writes a op).all (fun w => away w q)=true := by
  cases eq : writes a op with
  | none => rfl
  | some w =>
    simp only [safe,eq,Option.all_some] at known
    obtain ⟨z,member,inside⟩ := List.any_eq_true.mp has
    have outside := List.all_eq_true.mp known _ member
    simp only [Bool.and_eq_true,decide_eq_true_eq] at inside
    simp only [Bool.or_eq_true,decide_eq_true_eq] at outside
    simp only [Option.all_some,away,Bool.or_eq_true,decide_eq_true_eq]
    omega

abbrev image := Artifact.submission.image .opening
abbrev Path (coins : Bool) := HonestCuts.Reaches image coins HonestWideShapes.cut

private theorem splitPath {coins : Bool} {s t : MachineState} (walk : Path coins s t) :
    ∃ out, out∈support (execute image 1 s coins) ∧ out.exit=.unfinished ∧ ((HonestWideShapes.cut out.state.pc=true ∧
      t=out.state) ∨ (HonestWideShapes.cut out.state.pc=false ∧ Path coins out.state t)) := by
  cases walk with
  | hit a b c => exact ⟨_,a,b,Or.inl ⟨c,rfl⟩⟩
  | more a b c d => exact ⟨_,a,b,Or.inr ⟨c,d⟩⟩

set_option maxRecDepth 32768
attribute [local irreducible] ArtifactEncoding.decode

/-- Every reached record cutpoint satisfies the next interval state, and all
protected ABI input and frame words retain their actual machine values. -/
theorem sound (clock : Nat) (pc : Word) (a : Abstract) (cert : check clock pc a=true)
    (s t : MachineState) (coins : Bool) (entry : s.pc=pc) (meaning : Models s a)
    (frozen : ∀ q, protects context q=true → a.ram q=context.fixed q) (walk : Path coins s t) :
    (∃ b, HonestWideShapes.target t.pc=some b ∧ Holds context b t) ∧
    ∀ q, protects context q=true → t.getMem q=s.getMem q := by
  induction clock generalizing pc a s with
  | zero => cases cert
  | succ k ih =>
    cases opAt : HonestBlocks.readOp Artifact.openingCode pc with
    | none => simp [check,opAt] at cert
    | some op =>
      simp only [check,opAt,Bool.and_eq_true] at cert
      obtain ⟨⟨⟨call,dir⟩,away⟩,edges⟩ := cert
      have pub : op=.base .ECALL → s.getReg .x5=0 := by
        rintro rfl
        simp only [HonestRegionBlocks.callable,isQuery,Bool.not_true,Bool.false_or,beq_iff_eq] at call
        exact singleton_ok (meaning.1 _) call
      obtain ⟨out,run,cont,rest⟩ := splitPath walk
      have read := HonestBlocks.fetch_op Artifact.openingCode image (Eq.refl (ArtifactEncoding.decode 32 _)) (by decide)
        s op (entry ▸ opAt)
      obtain ⟨dest,normal⟩ := one _ s coins a op meaning read dir pub out run cont
      have before : Frozen s := by
        intro q has; change Contains (context.fixed q) (s.getMem q); rw [←frozen q has]; exact meaning.2 q
      have next := step op coins meaning before read out run cont normal
      rw [entry] at dest
      have edge := List.all_eq_true.mp edges _ dest
      have keep (q : Word) (inside : protects context q=true) : (after a op).ram q=context.fixed q :=
        (unchanged context a s op meaning away q inside).trans (frozen q inside)
      have physical (q : Word) (inside : protects context q=true) : out.state.getMem q=s.getMem q :=
        HonestPhysical.unchanged _ s coins a op meaning read pub out run cont q (protected_word a op away q inside)
      rcases rest with ⟨stop,rfl⟩|⟨inside,more⟩
      · simp only [stop,ite_true] at edge
        cases lookup : HonestWideShapes.target out.state.pc with
        | none => simp [lookup] at edge
        | some b =>
          simp only [lookup,Option.any_some] at edge
          have facts := fits_ok next edge
          exact ⟨⟨b,rfl,facts.1,facts.2,fun q h => (keep q h) ▸ next.2 q⟩,physical⟩
      · simp only [inside,Bool.false_eq_true,ite_false] at edge
        obtain ⟨out,frame⟩ := ih _ _ edge _ rfl next keep more
        exact ⟨out,fun q h => (frame q h).trans (physical q h)⟩

end CommitGolfCandidate.Reconstruction.HonestWideKernel
