import CommitGolfCandidate.ReconstructedHonestPhysical
import CommitGolfCandidate.ReconstructedHonestRecordShapes

namespace CommitGolfCandidate.Reconstruction.HonestFlagEffect
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open HonestRanges HonestRegionStep HonestProtected HonestMemoryRanges
open CommitBlocks (addr)

abbrev base : Nat := 4259840
def flags : Range := ⟨base,base+1023⟩
def leaves : Range := ⟨base+512,base+1023⟩
def Effect (s t : MachineState) (mark : Option Word) :=
  ∀ q, Contains flags q → t.getByte q = if mark=some q then 1 else s.getByte q

def Valid : Option Word → Prop
  | some p => Contains leaves p
  | none => True

theorem reflexive (s : MachineState) : Effect s s none := by intro q _; rfl

theorem follow {s t u : MachineState} {m : Option Word} (pre : Effect s t none) (next : Effect t u m) :
    Effect s u m := by
  intro q inside
  rw [next q inside,pre q inside]
  rfl

def markTest (a : Abstract) : Instruction → Bool
  | .base (.SB ptr value off) => narrow (addressRange (a.regs ptr) off) leaves && singleton (a.regs value)==some 1
  | _ => false

theorem marked (im : Image) (s : MachineState) (coins : Bool) (a : Abstract) (op : Instruction)
    (meaning : Models s a) (read : fetch im s=some op) (test : markTest a op=true)
    (out : Execution) (run : out∈support (execute im 1 s coins)) (cont : out.exit=.unfinished) :
    ∃ q, Valid (some q) ∧ Effect s out.state (some q) := by
  cases op with
  | word _ _ _ _ | sraiw _ _ _ => cases test
  | base op =>
    cases op <;> try cases test
    rename_i ptr source off
    simp only [markTest,Bool.and_eq_true,beq_iff_eq] at test
    let p := s.getReg ptr+signExtend12 off
    have bounded := weaken test.1 (address_ok (meaning.1 ptr) off)
    have val := singleton_ok (meaning.1 source) test.2
    have step := HonestAbstract.continued_step im s _ coins read (by simp) out run cont
    simp only [ordinaryStep,Option.ite_none_right_eq_some,Option.some.injEq] at step
    refine ⟨p,bounded,?_⟩
    intro q inside
    rw [step.2.symm]
    change (s.setByte p ((s.getReg source).truncate 8)).getByte q = _
    rw [set_byte_read,val]
    by_cases same : q=p
    · subst q; simp only [ite_true]; rfl
    · simp only [ite_eq_right same,Option.some.injEq,ite_eq_right (Ne.symm same)]

/-- Independently of the data values, each 3,633-bit record can set at most one
leaf occupancy byte. The checker also enforces that a segment observing such
a write ends at the outer record boundary. -/
def check (clock : Nat) (pc : Word) (a : Abstract) (marked : Bool) : Bool :=
  match clock with
  | 0 => false
  | k+1 =>
    match HonestBlocks.readOp Artifact.openingCode pc with
    | none => false
    | some op =>
      let hit := pc == addr 135
      HonestRegionBlocks.callable a op && HonestFlow.direct op &&
      (if hit then !marked && markTest a op else (writes a op).all (HonestPhysical.misses flags)) &&
      (HonestAbstract.destinations pc (exactFile a.regs) op).all (fun target =>
        if HonestRecordShapes.stopAt target then !(marked || hit) || HonestRecordCost.cut target
        else check k target (advance a op) (marked || hit))

private theorem splitPath {im : Image} {coins : Bool} {cut : Word→Bool} {s t : MachineState}
    (walk : HonestCuts.Reaches im coins cut s t) : ∃ out, out∈support (execute im 1 s coins) ∧
    out.exit=.unfinished ∧ ((cut out.state.pc=true ∧ t=out.state) ∨
      (cut out.state.pc=false ∧ HonestCuts.Reaches im coins cut out.state t)) := by
  cases walk with
  | hit a b c => exact ⟨_,a,b,Or.inl ⟨c,rfl⟩⟩
  | more a b c d => exact ⟨_,a,b,Or.inr ⟨c,d⟩⟩

set_option maxRecDepth 32768
attribute [local irreducible] ArtifactEncoding.decode

theorem sound (clock : Nat) (pc : Word) (a : Abstract) (origin s t : MachineState) (m : Option Word)
    (valid : Valid m) (old : Effect origin s m) (cert : check clock pc a m.isSome=true)
    (coins : Bool) (entry : s.pc=pc) (meaning : Models s a)
    (walk : HonestCuts.Reaches (Artifact.submission.image .opening) coins HonestRecordShapes.stopAt s t) :
    ∃ event, Valid event ∧ Effect origin t event ∧ (event.isSome=true → HonestRecordCost.cut t.pc=true) := by
  induction clock generalizing pc a s m with
  | zero => cases cert
  | succ k ih =>
    cases opAt : HonestBlocks.readOp Artifact.openingCode pc with
    | none => simp [check,opAt] at cert
    | some op =>
      simp only [check,opAt,Bool.and_eq_true] at cert
      obtain ⟨⟨⟨call,dir⟩,write⟩,edges⟩ := cert
      have pub : op=.base .ECALL → s.getReg .x5=0 := by
        rintro rfl
        simp only [HonestRegionBlocks.callable,isQuery,Bool.not_true,Bool.false_or,beq_iff_eq] at call
        exact singleton_ok (meaning.1 _) call
      obtain ⟨out,run,cont,rest⟩ := splitPath walk
      have read := HonestBlocks.fetch_op Artifact.openingCode (Artifact.submission.image .opening)
        (Eq.refl (ArtifactEncoding.decode 32 _)) (by decide) s op (entry ▸ opAt)
      obtain ⟨target,next⟩ := one _ _ coins a op meaning read dir pub out run cont
      rw [entry] at target
      have edge := List.all_eq_true.mp edges _ target
      have stepEffect : ∃ m', Valid m' ∧ Effect origin out.state m' ∧ m'.isSome=(m.isSome || pc==addr 135) := by
        cases hit : (pc==addr 135) with
        | true =>
          simp only [hit,ite_true,Bool.and_eq_true,Bool.not_eq_true'] at write
          have empty : m=none := by cases m <;> simp_all
          subst m
          obtain ⟨q,inRange,change⟩ := marked _ s coins a _ meaning read write.2 out run cont
          exact ⟨some q,inRange,follow old change,rfl⟩
        | false =>
          simp only [hit,Bool.false_eq_true,ite_false] at write
          exact ⟨m,valid,(by
            intro q inside
            rw [HonestPhysical.same_bytes _ s coins a op meaning read pub out run cont flags write q inside]
            exact old q inside),by simp⟩
      obtain ⟨m',allowed,action,isSome⟩ := stepEffect
      rcases rest with ⟨stop,rfl⟩|⟨inside,more⟩
      · simp only [stop,ite_true,←isSome,Bool.or_eq_true,Bool.not_eq_true'] at edge
        exact ⟨m',allowed,action,by intro h; rcases edge with no|yes; simp_all; exact yes⟩
      · simp only [inside,Bool.false_eq_true,ite_false,←isSome] at edge
        exact ih _ _ _ m' allowed action edge rfl next more

end CommitGolfCandidate.Reconstruction.HonestFlagEffect
