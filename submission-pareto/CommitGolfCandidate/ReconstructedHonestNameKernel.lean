import CommitGolfCandidate.ReconstructedHonestNameShapes
import CommitGolfCandidate.ReconstructedHonestFlagState

namespace CommitGolfCandidate.Reconstruction.HonestNameKernel
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp HonestRanges HonestProtected HonestRegionStep HonestMemoryRanges
open HonestWideKernel (image Path)
open HonestWideMemory (context Frozen)
open HonestNames
open CommitBlocks (addr)

set_option maxRecDepth 32768
attribute [local irreducible] ArtifactEncoding.decode

def holds (v : Values) (shape : HonestNameShapes.Shape) (s : MachineState) :=
  (∀ r x, (r,x)∈shape.regs → s.getReg r=eval v x) ∧ (∀ q x, (q,x)∈shape.mem → s.getMem q=eval v x)

private theorem found {α : Type} [DecidableEq α] (ls : List (α×Term)) (k : α) (x : Term)
    (h : HonestNameShapes.find ls k=some x) : (k,x)∈ls := by
  induction ls with
  | nil => cases h
  | cons p ls ih =>
    obtain ⟨key,val⟩ := p; simp only [HonestNameShapes.find] at h
    split at h
    · rename_i e; obtain rfl := Option.some.inj h; subst key; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

theorem model {v : Values} {shape : HonestNameShapes.Shape} {s : MachineState} (given : holds v shape s) :
    Means v s shape.model := ⟨fun r x h => given.1 _ _ (found _ _ _ h),fun q x h => given.2 _ _ (found _ _ _ h)⟩

def fits (b : Names) (shape : HonestNameShapes.Shape) := shape.regs.all (fun (r,x) => b.regs r==some x) &&
  shape.mem.all (fun (q,x) => b.mem q==some x)

private theorem fit_ok {v : Values} {shape : HonestNameShapes.Shape} {s : MachineState} {b : Names}
    (known : Means v s b) (ok : fits b shape=true) : holds v shape s := by
  simp only [fits,Bool.and_eq_true] at ok
  exact ⟨fun r x h => known.1 _ _ (beq_iff_eq.mp (List.all_eq_true.mp ok.1 (r,x) h)),
    fun q x h => known.2 _ _ (beq_iff_eq.mp (List.all_eq_true.mp ok.2 (q,x) h))⟩

abbrev leafTerm : Term := ⟨.leaf,4259840⟩
def markAddr (v : Values) := eval v leafTerm
def seen (k : Nat) := [136,139,141,142].contains k
def doneAt (q : Word) := let j := HonestBinaryRank.index q; j==143 || j==1429 || seen j
def guardOK (i : Nat) (q : Word) := let j := HonestBinaryRank.index q
  if j=143 ∨ j=142 then decide (i=141) else if j=1429 then decide (i=142) else true

def markTest (a : Abstract) (b : Names) : Instruction→Bool
  | .base (.SB ptr val off) => off==0 && value a b ptr==some leafTerm && singleton (a.regs val)==some 1
  | _ => false

private theorem mark {a : Abstract} {b : Names} {v : Values} {s : MachineState} (op : Instruction) (coins : Bool)
    (numeric : Models s a) (names : Means v s b) (read : fetch image s=some op) (test : markTest a b op=true)
    (out : Execution) (run : out∈support (execute image 1 s coins)) (alive : out.exit=.unfinished) :
    HonestFlagEffect.Effect s out.state (some (markAddr v)) := by
  cases op with
  | word _ _ _ _ | sraiw _ _ _ => cases test
  | base op =>
    cases op <;> try cases test
    rename_i ptr src off
    simp only [markTest,Bool.and_eq_true,beq_iff_eq] at test
    obtain ⟨⟨rfl,pos⟩,unit⟩ := test
    have step := HonestAbstract.continued_step _ s _ coins read (by simp) out run alive
    simp only [ordinaryStep,Option.ite_none_right_eq_some,Option.some.injEq] at step
    intro q inside; rw [←step.2]
    change (s.setByte (s.getReg ptr+signExtend12 0) ((s.getReg src).truncate 8)).getByte q=_
    rw [set_byte_read,value_ok numeric names pos,singleton_ok (numeric.1 _) unit]
    change (if q=markAddr v+0#64 then (1#64).truncate 8 else s.getByte q)=_
    simp only [BitVec.add_zero,Option.some.injEq]
    by_cases eq : q=markAddr v
    · subst q; rfl
    · simp only [ite_eq_right eq,ite_eq_right (Ne.symm eq)]

def check (start clock : Nat) (pc : Word) (a : Abstract) (b : Names) (marked : Bool) : Bool := match clock with
  | 0 => false
  | k+1 => match HonestBlocks.readOp Artifact.openingCode pc with
    | none => false
    | some op =>
      let hit := pc==addr 135
      HonestRegionBlocks.callable a op && HonestFlow.direct op && safe context a op &&
      (if hit then !marked && markTest a b op else (writes a op).all (HonestPhysical.misses HonestFlagEffect.flags)) &&
      (HonestAbstract.destinations pc (exactFile a.regs) op).all (fun q =>
        let b' := HonestNames.next a b op
        if HonestWideShapes.cut q then fits b' (HonestNameShapes.target q) && (marked || hit)==doneAt q && guardOK start q
        else check start k q (HonestWideKernel.after a op) b' (marked || hit))

def checked (i : Nat) := match HonestWideShapes.current i with
  | none => true
  | some shape => check i 64 (addr i) (shape.model context) (HonestNameShapes.current i).model (seen i)

def event (v : Values) (marked : Bool) := if marked then some (markAddr v) else none

private theorem splitPath {coins : Bool} {s t : MachineState} (walk : Path coins s t) :
    ∃ out, out∈support (execute image 1 s coins) ∧ out.exit=.unfinished ∧ ((HonestWideShapes.cut out.state.pc=true ∧
      t=out.state) ∨ (HonestWideShapes.cut out.state.pc=false ∧ Path coins out.state t)) := by
  cases walk with
  | hit a b c => exact ⟨_,a,b,Or.inl ⟨c,rfl⟩⟩
  | more a b c d => exact ⟨_,a,b,Or.inr ⟨c,d⟩⟩

theorem sound (start clock : Nat) (pc : Word) (a : Abstract) (b : Names) (v : Values) (marked : Bool)
    (cert : check start clock pc a b marked=true) (origin s t : MachineState) (coins : Bool) (entry : s.pc=pc)
    (numeric : Models s a) (names : Means v s b) (fixed : Frozen s) (loc : protects context v.indices=true)
    (index : s.getMem v.indices=v.position) (flags : HonestFlagEffect.Effect origin s (event v marked))
    (walk : Path coins s t) : holds v (HonestNameShapes.target t.pc) t ∧
      HonestFlagEffect.Effect origin t (event v (doneAt t.pc)) ∧ guardOK start t.pc=true := by
  induction clock generalizing pc a b s marked with
  | zero => cases cert
  | succ k ih =>
    cases opAt : HonestBlocks.readOp Artifact.openingCode pc with
    | none => simp [check,opAt] at cert
    | some op =>
      simp only [check,opAt,Bool.and_eq_true] at cert
      obtain ⟨⟨⟨⟨call,dir⟩,safe⟩,write⟩,edges⟩ := cert
      have pub : op=.base .ECALL → s.getReg .x5=0 := by
        rintro rfl; simp only [HonestRegionBlocks.callable,isQuery,Bool.not_true,Bool.false_or,beq_iff_eq] at call
        exact singleton_ok (numeric.1 _) call
      obtain ⟨out,run,alive,rest⟩ := splitPath walk
      have read := HonestBlocks.fetch_op Artifact.openingCode image (Eq.refl (ArtifactEncoding.decode 32 _)) (by decide)
        s op (entry ▸ opAt)
      obtain ⟨dest,normal⟩ := one _ s coins a op numeric read dir pub out run alive
      have next := HonestWideKernel.step op coins numeric fixed read out run alive normal
      have semantic := HonestNames.step op coins numeric names index read pub out run alive
      have mem (q : Word) (inside : protects context q=true) : out.state.getMem q=s.getMem q :=
        HonestPhysical.unchanged _ s coins a op numeric read pub out run alive q (HonestWideKernel.protected_word a op safe q inside)
      have newer : Frozen out.state := fun q h => mem q h ▸ fixed q h
      have acted : HonestFlagEffect.Effect origin out.state (event v (marked || pc==addr 135)) := by
        cases hit : (pc==addr 135) with
        | true =>
          simp only [hit,ite_true,Bool.and_eq_true,Bool.not_eq_true'] at write
          obtain ⟨rfl,store⟩ := write
          exact HonestFlagEffect.follow flags (mark op coins numeric names read store out run alive)
        | false =>
          simp only [hit,Bool.false_eq_true,ite_false] at write
          intro q inside
          rw [HonestPhysical.same_bytes _ s coins a op numeric read pub out run alive HonestFlagEffect.flags write q inside]
          simpa only [Bool.or_false] using flags q inside
      rw [entry] at dest
      have edge := List.all_eq_true.mp edges _ dest
      rcases rest with ⟨stop,rfl⟩|⟨inside,more⟩
      · simp only [stop,ite_true,Bool.and_eq_true,beq_iff_eq] at edge
        exact ⟨fit_ok semantic edge.1.1,edge.1.2 ▸ acted,edge.2⟩
      · simp only [inside,Bool.false_eq_true,ite_false] at edge
        exact ih _ _ _ _ edge _ rfl next semantic newer ((mem _ loc).trans index) acted more

end CommitGolfCandidate.Reconstruction.HonestNameKernel
