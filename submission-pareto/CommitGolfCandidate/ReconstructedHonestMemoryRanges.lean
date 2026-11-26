import RiscvZkvm.Rv64.Logic.ByteOps
import CommitGolfCandidate.ReconstructedHonestRanges

namespace CommitGolfCandidate.Reconstruction.HonestMemoryRanges
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 HonestRanges

abbrev Heap := Word → Range
def HeapMeaning (s : MachineState) (m : Heap) := ∀ q, Contains (m q) (s.getMem q)

structure Store where
  base : Reg
  source : Reg
  offset : BitVec 12
  whole : Bool
  deriving DecidableEq

def store : Instruction → Option Store
  | .base (.SD a b n) => some ⟨a,b,n,true⟩
  | .base (.SW a b n) | .base (.SH a b n) | .base (.SB a b n) => some ⟨a,b,n,false⟩
  | _ => none

def Store.address (w : Store) (s : MachineState) := s.getReg w.base+signExtend12 w.offset
def Store.cell (w : Store) (s : MachineState) := if w.whole then w.address s else alignToDword (w.address s)

theorem memory_frame (s t : MachineState) (op : Instruction) (q : Word)
    (step : ordinaryStep s op = some t) (separate : ∀ w, store op=some w → q≠w.cell s) :
    t.getMem q = s.getMem q := by
  cases op with
  | word op r a b | sraiw r a b =>
    simp only [ordinaryStep,Option.some.injEq] at step
    subst t; simp only [MachineState.getMem_setPC,MachineState.getMem_setReg]
  | base op =>
    cases op <;> simp only [ordinaryStep,reduceCtorEq,Option.ite_none_right_eq_some,Option.some.injEq] at step
    all_goals obtain ⟨_,rfl⟩ := step
    all_goals simp only [execInstrBr,MachineState.getMem_setPC,MachineState.getMem_setReg]
    all_goals try (split <;> rfl)
    all_goals have away := separate _ rfl
    all_goals simp only [Store.cell,Store.address,ite_true,Bool.false_eq_true,ite_false] at away
    all_goals exact MachineState.getMem_setMem_ne away

theorem full_store {s t : MachineState} {op : Instruction} {w : Store} (desc : store op=some w)
    (full : w.whole=true) (step : ordinaryStep s op=some t) : t.getMem (w.address s)=s.getReg w.source := by
  cases op with
  | word _ _ _ _ | sraiw _ _ _ => cases desc
  | base op =>
    cases op <;> simp only [store,reduceCtorEq,Option.some.injEq] at desc
    all_goals subst w
    all_goals try cases full
    simp only [ordinaryStep,Option.ite_none_right_eq_some,Option.some.injEq] at step
    obtain ⟨_,rfl⟩ := step
    exact MachineState.getMem_setMem_eq

theorem aligned_window (v : Word) : (alignToDword v).toNat ≤ v.toNat ∧ v.toNat ≤ (alignToDword v).toNat+7 := by
  constructor
  · simp only [alignToDword,BitVec.toNat_and]; exact Nat.and_le_left
  · have bounds : byteOffset v < 8 := byteOffset_lt_8
    have whole := congrArg BitVec.toNat (alignToDword_add_byteOffset v)
    simp only [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show byteOffset v<2^64 by omega)] at whole
    omega

/-- Addresses outside an interval retain their stored qword, including when a
byte or halfword store updates its enclosing aligned qword. -/
def away (a : Range) (q : Word) : Bool := q.toNat+7<a.lo || a.hi<q.toNat

theorem away_ok (a : Range) (q p : Word) (valid : Contains a p) (out : away a q = true) :
    q≠p ∧ q≠alignToDword p := by
  simp only [away,Bool.or_eq_true,decide_eq_true_eq] at out
  obtain ⟨lo,hi⟩ := valid
  constructor
  · rintro rfl; omega
  · rintro rfl; have := aligned_window p; omega

def addressRange (base : Range) (offset : BitVec 12) := plus base (point (signExtend12 offset))

theorem address_ok {p : Word} {base : Range} (within : Contains base p) (n : BitVec 12) :
    Contains (addressRange base n) (p+signExtend12 n) := plus_ok within (precise _)

def heapAfter (m : Registers) (h : Heap) (op : Instruction) (q : Word) : Range :=
  match store op with
  | none => h q
  | some w =>
    let a := addressRange (m w.base) w.offset
    if w.whole && singleton a == some q then m w.source
    else if away a q then h q else any

theorem heapAfter_ok {s t : MachineState} (m : Registers) (h : Heap) (op : Instruction)
    (reg : Meaning s m) (mem : HeapMeaning s h) (step : ordinaryStep s op=some t) :
    HeapMeaning t (heapAfter m h op) := by
  intro q
  cases desc : store op with
  | none =>
    simp only [heapAfter,desc]
    rw [memory_frame _ _ _ _ step (by intro w eq; rw [desc] at eq; cases eq)]
    exact mem q
  | some w =>
    have contained := address_ok (reg w.base) w.offset
    simp only [heapAfter,desc]
    split
    · rename_i hit
      simp only [Bool.and_eq_true,beq_iff_eq] at hit
      have value : w.address s=q := singleton_ok contained hit.2
      rw [←value,full_store desc hit.1 step]
      exact reg _
    · split
      · rename_i separate
        have ⟨word,part⟩ := away_ok _ _ _ contained separate
        rw [memory_frame _ _ _ _ step (by
          rintro w' eq
          obtain rfl := Option.some.inj (desc.symm.trans eq)
          unfold Store.cell; split <;> assumption)]
        exact mem _
      · exact arbitrary _

/-- A qword load whose address is known can use the live immutable or spilled
word. All other loads and ALU operations retain the regular register abstraction. -/
def registersAfter (m : Registers) (h : Heap) (op : Instruction) (r : Reg) : Range :=
  match op with
  | .base (.LD d a n) =>
    if d=r ∧ r≠.x0 then
      match singleton (addressRange (m a) n) with
      | some p => h p
      | none => any
    else HonestRanges.update m op r
  | _ => HonestRanges.update m op r

theorem registersAfter_ok {s t : MachineState} (m : Registers) (h : Heap) (op : Instruction)
    (reg : Meaning s m) (mem : HeapMeaning s h) (step : ordinaryStep s op=some t) :
    Meaning t (registersAfter m h op) := by
  intro r
  have ordinary := update_ok m op reg step r
  cases op with
  | word _ _ _ _ | sraiw _ _ _ => exact ordinary
  | base op =>
    cases op <;> try exact ordinary
    rename_i d a n
    simp only [registersAfter]
    split
    · rename_i test
      obtain ⟨rfl,nz⟩ := test
      cases known : singleton (addressRange (m a) n) with
      | none => exact arbitrary _
      | some p =>
        have addr := singleton_ok (address_ok (reg a) n) known
        simp only [ordinaryStep,Option.ite_none_right_eq_some,Option.some.injEq] at step
        obtain ⟨_,rfl⟩ := step
        simp only [execInstrBr,MachineState.getReg_setPC,MachineState.getReg_setReg_eq nz,addr]
        exact mem _
    · exact ordinary

end CommitGolfCandidate.Reconstruction.HonestMemoryRanges
