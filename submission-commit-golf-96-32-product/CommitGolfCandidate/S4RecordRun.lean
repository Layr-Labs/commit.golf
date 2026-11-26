import CommitGolfCandidate.S4FieldRun
import CommitGolfCandidate.S4RecordData
import CommitGolfCandidate.S4ReadField
namespace CommitGolfCandidate.S4.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (Trapdoor pcAt)
open Machine (W byte Runs SameOutside proofBase)

def recordState (b : Bool) (l : Nat) (s : MachineState) : Nat→MachineState
  | 0=>s
  | q+1=>afterField b l q (recordState b l s q)
def prefixSteps (b : Bool) (l : Nat) : Nat→Nat
  | 0=>0
  | q+1=>prefixSteps b l q+fieldSize b l q

private theorem offsets : ∀ b : Bool,∀ q : Fin 26,q.val<fieldsIn b →
    offsetAt b q+widthAt b q=offsetAt b (q.val+1) ∧ offsetAt b q+widthAt b q≤recordBytes b ∧ widthAt b q≤32 := by decide

structure RecordProgress (td : Trapdoor) (ps : Positions) (b : Bool) (l base q : Nat) (i : Index)
    (s t : MachineState) : Prop where
  run : Runs .opening s t (prefixSteps b l q) (totalCost b l q)
  pc : t.pc=pcAt (fieldPC b l q)
  cursor : t.getReg .x19=W (base+offsetAt b q)
  field : FieldState b l q i t
  source : Sources td ps t
  keep : ∀ r,saved b r → t.getReg r=s.getReg r
  bytes : Contains t base (recordPrefix td b i q)
  length : (recordPrefix td b i q).length=offsetAt b q
  outside : SameOutside s t base (offsetAt b q)

theorem recordRun (td : Trapdoor) (ps : Positions) (b : Bool) (l base : Nat) (i : Index) (s : MachineState)
    (bl : l<8) (which : b=true ∨ l=0) (code : ∀ q<fieldsIn b,fieldValid b l q)
    (start : s.pc=pcAt (recordPC b l)) (src : Sources td ps s) (divisor : s.getReg .x27=3)
    (headIndex : s.getMem (s.getReg (ixReg b)+W (8*l))=W i.val)
    (safeIndex : accessValid (s.getReg (ixReg b)+W (8*l)) 8=true)
    (out : s.getReg .x19=W base) (baseAlign : base%8=(recordBytes b*l)%8)
    (high : proofBase≤base) (cap : base+recordBytes b≤MEMORY_BYTES) (q : Nat) (bound : q≤fieldsIn b) :
    RecordProgress td ps b l base q i s (recordState b l s q) := by
  induction q with
  | zero=>
    exact ⟨Runs.refl .opening s,start,out,⟨divisor,fun _=>headIndex,fun k=>False.elim (by omega),
      fun k=>False.elim (by omega),fun k=>False.elim (by omega)⟩,src,fun _ _=>rfl,containsEmpty s base,rfl,fun _ _ _=>rfl⟩
  | succ q ih=>
    let mid:=recordState b l s q
    let next:=afterField b l q mid
    have f:=ih (by omega)
    have inside : q<fieldsIn b:=by omega
    have qlim : q<26:=by unfold fieldsIn at inside;split at inside <;> omega
    obtain ⟨edge,below,wide⟩:=offsets b ⟨q,qlim⟩ inside
    have eqv : offsetAt b q+widthAt b q=offsetAt b (q+1):=edge
    have within : offsetAt b q+widthAt b q≤recordBytes b:=below
    have widthBound : widthAt b q≤32:=wide
    obtain ⟨_,srcBound,align⟩:=fieldBounds b q i inside
    have addrBound : targetAddr i q+widthAt b q≤MEMORY_BYTES:=by
      unfold Machine.indexBase at srcBound;unfold MEMORY_BYTES;omega
    have noOverlap : targetAddr i q+widthAt b q≤base+offsetAt b q:=by
      unfold Machine.indexBase at srcBound;unfold proofBase at high;omega
    have destBound : base+offsetAt b q+widthAt b q≤MEMORY_BYTES:=by omega
    have safe : q=0 → accessValid (mid.getReg (ixReg b)+W (8*l)) 8=true:=by rintro rfl;exact safeIndex
    have endOf :=runField b l q (base+offsetAt b q) i mid bl inside which (code q inside) f.pc f.field f.cursor safe align
      (by omega) addrBound destBound noOverlap
    have sourceNext : Sources td ps next:=f.source.moved endOf.copied (by omega)
    have dreg : next.getReg .x27=3:=(endOf.keep .x27 (by cases b <;> decide)).trans f.field.divisor
    have stateNext : FieldState b l (q+1) i next := by
      refine ⟨dreg,fun e=>False.elim (by omega),fun _=>?_,?_,?_⟩
      · have depth : atLevel q=(if q+1=2 then 1 else q+1-2):=by unfold atLevel;split_ifs <;> omega
        rw [←depth];exact endOf.node
      · intro e;have k : q=1:=by omega
        apply (endOf.first k).1.trans
        rw [k];change W ((nodeIndex i.val 0%3+1)%3)=_
        rw [show nodeIndex i.val 0=i.val from Nat.div_one _]
      · intro e;have k : q=1:=by omega
        apply (endOf.first k).2.trans;rw [k];rfl
    have result : Contains next base (recordPrefix td b i (q+1)) := by
      rw [prefixStep]
      apply f.bytes.copy (sourceField td ps b i q mid f.source inside) (payloadSize td b i q inside)
      · rw [f.length];exact endOf.copied
      · rw [f.length];exact destBound.trans (by decide)
    have frame :=f.outside.combined endOf.copied.frame
      (l:=base) (k:=offsetAt b (q+1)) (by omega)
    refine ⟨f.run.trans endOf.runs,endOf.pc,?_,stateNext,sourceNext,
      fun r hr=>(endOf.keep r hr).trans (f.keep r hr),result,?_,frame⟩
    · rw [←eqv,←Nat.add_assoc];exact endOf.cursor
    · rw [prefixStep,List.length_append,f.length,payloadSize _ _ _ _ inside,eqv]
end CommitGolfCandidate.S4.Open
