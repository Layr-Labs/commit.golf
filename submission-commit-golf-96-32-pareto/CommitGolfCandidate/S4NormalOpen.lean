import CommitGolfCandidate.S4NormalLatch
import CommitGolfCandidate.S4RecordRun
import CommitGolfCandidate.S4FieldWords8
namespace CommitGolfCandidate.S4.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Machine (W Runs SameOutside proofBase indexBase wordAt Safe)
open Late (Trapdoor pcAt)

def returnedRecords (td : Trapdoor) (ps : Positions) (b : Bool) (r : Nat) :=
  ((indices ps).take r).flatMap (rawRecord td b)

theorem returnedStep (td : Trapdoor) (ps : Positions) (b : Bool) (r : Nat) (inside : r<ps.card) :
    returnedRecords td ps b (r+1)=returnedRecords td ps b r++rawRecord td b (recordIndex ps r) := by
  have h : r<(indices ps).length:=by simpa only [indices,Finset.length_sort] using inside
  simp only [returnedRecords,List.take_succ_eq_append_getElem h,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  rw [show recordIndex ps r=(indices ps)[r] from by change (indices ps)[r]?.getD _=_;rw [List.getElem?_eq_getElem h];rfl]

theorem rawRecordLen (td : Trapdoor) (b : Bool) (i : Index) : (rawRecord td b i).length=recordBytes b := by
  have ix (q : Nat) (small : q≤fieldsIn b) : (recordPrefix td b i q).length=offsetAt b q := by
    induction q with
    | zero=>rfl
    | succ q ih=>
      have lim : q<26:=by unfold fieldsIn at small;split at small <;> omega
      have eqv : ∀ b : Bool,∀ q : Fin 26,q.val<fieldsIn b → offsetAt b q+widthAt b q=offsetAt b (q.val+1):=by decide
      rw [prefixStep,List.length_append,ih (by omega),payloadSize _ _ _ _ (by omega)]
      exact eqv b ⟨q,lim⟩ (by change q<fieldsIn b;omega)
  rw [←completeRecord,ix _ le_rfl];cases b <;> decide

theorem returnedLen (td : Trapdoor) (ps : Positions) (b : Bool) (r : Nat) (inside : r≤ps.card) :
    (returnedRecords td ps b r).length=recordBytes b*r := by
  induction r with
  | zero=>simp [returnedRecords]
  | succ r ih=>rw [returnedStep _ _ _ _ (by omega),List.length_append,rawRecordLen,ih (by omega),Nat.mul_succ]

theorem Contains.more {s t : MachineState} {a : Nat} {old newBytes : Proof} (before : Contains s a old)
    (next : Contains t (a+old.length) newBytes) (untouched : SameOutside s t (a+old.length) newBytes.length)
    (bound : a+old.length≤MEMORY_BYTES) : Contains t a (old++newBytes) := by
  intro j bj;by_cases prev : j<old.length
  · rw [List.getElem_append_left prev]
    exact (untouched (a+j) (by unfold MEMORY_BYTES at bound;omega) (Or.inl (by omega))).trans (before j prev)
  · rw [List.getElem_append_right (by omega)]
    have small : j-old.length<newBytes.length:=by rw [List.length_append] at bj;omega
    simpa only [show a+old.length+(j-old.length)=a+j by omega] using next _ small

structure NormalCursor (td : Trapdoor) (ps : Positions) (s : MachineState) (r : Nat) : Prop where
  pc : s.pc=pcAt (normalEndPC ps.card r)
  dest : s.getReg .x19=W (proofBase+824*r)
  ix : s.getReg .x21=W (indexBase+8*r)
  left : s.getReg .x20=W (ps.card-r)
  output : s.getReg .x15=W proofBase
  three : s.getReg .x27=3
  sources : Sources td ps s
  data : Contains s proofBase (returnedRecords td ps false r)

private theorem sizes : prefixSteps false 0 26=587 ∧ totalCost false 0 26=599 ∧ offsetAt false 26=824 := by decide

theorem normalStep (td : Trapdoor) (ps : Positions) (s : MachineState) (r : Nat) (inside : r<ps.card)
    (f : NormalCursor td ps s r) : ∃ t,NormalCursor td ps t (r+1) ∧
    Runs .opening s t (587+latchPrice ps.card r) (599+latchPrice ps.card r) := by
  let base:=proofBase+824*r;let i:=recordIndex ps r
  have room : ps.card≤LENGTH:=by simpa using Finset.card_le_univ ps
  change ps.card≤16777216 at room
  have start : s.pc=pcAt (recordPC false 0):=by simpa only [normalEndPC,if_pos inside,recordPC,Bool.false_eq_true,ite_false] using f.pc
  have a : s.getReg (ixReg false)+W (8*0)=W (indexBase+8*r):=by rw [show ixReg false=.x21 from rfl,f.ix];exact BitVec.add_zero _
  have idx : s.getMem (s.getReg (ixReg false)+W (8*0))=W i.val:=by rw [a];exact f.sources.index r inside
  have safe : accessValid (s.getReg (ixReg false)+W (8*0)) 8=true:=by
    rw [a];apply Safe.valid;constructor <;> simp only [indexBase,MEMORY_BYTES] <;> omega
  let x:=recordState false 0 s 26
  have recs : RecordProgress td ps false 0 base 26 i s x:=recordRun td ps false 0 base i s (by decide) (Or.inr rfl)
    (fun q bq=>allWords8 ⟨q,bq⟩) start f.sources f.three idx safe f.dest (by unfold base proofBase;omega)
    (by unfold base;omega) (by unfold base proofBase;change 12079599648+824*r+824≤2^36;omega) 26 le_rfl
  have keep (v : Reg) (h : saved false v) :=recs.keep v h
  have ptrIx : x.getReg .x21=W (indexBase+8*r):=(keep .x21 (by decide)).trans f.ix
  have cnt : x.getReg .x20=W (ps.card-r):=(keep .x20 (by decide)).trans f.left
  obtain ⟨latch,nextPC,nextIx,nextCnt,same,nextRegs⟩:=normalLatch x ps.card r inside room (normalEnd ▸ recs.pc) ptrIx cnt
  let t:=normalTail x ps.card r
  refine ⟨t,⟨nextPC,?_,nextIx,nextCnt,?_,?_,recs.source.sameMem same,?_⟩,?_⟩
  · have d:=recs.cursor
    rw [sizes.2.2] at d
    exact (nextRegs .x19 (by decide) (by decide)).trans (d.trans (congrArg W (by dsimp [base];omega)))
  · exact (nextRegs .x15 (by decide) (by decide)).trans ((keep .x15 (by decide)).trans f.output)
  · exact (nextRegs .x27 (by decide) (by decide)).trans ((keep .x27 (by decide)).trans f.three)
  · rw [returnedStep td ps false r inside]
    have part : Contains x base (rawRecord td false i):=completeRecord td false i ▸ recs.bytes
    have len : (returnedRecords td ps false r).length=824*r:=returnedLen _ _ _ _ (by omega)
    apply Contains.mem _ same
    apply f.data.more
    · rw [len];exact part
    · rw [len,rawRecordLen];have frame:=recs.outside;rw [sizes.2.2] at frame;exact frame
    · rw [len];unfold proofBase MEMORY_BYTES;omega
  · have body:=recs.run
    rw [sizes.1,sizes.2.1] at body;exact body.trans latch

theorem normalAll (td : Trapdoor) (ps : Positions) (s : MachineState) (f : NormalCursor td ps s 0)
    (k : Nat) (bk : k≤ps.card) : ∃ t n m,NormalCursor td ps t k ∧ Runs .opening s t n m ∧ n≤591*k := by
  induction k with
  | zero=>exact ⟨s,0,0,f,Runs.refl .opening s,le_rfl⟩
  | succ k ih=>
    obtain ⟨u,n,m,state,done,limit⟩:=ih (by omega)
    obtain ⟨t,endState,tail⟩:=normalStep td ps u k (by omega) state
    refine ⟨t,_,_,endState,done.trans tail,?_⟩;unfold latchPrice;split <;> omega
end CommitGolfCandidate.S4.Open
