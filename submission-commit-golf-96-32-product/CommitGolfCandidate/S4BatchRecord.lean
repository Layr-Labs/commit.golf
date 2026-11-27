import CommitGolfCandidate.S4BatchLatch
import CommitGolfCandidate.S4FieldWords

set_option Elab.async false
namespace CommitGolfCandidate.S4.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Machine (W Runs SameOutside proofBase indexBase Safe)
open Late (Trapdoor pcAt)

def batchNext (r : Nat) := if r<128 then recordPC true (r%8) else 4892
structure BatchData (td : Trapdoor) (ps : Positions) (s : MachineState) (r : Nat) : Prop where
  dest : s.getReg .x19=W (proofBase+510*r)
  flags : s.getReg .x24=512
  one : s.getReg .x25=1
  three : s.getReg .x27=3
  output : s.getReg .x15=W proofBase
  sources : Sources td ps s
  bytes : Contains s proofBase (returnedRecords td ps true r)
  marked : Marked ps r s
structure BatchCursor (td : Trapdoor) (ps : Positions) (s : MachineState) (r : Nat) extends BatchData td ps s r : Prop where
  pc : s.pc=pcAt (batchNext r)
  ix : s.getReg .x13=W (indexBase+64*(r/8))
  tiles : s.getReg .x9=W (16-r/8)

def laneSteps (r : Nat) := prefixSteps true (r%8) 17+2
def laneCost (r : Nat) := totalCost true (r%8) 17+2
def recordLatch (r : Nat) := if r%8=7 then tileSteps (r/8) else 0

set_option maxRecDepth 5000 in
theorem oneBatchRecord (td : Trapdoor) (ps : Positions) (s : MachineState) (r : Nat) (batch : ps.card=128)
    (br : r<128) (f : BatchCursor td ps s r) :
    ∃ z,BatchData td ps z (r+1) ∧ z.pc=pcAt (markPC (r%8)+2) ∧
      z.getReg .x13=s.getReg .x13 ∧ z.getReg .x9=s.getReg .x9 ∧
      Runs .opening s z (laneSteps r) (laneCost r) := by
  let l:=r%8;let i:=recordIndex ps r
  let base:=proofBase+510*r
  have lane : l<8:=Nat.mod_lt _ (by decide)
  have inside : r<ps.card:=by omega
  have pc : s.pc=pcAt (recordPC true l):=by simpa only [batchNext,if_pos br] using f.pc
  have address : s.getReg (ixReg true)+W (8*l)=W (indexBase+8*r):=by
    change s.getReg .x13+_=_
    rw [f.ix];exact (BitVec.ofNat_add ..).symm.trans (congrArg W (by dsimp [l];omega))
  have idx : s.getMem (s.getReg (ixReg true)+W (8*l))=W i.val:=by rw [address];exact f.sources.index r inside
  have safe : accessValid (s.getReg (ixReg true)+W (8*l)) 8=true:=by
    rw [address];apply Safe.valid;constructor <;> simp only [indexBase,MEMORY_BYTES] <;> omega
  let x:=recordState true l s 17
  have recs : RecordProgress td ps true l base 17 i s x:=recordRun td ps true l base i s lane (Or.inl rfl)
    (fun q bq=>fieldWords true l q lane bq (Or.inl rfl)) pc f.sources f.three idx safe f.dest
    (by change (12079599648+510*r)%8=(510*(r%8))%8;omega) (by dsimp [base];omega)
    (by change 12079599648+510*r+510≤2^36;omega) 17 le_rfl
  have reg (v : Reg) (h : saved true v) : x.getReg v=s.getReg v:=recs.keep v h
  have parent : x.getReg .x8=W (nodeIndex i.val 15):=recs.field.node (by decide : 0<17)
  obtain ⟨run,atEnd,keep,w⟩:=markRun ⟨l,lane⟩ i x recs.pc ((reg _ (by decide)).trans f.flags) ((reg _ (by decide)).trans f.one) parent
  let z:=markedState x
  have pass (v : Reg) (h : saved true v) (ne : Reg.x6≠v) : z.getReg v=s.getReg v:=(keep v ne).trans (reg v h)
  have bucketLimit : nodeIndex i.val 15<342:=indexInside i 15
  have size : offsetAt true 17=510:=by decide
  have len : (returnedRecords td ps true r).length=510*r:=returnedLen _ _ _ _ (by omega)
  have bounds : base+510≤MEMORY_BYTES:=by change 12079599648+510*r+510≤2^36;omega
  have data : Contains x proofBase (returnedRecords td ps true (r+1)):=by
    rw [returnedStep td ps true r inside]
    apply f.bytes.more
    · rw [len];exact completeRecord td true i ▸ recs.bytes
    · rw [len,rawRecordLen];have frame:=recs.outside;rw [size] at frame;exact frame
    · rw [len];change base≤MEMORY_BYTES;omega
  have current : Marked ps r x:=untouchedFlags f.marked recs.outside (by dsimp [base];omega)
  refine ⟨z,⟨?_,(pass _ (by decide) (by decide)).trans f.flags,(pass _ (by decide) (by decide)).trans f.one,
    (pass _ (by decide) (by decide)).trans f.three,(pass _ (by decide) (by decide)).trans f.output,
    recs.source.mark w (by unfold tdBase;omega),?_,markChanged inside current w⟩,atEnd,pass _ (by decide) (by decide),
    pass _ (by decide) (by decide),recs.run.trans run⟩
  · have d:=recs.cursor;rw [size] at d
    exact (keep .x19 (by decide)).trans (d.trans (congrArg W (by dsimp [base];omega)))
  · apply data.scratch w (by unfold proofBase;omega)
    rw [returnedLen td ps true (r+1) (by omega)];change 12079599648+510*(r+1)≤2^64;omega

theorem BatchData.preserve {td : Trapdoor} {ps : Positions} {r : Nat} {s t : MachineState}
    (data : BatchData td ps s r) (mem : t.mem=s.mem)
    (regs : ∀ x,x≠.x9 → x≠.x13 → t.getReg x=s.getReg x) : BatchData td ps t r := by
  refine ⟨(regs _ (by decide) (by decide)).trans data.dest,(regs _ (by decide) (by decide)).trans data.flags,
    (regs _ (by decide) (by decide)).trans data.one,(regs _ (by decide) (by decide)).trans data.three,
    (regs _ (by decide) (by decide)).trans data.output,data.sources.sameMem mem,data.bytes.mem mem,?_⟩
  intro j hj;simpa only [Machine.byte,MachineState.getByte,MachineState.getMem,mem] using data.marked j hj
end CommitGolfCandidate.S4.Open
