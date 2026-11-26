import CommitGolfCandidate.Stage3Record
import CommitGolfCandidate.LateCheckInputs
import CommitGolfCandidate.TruncAuthentication
import CommitGolfCandidate.TruncNormalLatches
import CommitGolfCandidate.TruncBRowHash
namespace CommitGolfCandidate.Trunc.Normal
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 12000
set_option maxHeartbeats 190000
attribute [local irreducible] readBuffer checkEvaluation

theorem positionCount (ps : Positions) : ps.card≤16777216 := by
  change ps.card≤LENGTH;simpa [Index] using Finset.card_le_univ ps

def inputState (i : CheckInput) := Trunc.submission.initialState .check i

structure Frame (i : CheckInput) (n : Nat) (s : MachineState) : Prop where
  indexPtr : s.getReg .x24=BitVec.ofNat 64 (7650414624+8*n)
  valuePtr : s.getReg .x8=BitVec.ofNat 64 (7784632352+256*n)
  proofPtr : s.getReg .x25=BitVec.ofNat 64 (12079599648+792*n)
  remaining : s.getReg .x27=BitVec.ofNat 64 (i.positions.card-n)
  root : s.getReg .x26=4294971392
  scratch : s.getReg .x21=256
  depth : s.getReg .x30=24
  slots : s.getReg .x19=0
  pc : s.pc=if n=i.positions.card then 4420 else 4156
  high : ∀ w : Word,32768≤w.toNat → w.toNat%8=0 → w.toNat+8≤MEMORY_BYTES → s.getMem w=(inputState i).getMem w

def mathRoot (o : Oracle) (i : CheckInput) (n : Nat) :=
  Trunc.recordRoot o.compression (recordValue i n) (recordSalt i n) (recordIndex i n) (normalSibling i n)

theorem addrOK8 (a : Nat) (bound : a+8 ≤ 2^36) (align : a%8=0) :
    accessValid (BitVec.ofNat 64 a) 8 = true := by
  simp only [accessValid,rangeValid,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : a<2^64),
    Bool.and_eq_true,decide_eq_true_eq,MEMORY_BYTES];exact ⟨bound,align⟩

theorem hash (o : Oracle) (i : CheckInput) (mode : i.positions.card≠BATCH) (n : Nat) (hn : n < i.positions.card)
    (s : MachineState) (f : Frame i n s) :
    ∃ t k, k≤1460 ∧ Batch.Runs o s t k 28 ∧ t.pc=5120 ∧ t.getReg .x20=0 ∧
      t.getReg .x8=s.getReg .x8+256 ∧ t.getReg .x25=s.getReg .x25+792 ∧
      (∀ r∈[Reg.x19,.x21,.x24,.x26,.x27,.x30],t.getReg r=s.getReg r) ∧
      Late.Check3.Micro.High s t ∧ readBuffer t 256 32=mathRoot o i n := by
  let start:=s.setPC (loc 207)
  let ix:=recordIndex i n
  let a:=7784632352+256*n
  let p:=12079599648+792*n
  have card:=positionCount i.positions
  have ip : s.pc=4156 := f.pc.trans (if_neg (Nat.ne_of_lt hn))
  have jump:=recordStart s ip
  have indexEq : ix=Late.Check.recordIndex i.positions n := by
    apply Fin.ext
    simp only [ix,recordIndex,openingIndex,dif_pos hn,Late.Check.recordIndex,
      List.getElem?_eq_getElem (by simpa using hn : n<(i.positions.sort (·≤·)).length),Option.getD_some]
  have valEq : recordValue i n=Late.Check.recordValue i n := by
    simp only [recordValue,dif_pos hn,Late.Check.recordValue,List.getElem?_eq_getElem
      (by simpa using hn : n<(i.positions.attach.sort (fun a b=>a.val≤b.val)).length),Option.map_some,Option.getD_some]
  have ok : accessValid (s.getReg .x24) 8 := by rw [f.indexPtr];apply addrOK8 <;> omega
  have atN : (BitVec.ofNat 64 (7650414624+8*n)).toNat=7650414624+8*n := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have idx : s.getMem (s.getReg .x24)=Late.Open.W ix.val := by
    rw [f.indexPtr,f.high _ (by rw [atN];omega) (by rw [atN];omega) (by rw [atN];unfold MEMORY_BYTES;omega),indexEq]
    exact Late.Check.loaded_index i n hn
  have val : readBuffer s a 256=recordValue i n := by
    rw [valEq];exact (Batch.readHighA s _ f.high _ _ (by unfold a;omega) (by unfold a MEMORY_BYTES;omega)).trans (Late.Check.loaded_value i n hn)
  have salt : readBuffer s p 24=recordSalt i n := Batch.readHighA s _ f.high _ _ (by unfold p;omega) (by unfold p MEMORY_BYTES;omega)
  have path (j : Nat) (hj : j<24) : readBuffer s (p+24+32*j) 32=normalSibling i n j :=
    Batch.readHigh s _ f.high _ (by unfold p;omega) (by unfold p;omega) (by unfold p MEMORY_BYTES;omega)
  obtain ⟨t,k,h⟩:=Trunc.hashPosition o start 24 a p ix _ _ (normalSibling i n) rfl ok idx f.valuePtr f.proofPtr
    f.scratch f.depth (Or.inr rfl) ⟨fun _=>rfl,fun _=>f.slots⟩ ⟨by unfold a;omega,by unfold a MEMORY_BYTES;omega⟩
    ⟨by unfold p;omega,by unfold p MEMORY_BYTES;omega⟩ (by unfold a;omega) (by unfold p;omega)
    ((Late.read_congr_mem start s a 256 rfl).trans val) ((Late.read_congr_mem start s p 24 rfl).trans salt)
    (fun j hj=>(Late.read_congr_mem start s _ _ rfl).trans (path j hj))
  refine ⟨t,1+k,by have:=h.bound;omega,Batch.runs_trans (Batch.pureBlockRuns (fun fuel=>jump fuel false)) h.run,
    h.pc,?_,?_,?_,fun reg hr=>(h.keep reg hr).trans MachineState.getReg_setPC,
    (Late.Check3.Micro.High.memory (show start.mem=s.mem from rfl)).trans h.high,h.data⟩
  · rw [h.index,Nat.div_eq_of_lt (show ix.val<2^24 from ix.isLt)];rfl
  · rw [h.value,f.valuePtr];exact BitVec.ofNat_add a 256
  · rw [h.proof,f.proofPtr,show p+24+32*24=p+792 by omega];exact BitVec.ofNat_add p 792

end CommitGolfCandidate.Trunc.Normal
