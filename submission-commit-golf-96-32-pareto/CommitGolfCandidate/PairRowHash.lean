import CommitGolfCandidate.PairCounts
import CommitGolfCandidate.PairPrefix
import CommitGolfCandidate.PairPathValue
import CommitGolfCandidate.BatchPathRun
namespace CommitGolfCandidate.PairCap.Batch
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 10000
set_option maxHeartbeats 250000
attribute [local irreducible] Late.Check.Normal.checkEvaluation readBuffer

def rowBucket (input : CheckInput) (n : Nat) : Fin 256 :=
  ⟨openingIndex input.positions n / 65536,by have h : openingIndex input.positions n < 16777216 := opening_index_bound _ _; omega⟩

theorem addrOK8 (a : Nat) (bound : a+8 ≤ 2^36) (align : a%8=0) :
    accessValid (BitVec.ofNat 64 a) 8 = true := by
  simp only [accessValid,rangeValid,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : a<2^64),
    Bool.and_eq_true,decide_eq_true_eq,MEMORY_BYTES];exact ⟨bound,align⟩

theorem readHighA (s t : MachineState)
    (same : ∀ w : Word, 32768≤w.toNat → w.toNat%8=0 → w.toNat+8≤MEMORY_BYTES → s.getMem w=t.getMem w)
    (a n : Nat) (hi : 32768≤a) (bound : a+n≤MEMORY_BYTES) : readBuffer s a n=readBuffer t a n := by
  have preserved : Late.Open.Outside t s 0 32768 := by
    intro j hj al outside
    have big : 32768≤j := by omega
    have j64 : j<2^64 := by unfold MEMORY_BYTES at hj;omega
    apply same
    all_goals rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt j64]
    · exact big
    · exact al
    · unfold MEMORY_BYTES at *;omega
  exact Late.Open.outside_read preserved (by decide) (by decide) a n bound (Or.inr hi)

theorem readHigh (s t : MachineState)
    (same : ∀ w : Word,32768≤w.toNat → w.toNat%8=0 → w.toNat+8≤MEMORY_BYTES → s.getMem w=t.getMem w)
    (a : Nat) (hi : 32768≤a) (_align : a%8=0) (bound : a+32≤MEMORY_BYTES) :
    readBuffer s a 32=readBuffer t a 32 := readHighA s t same a 32 hi bound

theorem wordShift (i : Nat) (b : i<2^24) :
    BitVec.ofNat 64 i >>> 16 = BitVec.ofNat 64 (i/65536) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : i<2^64), Nat.mod_eq_of_lt (by omega : i/65536<2^64)]

structure HashedFrame (o : Oracle) (input : CheckInput) (n : Nat) (s : MachineState) : Prop where
  pc : s.pc=5120
  index : s.getReg .x20=BitVec.ofNat 64 (rowBucket input n).val
  ip : s.getReg .x24=BitVec.ofNat 64 (7650414624+8*n)
  vp : s.getReg .x8=BitVec.ofNat 64 (7784632352+256*(n+1))
  pp : s.getReg .x25=BitVec.ofNat 64 (12079599648+536*(n+1))
  remaining : s.getReg .x27=BitVec.ofNat 64 (128-n)
  scratch : s.getReg .x21=256
  depth : s.getReg .x30=16
  slots : s.getReg .x19=12079668256
  root : s.getReg .x26=4294971392
  digest : readBuffer s 256 32=lowerHash o.compression input n

theorem hashRecord (o : Oracle) (input : CheckInput) (batch : input.positions.card=BATCH)
    (n : Nat) (small : n<128) (s : MachineState) (inv : RecordInvariant o.compression input n s) :
    ∃ t k, k≤834 ∧ Runs o s t k 20 ∧ HashedFrame o input n t ∧ Late.Check.Micro.High s t := by
  let i:=Late.Check.recordIndex input.positions n
  let v:=Late.Check.recordValue input n
  let a:=7784632352+256*n
  let p:=12079599648+536*n
  have present : n < input.positions.card := by rw [batch];exact small
  have pbound : p+536≤MEMORY_BYTES := by unfold p MEMORY_BYTES;omega
  have vp : Late.Open.AddrOK a 256 := ⟨by unfold a;omega,by unfold a MEMORY_BYTES;omega⟩
  have pr : Late.Open.AddrOK p 24 := ⟨by unfold p;omega,by omega⟩
  have pp : Late.Open.AddrOK (p+24) 512 := ⟨by have :=pr.1;omega,by omega⟩
  have ix (w : Word) (h : w.toNat=7650414624+8*n) :
      s.getMem w=(Late.submission.initialState .check input).getMem w :=
    inv.inputWords w (by rw [h];omega) (by rw [h];omega) (by rw [h];unfold MEMORY_BYTES;omega)
  have indexData : s.getMem (s.getReg .x24)=Late.Open.W i.val := by
    rw [inv.indexPtr,ix _ (by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)])]
    exact Late.Check.loaded_index input n present
  have safe : accessValid (s.getReg .x24) 8 := by rw [inv.indexPtr];apply addrOK8 <;> omega
  have valueR : readBuffer s a 256=v :=
    (readHighA s _ inv.inputWords a 256 (by unfold a;omega) vp.2).trans (Late.Check.loaded_value input n present)
  have fixed : Late.Check.start input n=536*n := by unfold Late.Check.start Late.Check.depth;rw [if_pos batch];omega
  have saltR : readBuffer s p 24=Late.Check.salt input n := by
    rw [readHighA s _ inv.inputWords p 24 (by unfold p;omega) pr.2,Late.Check.salt,fixed];rfl
  obtain ⟨u,k,lf⟩:=Late.Check.Micro.rowLeaf o .batch s a p i (Late.Check.salt input n) v
    (by rw [inv.pc,if_neg (by omega)];rfl) safe indexData inv.valuePtr inv.proofPtr inv.scratch
    vp pr (by unfold a;omega) (by unfold p;omega) valueR saltR
  have pathData (j : Nat) (hj : j<16) : readBuffer u (p+24+32*j) 32=Late.Check.sibling input n j := by
    have bound : p+24+32*j+32≤MEMORY_BYTES := by omega
    rw [lf.high _ _ (by unfold p;omega) bound,readHighA s _ inv.inputWords _ _ (by unfold p;omega) bound,
      Late.Check.sibling,fixed]
    unfold Late.Check.proofAt p
    rw [show 12079599648+536*n+24+32*j=12079599648+(536*n+24+32*j) by omega];rfl
  obtain ⟨t,j,done⟩:=BatchPath.fullPath o u (p+24) i (Late.Check.sibling input n) lf.pc
    ((lf.keep _ (by decide)).trans inv.depth) ((lf.keep _ (by decide)).trans inv.scratch)
    lf.proof lf.idx pp (by unfold p;omega) pathData
  refine ⟨t,k+j,by have :=lf.budget;have :=done.budget;omega,?_,?_,lf.high.trans done.high⟩
  · exact lf.run.trans done.runs
  · refine ⟨done.pc,done.index,(done.keep _ (by decide)).trans ((lf.keep _ (by decide)).trans inv.indexPtr),?_,?_,
      (done.keep _ (by decide)).trans ((lf.keep _ (by decide)).trans inv.remaining),
      (done.keep _ (by decide)).trans ((lf.keep _ (by decide)).trans inv.scratch),
      (done.keep _ (by decide)).trans ((lf.keep _ (by decide)).trans inv.depth),
      (done.keep _ (by decide)).trans ((lf.keep _ (by decide)).trans inv.slots),
      (done.keep _ (by decide)).trans ((lf.keep _ (by decide)).trans inv.root),?_⟩
    · exact (done.keep _ (by decide)).trans (lf.value.trans (congrArg Late.Open.W (by unfold a;omega)))
    · exact done.proof.trans (congrArg Late.Open.W (by unfold p;omega))
    · unfold lowerHash Late.Check.lower
      exact done.digest.trans (congrArg (fun z=>climb o.compression z (Late.Check.path i 16 (Late.Check.sibling input n))) lf.digest)

end CommitGolfCandidate.PairCap.Batch
