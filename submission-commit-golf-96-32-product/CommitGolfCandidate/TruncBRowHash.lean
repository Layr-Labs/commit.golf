import CommitGolfCandidate.TruncBCounts
import CommitGolfCandidate.TruncBPrefix
import CommitGolfCandidate.TruncCap
import CommitGolfCandidate.Stage3Record
import CommitGolfCandidate.LateCheckInputs
namespace CommitGolfCandidate.Trunc.Batch
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 10000
set_option maxHeartbeats 250000
attribute [local irreducible] Late.Check.Normal.checkEvaluation readBuffer

def rowBucket (input : CheckInput) (n : Nat) : Fin 256 :=
  ⟨CommitGolfCandidate.openingIndex input.positions n / 65536,by have h : CommitGolfCandidate.openingIndex input.positions n < 16777216 := CommitGolfCandidate.opening_index_bound _ _; omega⟩

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

theorem hashRecord (o : Oracle) (i : CheckInput) (batch : i.positions.card=BATCH)
    (n : Nat) (small : n<128) (s : MachineState) (inv : RecordInvariant o.compression i n s) :
    ∃ t k, k≤1010 ∧ Runs o s t k 20 ∧ HashedFrame o i n t ∧ Late.Check3.Micro.High s t := by
  let ix:=CommitGolfCandidate.recordIndex i n
  let v:=CommitGolfCandidate.recordValue i n
  let a:=7784632352+256*n
  let p:=12079599648+536*n
  have fit : n < i.positions.card := by rw [batch];exact small
  have eqIx : ix=Late.Check.recordIndex i.positions n := by
    apply Fin.ext
    simp only [ix,CommitGolfCandidate.recordIndex,CommitGolfCandidate.openingIndex,dif_pos fit,Late.Check.recordIndex,
      List.getElem?_eq_getElem (by simpa using fit : n<(i.positions.sort (·≤·)).length),Option.getD_some]
  have eqV : v=Late.Check.recordValue i n := by
    simp only [v,CommitGolfCandidate.recordValue,dif_pos fit,Late.Check.recordValue,List.getElem?_eq_getElem
      (by simpa using fit : n<(i.positions.attach.sort (fun a b=>a.val≤b.val)).length),Option.map_some,Option.getD_some]
  have raw (w : Word) (x : w.toNat=7650414624+8*n) :
      s.getMem w=(Trunc.submission.initialState .check i).getMem w :=
    inv.inputWords w (by rw [x];omega) (by rw [x];omega) (by rw [x];unfold MEMORY_BYTES;omega)
  have addrOK : accessValid (s.getReg .x24) 8 := by rw [inv.indexPtr];apply addrOK8 <;> omega
  have ixR : s.getMem (s.getReg .x24)=Late.Open.W ix.val := by
    rw [inv.indexPtr,raw _ (by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]),eqIx]
    exact Late.Check.loaded_index i n fit
  have valueR : readBuffer s a 256=v := by rw [eqV];exact (readHighA s _ inv.inputWords _ _ (by unfold a;omega)
    (by unfold a MEMORY_BYTES;omega)).trans (Late.Check.loaded_value i n fit)
  have saltR : readBuffer s p 24=batchSalt i n := readHighA s _ inv.inputWords _ _ (by unfold p;omega) (by unfold p MEMORY_BYTES;omega)
  have src (j : Nat) (hj : j<16) : readBuffer s (p+24+32*j) 32=lowerSibling i n j :=
    readHigh s _ inv.inputWords _ (by unfold p;omega) (by unfold p;omega) (by unfold p MEMORY_BYTES;omega)
  obtain ⟨t,k,h⟩:=Trunc.hashPosition o s 16 a p ix (batchSalt i n) v (lowerSibling i n)
    (by rw [inv.pc,if_neg (by omega)]) addrOK ixR inv.valuePtr inv.proofPtr inv.scratch inv.depth (Or.inl rfl)
    (by rw [inv.slots];decide) ⟨by unfold a;omega,by unfold a MEMORY_BYTES;omega⟩
    ⟨by unfold p;omega,by unfold p MEMORY_BYTES;omega⟩ (by unfold a;omega) (by unfold p;omega) valueR saltR src
  refine ⟨t,k,by have:=h.bound;omega,h.run,?_,h.high⟩
  exact ⟨h.pc,h.index,(h.keep _ (by decide)).trans inv.indexPtr,h.value.trans (congrArg Late.Open.W (by unfold a;omega)),
    h.proof.trans (congrArg Late.Open.W (by unfold p;omega)),(h.keep _ (by decide)).trans inv.remaining,
    (h.keep _ (by decide)).trans inv.scratch,(h.keep _ (by decide)).trans inv.depth,
    (h.keep _ (by decide)).trans inv.slots,(h.keep _ (by decide)).trans inv.root,h.data⟩

end CommitGolfCandidate.Trunc.Batch
