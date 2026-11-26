import CommitGolfCandidate.PairCounts
import CommitGolfCandidate.PairPrefix
import CommitGolfCandidate.CKBLeaf
import CommitGolfCandidate.CKBPath
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
  pp : s.getReg .x25=BitVec.ofNat 64 (12079599648+510*(n+1))
  remaining : s.getReg .x27=BitVec.ofNat 64 (128-n)
  scratch : s.getReg .x21=256
  depth : s.getReg .x30=16
  slots : s.getReg .x19=12079664928
  root : s.getReg .x26=4294971392
  digest : readBuffer s 256 32=lowerHash o.compression input n

/-- Words 207, 208, 217: load the index, jump to the batch leaf `bleaf` (632) linking word 218. -/
theorem enterBatch (s : MachineState) (pc : s.pc=Late.pcAt 207) (safe : accessValid (s.getReg .x24) 8=true) :
    Late.Check.Micro.Runs s (((s.setReg .x20 (s.getMem (s.getReg .x24))).setReg .x1 (Late.pcAt 218)).setPC (Late.pcAt 632)) 3 3 := by
  let a:=s.setReg .x20 (s.getMem (s.getReg .x24))
  have h : Late.Check.Micro.Runs s (a.setPC (Late.pcAt 208)) 1 1 := by
    apply Late.Check.Micro.one 207 (by decide) (.LD .x20 .x24 0) rfl _ _ pc
    have ok : memoryArgumentsValid s (.LD .x20 .x24 0)=true := by change accessValid (s.getReg .x24+0) 8=true;simpa using safe
    have zero : s.getReg .x24+signExtend12 0=s.getReg .x24 := BitVec.add_zero _
    simp only [ordinaryStep,ok,↓reduceIte,execInstrBr,zero,pc]
    change some (a.setPC (Late.pcAt 207+4))=some (a.setPC (Late.pcAt 208))
    rw [← Late.pc_succ 207]
  have j : Late.Check.Micro.Runs (a.setPC (Late.pcAt 208)) (a.setPC (Late.pcAt 217)) 1 1 :=
    Late.Check.Micro.one 208 (by decide) (.JAL .x0 36) rfl _ _ rfl rfl
  have k : Late.Check.Micro.Runs (a.setPC (Late.pcAt 217)) (((a.setReg .x1 (Late.pcAt 218))).setPC (Late.pcAt 632)) 1 1 := by
    apply Late.Check.Micro.one 217 (by decide) (.JAL .x1 1660) rfl _ _ rfl
    change some (((a.setPC (Late.pcAt 217)).setReg .x1 (Late.pcAt 217+4)).setPC (Late.pcAt 217+signExtend21 1660))=_
    rfl
  exact (h.trans j).trans k

attribute [local irreducible] Late.Check.lower

theorem hashRecord (o : Oracle) (input : CheckInput) (batch : input.positions.card=BATCH)
    (n : Nat) (small : n<128) (s : MachineState) (inv : RecordInvariant o.compression input n s) :
    ∃ t k, k≤1400 ∧ Runs o s t k 20 ∧ HashedFrame o input n t ∧ Late.Check.Micro.High s t := by
  let i:=Late.Check.recordIndex input.positions n
  let v:=Late.Check.recordValue input n
  let a:=7784632352+256*n
  let p:=12079599648+510*n
  have present : n < input.positions.card := by rw [batch];exact small
  have pbound : p+536≤MEMORY_BYTES := by unfold p MEMORY_BYTES;omega
  have vp : Late.Open.AddrOK a 256 := ⟨by unfold a;omega,by unfold a MEMORY_BYTES;omega⟩
  have ix (w : Word) (h : w.toNat=7650414624+8*n) :
      s.getMem w=(Late.submission.initialState .check input).getMem w :=
    inv.inputWords w (by rw [h];omega) (by rw [h];omega) (by rw [h];unfold MEMORY_BYTES;omega)
  have indexData : s.getMem (s.getReg .x24)=Late.Open.W i.val := by
    rw [inv.indexPtr,ix _ (by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)])]
    exact Late.Check.loaded_index input n present
  have safe : accessValid (s.getReg .x24) 8 := by rw [inv.indexPtr];apply addrOK8 <;> omega
  have valueR : readBuffer s a 256=v :=
    (readHighA s _ inv.inputWords a 256 (by unfold a;omega) vp.2).trans (Late.Check.loaded_value input n present)
  have fixed : Late.Check.start input n=510*n := by
    unfold Late.Check.start Late.Check.stride;rw [if_pos batch];omega
  have saltR : readBuffer s p 24=Late.Check.salt input n := by
    rw [readHighA s _ inv.inputWords p 24 (by unfold p;omega) (by omega),Late.Check.salt,fixed];rfl
  have pcs : s.pc=Late.pcAt 207 := by rw [inv.pc,if_neg (by omega)];rfl
  have en := enterBatch s pcs safe
  let e := ((s.setReg .x20 (s.getMem (s.getReg .x24))).setReg .x1 (Late.pcAt 218)).setPC (Late.pcAt 632)
  have er (r : Reg) (n20 : r ≠ .x20) (n1 : r ≠ .x1) : e.getReg r = s.getReg r := by
    simp only [e, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm n20),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm n1)]
  have e20 : e.getReg .x20 = Late.Open.W i.val := by
    simp only [e, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x1 ≠ .x20),
      MachineState.getReg_setReg_eq (by decide : Reg.x20 ≠ .x0)]
    exact indexData
  have emem : e.mem = s.mem := rfl
  obtain ⟨u,k1,lf⟩ := Late.Check.Micro.CKBLeaf.leafRun o e i (Late.Check.salt input n) v a p rfl
    ((er _ (by decide) (by decide)).trans inv.valuePtr) e20
    ((er _ (by decide) (by decide)).trans inv.proofPtr) ((er _ (by decide) (by decide)).trans inv.scratch)
    (by simp only [e, MachineState.getReg_setPC, MachineState.getReg_setReg_eq (by decide : Reg.x1 ≠ .x0)])
    vp (by unfold p; omega) (by omega) (by unfold a;omega) (by unfold p;omega)
    ((Late.read_congr_mem e s _ _ emem).trans valueR) ((Late.read_congr_mem e s _ _ emem).trans saltR)
  have eh : Late.Check.Micro.High s e := Late.Check.Micro.High.memory emem
  have readP (x m : Nat) (hx : 12079599648 ≤ x) (fit : x+m ≤ MEMORY_BYTES) :
      readBuffer u x m = readBuffer (Late.submission.initialState .check input) x m := by
    rw [lf.high _ _ (by omega) fit, Late.read_congr_mem e s _ _ emem, readHighA s _ inv.inputWords _ _ (by omega) fit]
  have dataA (j : Nat) (hj : j<3) : readBuffer u (p+24+32*j) 32 = Late.Check.sibling input n j := by
    rw [readP _ _ (by unfold p; omega) (by omega), Late.Check.sibling, if_neg (by omega)]
    unfold Late.Check.proofAt
    have lp : Late.submission.layout.proof = 12079599648 := rfl
    rw [fixed, lp]
    congr 1; unfold p; omega
  have dataB (j : Nat) (hj : j<13) : widen (readBuffer u (p+24+96+30*j) 30) = Late.Check.sibling input n (3+j) := by
    rw [readP _ _ (by unfold p; omega) (by omega), Late.Check.sibling, if_pos ⟨batch, by omega⟩]
    unfold Late.Check.proofAt
    have lp : Late.submission.layout.proof = 12079599648 := rfl
    rw [fixed, lp]
    congr 2; unfold p; omega
  have u21 : u.getReg .x21 = 256 := (lf.keep _ (by decide)).trans ((er _ (by decide) (by decide)).trans inv.scratch)
  obtain ⟨t,k2,done⟩ := Late.Check.Micro.CKBPath.fullPath o u (p+24) i (Late.Check.sibling input n) lf.pc u21
    lf.proofPtr ((lf.keep _ (by decide)).trans e20) (by unfold p; omega) (by unfold p; omega) (by omega)
    dataA dataB
  have keepAll (r : Reg) (hr : r ∈ [Reg.x8, .x19, .x24, .x26, .x27, .x30]) (hs : r ∈ Late.Check.Micro.stable)
      (hk : r ∈ Late.Check.Micro.CKBPath.keepRegs) (n20 : r ≠ .x20) (n1 : r ≠ .x1) :
      t.getReg r = s.getReg r := (done.keep r hk).trans ((lf.keep r hs).trans (er r n20 n1))
  refine ⟨t,3+k1+k2,by have :=lf.budget;have :=done.budget;omega,?_,?_,(eh.trans lf.high).trans done.high⟩
  · exact ((Late.Check.Normal.deterministic o en).trans lf.runs).trans done.runs
  · refine ⟨done.pc,?_,?_,?_,?_,?_,done.scratch,?_,?_,?_,?_⟩
    · rw [done.index]; rfl
    · exact (done.keep _ (by decide)).trans ((lf.keep _ (by decide)).trans ((er _ (by decide) (by decide)).trans inv.indexPtr))
    · rw [done.keep _ (by decide), lf.valPtr]; exact congrArg Late.Open.W (by unfold a;omega)
    · rw [done.proof]; exact congrArg Late.Open.W (by unfold p;omega)
    · exact (done.keep _ (by decide)).trans ((lf.keep _ (by decide)).trans ((er _ (by decide) (by decide)).trans inv.remaining))
    · exact (done.keep _ (by decide)).trans ((lf.keep _ (by decide)).trans ((er _ (by decide) (by decide)).trans inv.depth))
    · exact (done.keep _ (by decide)).trans ((lf.keep _ (by decide)).trans ((er _ (by decide) (by decide)).trans inv.slots))
    · exact (done.keep _ (by decide)).trans ((lf.keep _ (by decide)).trans ((er _ (by decide) (by decide)).trans inv.root))
    · unfold lowerHash Late.Check.lower
      rw [done.digest, lf.digest]

end CommitGolfCandidate.PairCap.Batch
