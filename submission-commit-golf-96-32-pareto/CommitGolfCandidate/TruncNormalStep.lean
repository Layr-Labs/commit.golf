import CommitGolfCandidate.TruncNormalHash
namespace CommitGolfCandidate.Trunc.Normal
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 10000
set_option maxHeartbeats 190000
attribute [local irreducible] Batch.obs checkEvaluation execute checkRootWordsState normalized readBuffer mathRoot

def Terminal (o : Oracle) (s : MachineState) (k q : Nat) (ex : Exit) :=
  ∀ fuel,Batch.obs o (k+fuel) s=(ex,q)

theorem runsThen {o s t k j q r ex} (run : Batch.Runs o s t k q) (fin : Terminal o t j r ex) :
    Terminal o s (k+j) (q+r) ex := by intro fuel;rw [Nat.add_assoc,run,fin]

private theorem nextFrame (i : CheckInput) (n : Nat) (hn : n < i.positions.card) (t : MachineState)
    (idx : t.getReg .x24=BitVec.ofNat 64 (6442455072+8*n))
    (vp : t.getReg .x8=BitVec.ofNat 64 (6576672800+256*(n+1)))
    (pp : t.getReg .x25=BitVec.ofNat 64 (10871640096+784*(n+1)))
    (remaining : t.getReg .x27=BitVec.ofNat 64 (i.positions.card-n))
    (rt : t.getReg .x26=4294971392) (scratch : t.getReg .x21=256) (depth : t.getReg .x30=24) (slots : t.getReg .x19=0)
    (high : ∀ w : Word,352≤w.toNat → t.getMem w=(inputState i).getMem w) :
    Frame i (n+1) (checkPositionNextState (checkRootWordsState t 66 4)) := by
  let c:=checkRootWordsState t 66 4
  have keep (r : Reg) (a : r≠.x6) (b : r≠.x7) := (check_root_words_preserves t 66 4 r a b).1
  have rest : c.getReg .x27-1=BitVec.ofNat 64 (i.positions.card-(n+1)) := by
    rw [keep _ (by decide) (by decide),remaining,show i.positions.card-n=(i.positions.card-(n+1))+1 by omega,BitVec.ofNat_add]
    exact BitVec.add_sub_cancel _ 1
  have bound:=positionCount i.positions
  have exhausted : c.getReg .x27-1=0 ↔ n+1=i.positions.card := by
    rw [rest];constructor
    · intro e;have val:=congrArg BitVec.toNat e
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)] at val;change _=0 at val;omega
    · intro e;rw [e,Nat.sub_self];rfl
  refine ⟨?_,(keep _ (by decide) (by decide)).trans vp,(keep _ (by decide) (by decide)).trans pp,
    rest,(keep _ (by decide) (by decide)).trans rt,(keep _ (by decide) (by decide)).trans scratch,
    (keep _ (by decide) (by decide)).trans depth,(keep _ (by decide) (by decide)).trans slots,?_,?_⟩
  · change c.getReg .x24+8=_
    rw [keep _ (by decide) (by decide),idx,show 6442455072+8*(n+1)=(6442455072+8*n)+8 by omega];exact (BitVec.ofNat_add _ _).symm
  · change (if c.getReg .x27-1=0 then _ else _)=_
    by_cases e : n+1=i.positions.card
    · rw [if_pos (exhausted.mpr e),if_pos e]
    · rw [if_neg (fun h=>e (exhausted.mp h)),if_neg e]
  · intro w hw;apply Eq.trans _ (high w hw)
    exact congrArg (fun mem : Word→Word=>mem w) (check_root_words_preserves t 66 4 .x0 (by decide) (by decide)).2

theorem oneRecord (o : Oracle) (i : CheckInput) (mode : i.positions.card≠BATCH) (n : Nat) (hn : n < i.positions.card)
    (s : MachineState) (f : Frame i n s) :
    (mathRoot o i n≠i.commitment ∧ ∃ k≤1480,Terminal o s k 28 .failure) ∨
    (mathRoot o i n=i.commitment ∧ ∃ t k,k≤1480 ∧ Batch.Runs o s t k 28 ∧ Frame i (n+1) t) := by
  let m:=normalized o s
  obtain ⟨k,hk,run,mpc,idx,vp,pp,keep,mem,value⟩:=hash o i mode n hn s f
  have z : m.getReg .x19=0 := (keep _ (by decide)).trans f.slots
  let v:=m.setPC (loc 64)
  let t:=checkTargetState v
  have before : Batch.Runs o s t (k+2+2) 28 :=
    Batch.runs_trans (Batch.runs_trans run (Batch.pureBlockRuns (fun j=>normalExit m mpc z j false)))
      (Batch.pureBlockRuns (fun j=>check_target v rfl j false))
  have same (r : Reg) (h : r≠.x7) (h' : r≠.x23) : t.getReg r=m.getReg r := by
    simp only [t,v,checkTargetState,MachineState.getReg_setPC,MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h')]
  have tptr : t.getReg .x23=4294971392 := by
    have root:=(keep .x26 (by decide)).trans f.root
    change m.getReg .x26+(m.getReg .x20<<<5)=_
    rw [idx,root];rfl
  have scratch : t.getReg .x21=256:=(same _ (by decide) (by decide)).trans ((keep _ (by decide)).trans f.scratch)
  have high (w : Word) (hw : 352≤w.toNat) : t.getMem w=(inputState i).getMem w := (mem w hw).trans (f.high w hw)
  have original : readBuffer t 4294971392 32=i.commitment :=
    (readHigh t _ high _ (by decide) (by decide) (by decide)).trans (check_input_commitment i)
  have left : readBuffer t 256 32=mathRoot o i n := (read_buffer_memory_congr t m rfl 256 32).trans value
  have test : (∀ w<4,t.getMem (t.getReg .x21+BitVec.ofNat 64 (8*w))=t.getMem (t.getReg .x23+BitVec.ofNat 64 (8*w))) ↔ mathRoot o i n=i.commitment := by
    rw [←left,←original,read_digest_eq_iff t t 256 4294971392 (by decide) (by decide)]
    rw [scratch,tptr];simp only [BitVec.ofNat_add];rfl
  have a : ∀ w<4,accessValid (t.getReg .x21+BitVec.ofNat 64 (8*w)) 8 := by rw [scratch];intro w hw;interval_cases w <;> decide
  have b : ∀ w<4,accessValid (t.getReg .x23+BitVec.ofNat 64 (8*w)) 8 := by rw [tptr];intro w hw;interval_cases w <;> decide
  by_cases valid : mathRoot o i n=i.commitment
  · right;refine ⟨valid,checkPositionNextState (checkRootWordsState t 66 4),k+2+2+12+3,by omega,?_,?_⟩
    · have endPC:=(check_root_words_pc t 66 (Or.inl rfl) rfl 4 (by decide) (test.mpr valid))
      exact Batch.runs_trans (Batch.runs_trans before (Batch.pureBlockRuns (fun j=>check_root_matches t 66 (Or.inl rfl) rfl a b (test.mpr valid) j false)))
        (Batch.pureBlockRuns (fun j=>check_position_next _ endPC j false))
    · apply nextFrame i n hn t
      · exact (same _ (by decide) (by decide)).trans ((keep _ (by decide)).trans f.indexPtr)
      · rw [same _ (by decide) (by decide),vp,f.valuePtr,show 6576672800+256*(n+1)=(6576672800+256*n)+256 by omega];exact (BitVec.ofNat_add _ _).symm
      · rw [same _ (by decide) (by decide),pp,f.proofPtr,show 10871640096+784*(n+1)=(10871640096+784*n)+784 by omega];exact (BitVec.ofNat_add _ _).symm
      · exact (same _ (by decide) (by decide)).trans ((keep _ (by decide)).trans f.remaining)
      · exact (same _ (by decide) (by decide)).trans ((keep _ (by decide)).trans f.root)
      · exact scratch
      · exact (same _ (by decide) (by decide)).trans ((keep _ (by decide)).trans f.depth)
      · exact (same _ (by decide) (by decide)).trans z
      · exact high
  · left;refine ⟨valid,k+2+2+15,by omega,runsThen (r:=0) (j:=15) before ?_⟩
    intro j
    obtain ⟨r,tr,fail,_⟩:=check_root_rejects t 66 (Or.inl rfl) rfl a b (fun h=>valid (test.mp h)) j false
    rw [Batch.obs,tr,check_evaluation_pure];exact Prod.ext fail rfl
end CommitGolfCandidate.Trunc.Normal
