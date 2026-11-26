import CommitGolfCandidate.TruncCheckAncestor
import CommitGolfCandidate.TruncAuthentication
import CommitGolfCandidate.TruncNormalLatches
import CommitGolfCandidate.TruncBProgress
namespace CommitGolfCandidate.Trunc.Normal
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 12000
set_option maxHeartbeats 190000
attribute [local irreducible] readBuffer checkEvaluation Check.rec_checkPositionHash

theorem positionCount (ps : Positions) : ps.card≤16777216 := by
  change ps.card≤LENGTH;simpa [Index] using Finset.card_le_univ ps

def inputState (i : CheckInput) := CommitGolfCandidate.submission.initialState .check i

structure Frame (i : CheckInput) (n : Nat) (s : MachineState) : Prop where
  indexPtr : s.getReg .x24=BitVec.ofNat 64 (6442455072+8*n)
  valuePtr : s.getReg .x8=BitVec.ofNat 64 (6576672800+256*n)
  proofPtr : s.getReg .x25=BitVec.ofNat 64 (10871640096+784*n)
  remaining : s.getReg .x27=BitVec.ofNat 64 (i.positions.card-n)
  root : s.getReg .x26=4294971392
  scratch : s.getReg .x21=256
  depth : s.getReg .x30=24
  slots : s.getReg .x19=0
  pc : s.pc=if n=i.positions.card then 4420 else 4156
  high : ∀ w : Word,352≤w.toNat → s.getMem w=(inputState i).getMem w

def normalized (o : Oracle) (s : MachineState) :=
  (checkEvaluation o (Check.rec_checkPositionHash (s.setPC (loc 232)) 24)).1

def mathRoot (o : Oracle) (i : CheckInput) (n : Nat) :=
  Trunc.recordRoot o.compression (recordValue i n) (recordSalt i n) (recordIndex i n) (normalSibling i n)

theorem addrOK8 (a : Nat) (bound : a+8 ≤ 2^36) (align : a%8=0) :
    accessValid (BitVec.ofNat 64 a) 8 = true := by
  simp only [accessValid,rangeValid,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : a<2^64),
    Bool.and_eq_true,decide_eq_true_eq,MEMORY_BYTES];exact ⟨bound,align⟩

theorem readHigh (s t : MachineState) (same : ∀ w : Word, 352≤w.toNat → s.getMem w=t.getMem w)
    (a : Nat) (high : 352≤a) (aligned : a%8=0) (bound : a+32≤2^64) :
    readBuffer s a 32 = readBuffer t a 32 := by
  apply read_digest_congr _ _ _ aligned
  intro i hi;apply same
  all_goals rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : a+8*i<2^64)];omega

theorem readHighSalt (s t : MachineState) (same : ∀ w : Word, 352≤w.toNat → s.getMem w=t.getMem w)
    (a : Nat) (high : 352≤a) (aligned : a%8=0) (bound : a+16≤2^64) :
    readBuffer s a 16 = readBuffer t a 16 := by
  apply read_salt_congr _ _ _ aligned
  intro i hi;apply same
  all_goals rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : a+8*i<2^64)];omega

private theorem leafCalls (o : Oracle) (n : Nat) (s : MachineState) :
    (checkEvaluation o (checkLeafLoop s n)).2=n := by
  induction n generalizing s with
  | zero => rw [checkLeafLoop,check_evaluation_pure]
  | succ k ih =>
    rw [checkLeafLoop,check_evaluation_public_bind]
    simp [ih,Nat.add_comm]

private theorem pathCalls (o : Oracle) (n : Nat) (s : MachineState) :
    (checkEvaluation o (Check.rec_checkPathLoop s n)).2=n := by
  induction n generalizing s with
  | zero => rw [Check.rec_checkPathLoop,check_evaluation_pure]
  | succ k ih =>
    rw [Check.rec_checkPathLoop,check_evaluation_public_bind]
    simp [ih,Nat.add_comm]

theorem recordCalls (o : Oracle) (s : MachineState) :
    (checkEvaluation o (Check.rec_checkPositionHash s 24)).2=28 := by
  simp only [Check.rec_checkPositionHash,check_evaluation_bind,check_evaluation_pure,checkLeafSubroutineRun,leafCalls,pathCalls]
  exact congrArg (fun t : Digest × Nat => t.2+3+(24+0))
    (check_evaluation_public o (.inl (leafQuery (checkLeafInitCopyState (PairCap.rec_checkPositionState s)))))


theorem hash (o : Oracle) (i : CheckInput) (mode : i.positions.card≠BATCH) (n : Nat) (hn : n < i.positions.card)
    (s : MachineState) (f : Frame i n s) :
    let t:=normalized o s
    ∃ steps≤1459,Batch.Runs o s t steps 28 ∧ t.pc=5220 ∧ t.getReg .x20=0 ∧
      t.getReg .x8=s.getReg .x8+256 ∧ t.getReg .x25=s.getReg .x25+784 ∧
      (∀ r∈[Reg.x19,.x21,.x24,.x26,.x27,.x30],t.getReg r=s.getReg r) ∧
      (∀ w : Word,352≤w.toNat → t.getMem w=s.getMem w) ∧ readBuffer t 256 32=mathRoot o i n := by
  dsimp only
  let start:=s.setPC (loc 232)
  let ix:=recordIndex i n
  have cap : i.positions.card≤16777216:=positionCount _
  have startHigh (w : Word) (hw : 352≤w.toNat) : start.getMem w=(inputState i).getMem w := f.high w hw
  have idx : start.getMem (start.getReg .x24)=BitVec.ofNat 64 ix.val := by
    change s.getMem (s.getReg .x24)=_
    rw [f.indexPtr,f.high _ (by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)];omega)]
    exact check_input_position i n hn
  have idxOK : accessValid (start.getReg .x24) 8 := by rw [MachineState.getReg_setPC,f.indexPtr];apply addrOK8 <;> omega
  have pfOK : ∀ w<98,accessValid (start.getReg .x25+BitVec.ofNat 64 (8*w)) 8 := by
    intro w hw;rw [MachineState.getReg_setPC,f.proofPtr,←BitVec.ofNat_add];apply addrOK8 <;> omega
  have valOK : ∀ w<32,accessValid (start.getReg .x8+BitVec.ofNat 64 (8*w)) 8 := by
    intro w hw;rw [MachineState.getReg_setPC,f.valuePtr,←BitVec.ofNat_add];apply addrOK8 <;> omega
  have init : Batch.Runs o s start 1 0 := Batch.pureBlockRuns (fun k=>recordStart s (by rw [f.pc,if_neg (by omega)];rfl) k false)
  have run : Batch.Runs o start (normalized o s) (114+Check.pathInstructions (start.getMem (start.getReg .x24)) 24) 28 := by
    intro k;unfold Batch.obs
    rw [Check.rec_check_position_hash 24 (by decide) (by decide) start rfl f.depth idxOK f.scratch pfOK valOK k false,check_evaluation_bind]
    simp only [bind_pure_comp,check_evaluation_map,recordCalls];rfl
  have pr:=(Check.path_instruction_bounds (start.getMem (start.getReg .x24)) 24).2
  obtain ⟨endPC,vp,pp,tag,keep⟩:=Check.rec_check_position_hash_registers 24 (by decide) (by decide) start (normalized o s) f.depth (check_evaluation_support o _)
  refine ⟨_,by omega,Batch.runs_trans init run,endPC,?_,vp,pp,keep,?_,?_⟩
  · rw [tag,idx];apply BitVec.eq_of_toNat_eq
    have j : ix.val<16777216:=ix.isLt
    have val : (BitVec.ofNat 64 ix.val).toNat=ix.val:=Nat.mod_eq_of_lt (by omega)
    rw [BitVec.toNat_ushiftRight,val,Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt j
  · intro w hw
    apply Check.rec_check_position_hash_outside o start 24 w f.scratch
    intro j hj eq;have h:=congrArg BitVec.toNat eq
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)] at h;omega
  · refine Check.rec_check_record_ancestor o start 24 (6576672800+256*n) (10871640096+784*n)
      (recordValue i n) (recordSalt i n) ix (normalSibling i n) (Or.inr rfl) f.depth (by simp [show start.getReg .x19=0 from f.slots]) (by decide)
      f.scratch f.valuePtr f.proofPtr (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) ?_ ?_ idx ?_
    · intro j hj
      let a:=6576672800+256*n+64*j
      rw [show recordValue i n=i.values ((i.positions.attach.sort (fun q r=>q.val≤r.val))[n]'(by simpa using hn)) by simp [recordValue,hn]]
      trans readBuffer (inputState i) a 64
      · rw [read_compression_halves _ _ (by omega),read_compression_halves _ a (by dsimp [a];omega)]
        apply congrArg₂ BitVec.append <;> apply readHigh start (inputState i) startHigh <;> (try dsimp [a]) <;> omega
      · exact check_input_value_block i n j hn hj
    · unfold recordSalt;rw [if_neg mode];apply readHighSalt start (inputState i) startHigh <;> omega
    · intro j hj;unfold normalSibling;exact readHigh start (inputState i) startHigh _ (by omega) (by omega) (by omega)
end CommitGolfCandidate.Trunc.Normal
