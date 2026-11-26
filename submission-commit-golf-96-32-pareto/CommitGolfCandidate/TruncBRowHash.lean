import CommitGolfCandidate.TruncBCounts
import CommitGolfCandidate.TruncBPrefix

namespace CommitGolfCandidate.Trunc.Batch
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 10000
set_option maxHeartbeats 250000
attribute [local irreducible] checkEvaluation Check.rec_checkPositionHash readBuffer

def rowHash (o : Oracle) (s : MachineState) := (checkEvaluation o (Check.rec_checkPositionHash s 16)).1
def rowBucket (input : CheckInput) (n : Nat) : Fin 256 :=
  ⟨openingIndex input.positions n / 65536,by have h : openingIndex input.positions n < 16777216 := opening_index_bound _ _; omega⟩

theorem addrOK8 (a : Nat) (bound : a+8 ≤ 2^36) (align : a%8=0) :
    accessValid (BitVec.ofNat 64 a) 8 = true := by
  simp only [accessValid,rangeValid,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : a<2^64),
    Bool.and_eq_true,decide_eq_true_eq,MEMORY_BYTES];exact ⟨bound,align⟩

theorem readHigh (s t : MachineState) (same : ∀ w : Word, 32768≤w.toNat → w.toNat%8=0 → s.getMem w=t.getMem w)
    (a : Nat) (high : 32768≤a) (aligned : a%8=0) (bound : a+32≤2^64) :
    readBuffer s a 32 = readBuffer t a 32 := by
  apply read_digest_congr _ _ _ aligned
  intro i hi;apply same
  all_goals rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : a+8*i<2^64)];omega

theorem readHighSalt (s t : MachineState) (same : ∀ w : Word, 32768≤w.toNat → w.toNat%8=0 → s.getMem w=t.getMem w)
    (a : Nat) (high : 32768≤a) (aligned : a%8=0) (bound : a+16≤2^64) :
    readBuffer s a 16 = readBuffer t a 16 := by
  apply read_salt_congr _ _ _ aligned
  intro i hi;apply same
  all_goals rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : a+8*i<2^64)];omega

theorem wordShift (i : Nat) (b : i<2^24) :
    BitVec.ofNat 64 i >>> 16 = BitVec.ofNat 64 (i/65536) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : i<2^64), Nat.mod_eq_of_lt (by omega : i/65536<2^64)]

theorem hashedOutside (o : Oracle) (s : MachineState) (scratch : s.getReg .x21=256) (w : Word)
    (above : 352 ≤ w.toNat) : (rowHash o s).getMem w = s.getMem w := by
  apply Check.rec_check_position_hash_outside o s 16 w scratch
  intro i hi eqn
  have h := congrArg BitVec.toNat eqn
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)] at h;omega

structure HashedFrame (o : Oracle) (input : CheckInput) (n : Nat) (s : MachineState) : Prop where
  pc : s.pc=5220
  index : s.getReg .x20=BitVec.ofNat 64 (rowBucket input n).val
  ip : s.getReg .x24=BitVec.ofNat 64 (6442455072+8*n)
  vp : s.getReg .x8=BitVec.ofNat 64 (6576672800+256*(n+1))
  pp : s.getReg .x25=BitVec.ofNat 64 (10871640096+528*(n+1))
  remaining : s.getReg .x27=BitVec.ofNat 64 (128-n)
  scratch : s.getReg .x21=256
  depth : s.getReg .x30=16
  slots : s.getReg .x19=10871707680
  root : s.getReg .x26=4294971392
  digest : readBuffer s 256 32=lowerHash o.compression input n

theorem hashRecord (o : Oracle) (input : CheckInput) (batch : input.positions.card=BATCH)
    (n : Nat) (small : n<128) (s : MachineState) (inv : RecordInvariant o.compression input n s) :
    ∃ steps ≤ 1010, Runs o s (rowHash o s) steps 20 ∧ HashedFrame o input n (rowHash o s) := by
  let i := recordIndex input n
  have present : n < input.positions.card := by rw [batch];exact small
  have idxval : s.getMem (s.getReg .x24) = BitVec.ofNat 64 i.val := by
    have aligned : (BitVec.ofNat 64 (6442455072+8*n)).toNat=6442455072+8*n := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : 6442455072+8*n<2^64)]
    rw [inv.indexPtr,inv.inputWords _ (by rw [aligned];omega) (by rw [aligned];omega)]
    exact check_input_position input n present
  have idxOK : accessValid (s.getReg .x24) 8 := by rw [inv.indexPtr];apply addrOK8 <;> omega
  have pfOK : ∀ w<66,accessValid (s.getReg .x25 + BitVec.ofNat 64 (8*w)) 8 := by
    intro w hw;rw [inv.proofPtr,← BitVec.ofNat_add];apply addrOK8 <;> omega
  have valOK : ∀ w<32,accessValid (s.getReg .x8 + BitVec.ofNat 64 (8*w)) 8 := by
    intro w hw;rw [inv.valuePtr,← BitVec.ofNat_add];apply addrOK8 <;> omega
  have price := recordRuns o s (by rw [inv.pc,if_neg (by omega)]) inv.depth idxOK inv.scratch pfOK valOK
  dsimp only at price
  rw [recordCalls] at price
  refine ⟨_,by have := (Check.path_instruction_bounds (s.getMem (s.getReg .x24)) 16).2;omega,price,?_⟩
  obtain ⟨pc,vp,pp,tag,keep⟩ := Check.rec_check_position_hash_registers 16 (by decide) (by decide) s (rowHash o s)
    inv.depth (check_evaluation_support o _)
  refine ⟨pc,?_,(keep _ (by decide)).trans inv.indexPtr,?_,?_,
    (keep _ (by decide)).trans inv.remaining,(keep _ (by decide)).trans inv.scratch,
    (keep _ (by decide)).trans inv.depth,(keep _ (by decide)).trans inv.slots,
    (keep _ (by decide)).trans inv.root,?_⟩
  · rw [tag,idxval];exact wordShift _ i.isLt
  · rw [vp,inv.valuePtr,show 6576672800+256*(n+1)=(6576672800+256*n)+256 by omega];exact (BitVec.ofNat_add _ 256).symm
  · rw [pp,inv.proofPtr,← BitVec.ofNat_add];congr 1
  · refine Check.rec_check_record_ancestor o s 16 (6576672800+256*n) (10871640096+528*n)
      (recordValue input n) (batchSalt input n) i (lowerSibling input n)
      (Or.inl rfl) inv.depth (by rw [inv.slots];decide) (by decide) inv.scratch inv.valuePtr inv.proofPtr (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) ?_ ?_ idxval ?_
    · intro j hj
      let a := 6576672800+256*n+64*j
      have valEq : recordValue input n = input.values ((input.positions.attach.sort (fun i j => i.val≤j.val))[n]'(by simpa using present)) := by simp [recordValue,present]
      rw [valEq]
      trans readBuffer (CommitGolfCandidate.submission.initialState .check input) a 64
      · rw [read_compression_halves _ _ (by omega),read_compression_halves _ a (by dsimp [a];omega)]
        apply congrArg₂ BitVec.append <;> apply readHigh _ _ inv.inputWords <;> (try dsimp [a]) <;> omega
      · exact check_input_value_block input n j present hj
    · exact readHighSalt _ _ inv.inputWords _ (by omega) (by omega) (by omega)
    · intro j hj;exact readHigh _ _ inv.inputWords _ (by omega) (by omega) (by omega)
end CommitGolfCandidate.Trunc.Batch
