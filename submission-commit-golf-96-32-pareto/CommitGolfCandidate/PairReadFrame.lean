import CommitGolfCandidate.PairRowHash
namespace CommitGolfCandidate.PairCap.Batch
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 10000
set_option maxHeartbeats 250000
attribute [local irreducible] readBuffer rowHash

def tested (s : MachineState) := afterTest (bucketState s)

theorem testPreserves (s : MachineState) : (tested s).regs=(bucketState s).regs ∧ (tested s).mem=(bucketState s).mem := by
  dsimp [tested,afterTest,execInstrBr];split <;> exact ⟨rfl,rfl⟩

theorem testInfo (s : MachineState) (pc : s.pc=5220) (u : Fin 256) (idx : s.getReg .x20=BitVec.ofNat 64 u.val) :
    (tested s).getReg .x22=BitVec.ofNat 64 (flag u.val) ∧ (tested s).getReg .x23=BitVec.ofNat 64 (cell u.val) ∧
    (tested s).getReg .x21=s.getReg .x21 ∧ (tested s).mem=s.mem := by
  obtain ⟨_,f,c,_,mm⟩ := bucketInfo s pc u idx
  have same := (testPreserves s).1
  have keep : (bucketState s).getReg .x21=s.getReg .x21 := rfl
  exact ⟨(congrFun same .x22).trans f,(congrFun same .x23).trans c,(congrFun same .x21).trans keep,(testPreserves s).2.trans mm⟩

theorem hashedTable (o : Oracle) (s : MachineState) (hs : s.getReg .x21=256) (u : Fin 256) :
    storedAt (rowHash o s) u=storedAt s u := by
  have fb : ∀ v : Fin 256,352 ≤ (alignToDword (BitVec.ofNat 64 (flag v.val))).toNat := by decide
  have cb : ∀ v : Fin 256, cell v.val%8=0 ∧ 352≤cell v.val ∧ cell v.val+32≤2^64 := by decide
  have byte : (rowHash o s).getByte (BitVec.ofNat 64 (flag u.val)) = s.getByte _ :=
    congrArg (fun x => extractByte x (byteOffset (BitVec.ofNat 64 (flag u.val)))) (hashedOutside o s hs _ (fb u))
  have digest : readBuffer (rowHash o s) (cell u.val) 32=readBuffer s (cell u.val) 32 := by
    apply read_digest_congr _ _ _ (cb u).1
    intro j hj
    apply hashedOutside o s hs
    have c := (cb u).2
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)];omega
  simp only [storedAt,byte,digest]

theorem hashGap (o : Oracle) (s : MachineState) (hs : s.getReg .x21=256) (p : Fin 128) :
    readBuffer (rowHash o s) (16384+96*p.val+64) 32=readBuffer s (16384+96*p.val+64) 32 := by
  apply read_digest_congr _ _ _ (by omega)
  intro j hj;apply hashedOutside o s hs
  have hp:=p.isLt
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)];omega

theorem nextMem (s : MachineState) : (nextEdge s).mem=s.mem := by
  dsimp only [nextEdge,execInstrBr];split <;> rfl

theorem comparedMem (s : MachineState) (pc : s.pc=5220) (u : Fin 256) (idx : s.getReg .x20=BitVec.ofNat 64 u.val) :
    (compared s).mem=s.mem := by
  unfold compared;rw [nextMem]
  have jump (m : MachineState) : (execInstrBr m (.JAL .x0 44)).mem = m.mem := rfl
  rw [jump]
  change (top_checkRootWordsState (tested s) 294 4).mem=s.mem
  rw [(top_check_root_words_preserves _ _ _ .x19 (by decide) (by decide)).2]
  exact (testInfo s pc u idx).2.2.2

end CommitGolfCandidate.PairCap.Batch
