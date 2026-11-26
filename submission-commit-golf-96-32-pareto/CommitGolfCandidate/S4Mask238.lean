import CommitGolfCandidate.TruncMask
namespace CommitGolfCandidate.Trunc
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxHeartbeats 2500000

def pad238 (x : BitVec 256) : BitVec 256 := (0 : BitVec 18) ++ x.extractLsb' 0 238
def maskValue (x : BitVec 256) : Word := (x.extractLsb' 224 16).zeroExtend 64 &&& 16383

theorem pad238_bit (x : BitVec 256) (i : Nat) : (pad238 x).getLsbD i = (decide (i < 238) && x.getLsbD i) := by
  unfold pad238
  rw [BitVec.getLsbD_append]
  by_cases low : i < 238
  · simp [low, BitVec.getLsbD_extractLsb']
  · simp [low]

private theorem high_word (x : BitVec 256) :
    replaceWord32 (x.extractLsb' 192 64) 1 ((maskValue x).truncate 32)=(pad238 x).extractLsb' 192 64 := by
  unfold replaceWord32 maskValue
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_extractLsb',pad238_bit]
  interval_cases i <;> simp (config:={decide:=true})
private theorem low_word (x : BitVec 256) (k : Nat) (hk : k<3) :
    x.extractLsb' (8*(8*k)) 64=(pad238 x).extractLsb' (8*(8*k)) 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb',pad238_bit,decide_eq_true hi,Bool.true_and,
    decide_eq_true (show 8*(8*k)+i<238 by omega)]

theorem loaded238 (s : MachineState) (a : Nat) (v : BitVec 256)
    (al : a%8=0) (fits : a+32≤2^64) :
    (writeBits s (BitVec.ofNat 64 a) v).getHalfword (BitVec.ofNat 64 (a+28))=v.extractLsb' 224 16 := by
  have off : byteOffset (BitVec.ofNat 64 (a+28))=4:=by rw [byte_offset,BitVec.toNat_ofNat];omega
  have addr : alignToDword (BitVec.ofNat 64 (a+28))=BitVec.ofNat 64 (a+8*3):=word_address a 28 al
  rw [MachineState.getHalfword,off,addr,output_word s a 3 v al (by decide)]
  unfold extractHalfword;apply BitVec.eq_of_getLsbD_eq <;> intro bit bounded <;> interval_cases bit <;> simp (config := {decide := true}) [BitVec.getElem_append]

theorem cleared238 (s : MachineState) (a : Nat) (v : BitVec 256)
    (al : a%8=0) (fits : a+32≤2^64) :
    (writeBits s (BitVec.ofNat 64 a) v).setWord32 (BitVec.ofNat 64 (a+28)) ((maskValue v).truncate 32)=
      writeBits s (BitVec.ofNat 64 a) (pad238 v) := by
  have off : byteOffset (BitVec.ofNat 64 (a+28))=4:=by rw [byte_offset,BitVec.toNat_ofNat];omega
  have addr : alignToDword (BitVec.ofNat 64 (a+28))=BitVec.ofNat 64 (a+8*3):=word_address a 28 al
  have same : ((writeBits s (BitVec.ofNat 64 a) v).setWord32 (BitVec.ofNat 64 (a+28)) ((maskValue v).truncate 32)).mem=
      (writeBits s (BitVec.ofNat 64 a) (pad238 v)).mem := by
    funext q
    change ((writeBits s _ v).setWord32 _ _).getMem q=_
    rw [MachineState.setWord32,addr,off]
    by_cases last : q=BitVec.ofNat 64 (a+8*3)
    · subst q;change ((writeBits s _ v).setMem _ _).getMem _=(writeBits s _ (pad238 v)).getMem _
      rw [MachineState.getMem_setMem_eq,output_word s a 3 v al (by decide),output_word s a 3 _ al (by decide)]
      exact high_word v
    · rw [MachineState.getMem_setMem_ne last]
      by_cases someWord : ∃ k<4,q=BitVec.ofNat 64 (a+8*k)
      · obtain ⟨k,hk,rfl⟩:=someWord
        change _=(writeBits s _ (pad238 v)).getMem _
        rw [output_word s a k v al hk,output_word s a k _ al hk]
        have hk3 : k<3:=by
          by_contra! large
          have h3 : k=3:=by omega
          exact last (congrArg (fun j=>BitVec.ofNat 64 (a+8*j)) h3)
        simpa only [←Nat.mul_assoc] using low_word v k hk3
      · have away : ∀ i<32,q≠alignToDword (BitVec.ofNat 64 a+BitVec.ofNat 64 i):=by
          intro i hi e;exact someWord ⟨i/8,by omega,e.trans (by rw [←BitVec.ofNat_add,word_address a i al])⟩
        exact (writeBits_memory_outside s _ q v away).trans (writeBits_memory_outside s _ q (pad238 v) away).symm
  have f:=write_frame s (BitVec.ofNat 64 a) v
  have g:=write_frame s (BitVec.ofNat 64 a) (pad238 v)
  generalize writeBits s (BitVec.ofNat 64 a) v=raw at same f ⊢
  generalize writeBits s (BitVec.ofNat 64 a) (pad238 v)=out at same g ⊢
  cases s;cases raw;cases out
  simp only [MachineState.mk.injEq] at f g
  simp only [MachineState.setWord32,MachineState.setMem,MachineState.mk.injEq] at same ⊢
  simp_all

end CommitGolfCandidate.Trunc
