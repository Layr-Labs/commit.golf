import CommitGolfCandidate.Stage3cBucketState
import CommitGolfCandidate.Stage3cCheckCopy
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W Outside)
def bucketAddress (j : Nat) :=compBase+32*j
def bucketSpan:=17408
theorem BucketTable.same {H x n s t} (old : BucketTable H x n s) (mem : t.mem=s.mem) : BucketTable H x n t :=
  ⟨fun j h=>(Open.byte_mem mem _).trans (old.mark j h),fun j h v e=>(read_buffer_memory_congr t s mem _ _).trans (old.data j h v e),
    fun j h hi al=>(congrFun mem _).trans (old.blank j h hi al)⟩

theorem BucketTable.after_record {H x n s t} (old : BucketTable H x n s) (frame : RecordFrame s t) : BucketTable H x n t := by
  have mid (a : Nat) (al : a%8=0) (small : marksBuf≤a) (high : a<saltBuf) :
      Open.wordAt t a=Open.wordAt s a:= frame a (by unfold saltBuf at high;unfold MEMORY_BYTES;omega) al
      (Or.inr (by unfold leafBuf marksBuf at *;omega)) (Or.inl high)
  have bytes (a : Nat) (lo : marksBuf≤a) (hi : a<saltBuf) : Open.byteAt t a=Open.byteAt s a:=by
    rw [Open.byte_word,Open.byte_word s,mid _ (by omega) (by unfold marksBuf at lo ⊢;omega) (by omega)]
  refine ⟨fun j h=>(bytes _ (by omega) (by dsimp [marksBuf,saltBuf];omega)).trans (old.mark j h),?_,?_⟩
  · intro j bound v e
    apply Eq.trans _ (old.data j bound v e)
    unfold readBuffer;apply congrArg (BitVec.ofNat _);apply Finset.sum_congr rfl;intro k hk
    have small:=Finset.mem_range.mp hk
    exact congrArg (fun w : Byte=>w.toNat*2^(8*k)) (bytes _ (by dsimp [marksBuf,compBase];omega) (by dsimp [compBase,saltBuf];omega))
  · intro j lo hi al;exact (mid j al ((by decide : marksBuf≤capBase).trans lo) hi).trans (old.blank j lo hi al)

def flagWrite (s : MachineState) (j : Nat) :=s.setByte (W (marksBuf+j)) 1
theorem flag_outside (s : MachineState) (j : Nat) (small : j<512) : Outside s (flagWrite s j) marksBuf 512 := by
  intro a inside al away
  apply MachineState.getMem_setMem_ne;intro eq
  change W a=alignToDword (W (marksBuf+j)) at eq
  rw [show alignToDword (W (marksBuf+j))=W (marksBuf+8*(j/8)) from word_address marksBuf j (by decide)] at eq
  have num:=congrArg BitVec.toNat eq
  change a<2^36 at inside
  simp only [W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : a<2^64),Nat.mod_eq_of_lt (by dsimp [marksBuf];omega : marksBuf+8*(j/8)<2^64)] at num;omega

structure BucketWrite (o : Oracle) (s t : MachineState) (j : Nat) : Prop where
  run : Flow o s t 10 0
  pc : t.pc=pcAt 799
  copied : Open.Copied (flagWrite s j) t digestBuf (bucketAddress j) 4
  keep : ∀ q,q≠.x28→q≠.x30→t.getReg q=s.getReg q
private def saveCopy : CopySpec:=⟨.x30,.x27,.x29,0,0⟩
theorem save_bucket (o : Oracle) (s : MachineState) (j : Nat) (small : j<512) (pc : s.pc=pcAt 789)
    (mark : s.getReg .x7=W (marksBuf+j)) (to_ : s.getReg .x29=W (bucketAddress j)) (value : s.getReg .x27=W digestBuf) :
    ∃ t,BucketWrite o s t j := by
  let u:=(s.setReg .x28 1).setPC (pcAt 790)
  let v:=(flagWrite u j).setPC (pcAt 791)
  have one:=imm_step o s 789 .x28 .x0 1 1 pc (known (by decide +kernel)) rfl
  have loc : u.getReg .x7+signExtend12 0=W (marksBuf+j):=(BitVec.add_zero _).trans mark
  have ok : memoryArgumentsValid u (.SB .x7 .x28 0)=true:=by
    change accessValid (_+_) 1=true;rw [loc];apply access_ok <;> dsimp [marksBuf,MEMORY_BYTES] <;> omega
  have store : ordinaryStep u (.base (.SB .x7 .x28 0))=some v:=by
    simp only [ordinaryStep,ok,↓reduceIte];change some ((u.setByte _ 1).setPC (u.pc+4))=_;rw [loc];rfl
  have write:=one_flow o (show u.pc=pcAt 790 from rfl) (known (by decide +kernel)) store
  have stable (q : Reg) (n : q≠.x28) : v.getReg q=s.getReg q:=by
    apply Eq.trans _ (show u.getReg q=s.getReg q from MachineState.getReg_setPC.trans (MachineState.getReg_setReg_ne _ _ _ _ n.symm))
    cases q <;> rfl
  have hi : bucketAddress j+32≤MEMORY_BYTES:=by dsimp [bucketAddress,compBase,MEMORY_BYTES];omega
  have al : bucketAddress j%8=0:=by dsimp [bucketAddress,compBase];omega
  obtain ⟨t,done_⟩:=copy_words o v 791 digestBuf (bucketAddress j) 4 saveCopy (by unfold CopySites;decide +kernel) (by decide) (by decide) rfl
    ((stable _ (by decide)).trans value) ((stable _ (by decide)).trans to_) ⟨by decide,by decide⟩ ⟨al,hi⟩
    (Or.inl (by change digestBuf+32≤bucketAddress j;dsimp [digestBuf,bucketAddress,compBase];omega))
  have mem : v.mem=(flagWrite s j).mem:=rfl
  have saved : Open.Copied (flagWrite s j) t digestBuf (bucketAddress j) 4 :=
    ⟨fun q h a outside=>(done_.data.outside q h a outside).trans (congrFun mem _),
      fun i h=>(done_.data.words i h).trans (congrFun mem _)⟩
  exact ⟨t,⟨(one.trans write).trans done_.run,done_.pc,saved,fun q a b=>(done_.keep q b).trans (stable q a)⟩⟩
end CommitGolfCandidate.Chained.BinaryMachine.Check
