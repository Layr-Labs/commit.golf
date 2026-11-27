import CommitGolfCandidate.Stage3cCheckProjection
import CommitGolfCandidate.Stage3cClearOffset
import CommitGolfCandidate.Stage3cCheckLeafData
import CommitGolfCandidate.Stage3cCheckCalc
import CommitGolfCandidate.Stage3cTagCore
import CommitGolfCandidate.Stage3cCompletedParent
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Chained
open Open (W Outside wordAt)
def ChainOutside (s t : MachineState) (dst : Nat) := ∀ q<MEMORY_BYTES,q%8=0 →
  (q<rowBuf ∨ rowBuf+352≤q) → (q<dst ∨ dst+32≤q) → wordAt t q=wordAt s q
theorem ChainOutside.trans {s t u a} (x : ChainOutside s t a) (y : ChainOutside t u a) : ChainOutside s u a :=
  fun q h al lo hi=>(y q h al lo hi).trans (x q h al lo hi)
theorem ChainOutside.same {s t a} (m : t.mem=s.mem) : ChainOutside s t a:=fun q _ _ _ _=>congrFun m (W q)
theorem ChainOutside.inside {s t a n dst} (x : Outside s t a n) (lo : rowBuf≤a) (hi : a+n≤rowBuf+352) : ChainOutside s t dst :=
  fun q h al away _=>x q h al (by omega)
theorem ChainOutside.output {s t dst} (m : Outside s t dst 32) : ChainOutside s t dst:=fun q h a _ away=>m q h a away

structure ChainSys (h : Height) (dst : Nat) (s : MachineState) : Prop where
  address : s.getReg .x26=W chainBuf
  save : s.getReg .x28=W dst
  width : s.getReg .x31=W (wireWidth h)
  amount : s.getReg .x30=W (calls h)
  selector : s.getReg .x5=0
  bytes : s.getReg .x11=96
  mode : s.getReg .x13=0

def sysRegs : List Reg:=[.x26,.x28,.x31,.x30,.x5,.x11,.x13]
theorem ChainSys.kept {h dst s t} (r : ChainSys h dst s) (k : ∀ q∈sysRegs,t.getReg q=s.getReg q) : ChainSys h dst t :=
  ⟨(k _ (by decide)).trans r.address,(k _ (by decide)).trans r.save,(k _ (by decide)).trans r.width,
   (k _ (by decide)).trans r.amount,(k _ (by decide)).trans r.selector,(k _ (by decide)).trans r.bytes,(k _ (by decide)).trans r.mode⟩

structure ScratchFields (s : MachineState) : Prop where
  second : readBuffer s (chainBuf+32) 32=0
  pad : readBuffer s (chainBuf+72) 24=0

private theorem cleared_read (s : MachineState) (a off n : Nat) (zero : ∀ j<n,wordAt s (a+off+8*j)=0)
    (al : (a+off)%8=0) : readBuffer s (a+off) (8*n)=0 := by
  unfold readBuffer
  rw [Finset.sum_eq_zero (fun j hj=>?_)];rfl
  have lt:=Finset.mem_range.mp hj
  have byte : Open.byteAt s (a+off+j)=0:=by
    rw [Open.byte_word,show 8*((a+off+j)/8)=a+off+8*(j/8) by omega,zero (j/8) (by omega)]
    change ((0#64 >>> _) : Word).truncate 8=0;rw [BitVec.zero_ushiftRight];rfl
  change (Open.byteAt s (a+off+j)).toNat*_=0;rw [byte];simp

theorem chain_zero (o : Oracle) (s : MachineState) (dst : Nat) (pc : s.pc=pcAt 181)
    (scratch : s.getReg .x26=W chainBuf) (source : s.getReg .x10=W rowBuf) :
    ∃ t,Flow o s t 11 0 ∧ t.pc=pcAt 192 ∧ (∀ q,t.getReg q=s.getReg q) ∧ ScratchFields t ∧ readBuffer t (rowBuf+72) 24=0 ∧
      readBuffer t rowBuf 32=readBuffer s rowBuf 32 ∧ readBuffer t (rowBuf+32) 32=readBuffer s (rowBuf+32) 32 ∧ ChainOutside s t dst := by
  obtain ⟨u,x⟩:=clear_offset o s 181 chainBuf 4 8 .x26 (by unfold OffsetSites;decide +kernel) (by decide) pc scratch (by decide) (by decide)
  obtain ⟨t,y⟩:=clear_offset o u 189 rowBuf 9 3 .x10 (by unfold OffsetSites;decide +kernel) (by decide) x.last ((x.regs _).trans source) (by decide) (by decide)
  have middle : readBuffer u (chainBuf+32) 32=0:=cleared_read u chainBuf 32 4 (fun j h=>x.zero j (by omega)) (by decide)
  have last : readBuffer u (chainBuf+72) 24=0:=cleared_read u chainBuf 72 3 (fun j h=>by
    have e:=x.zero (5+j) (by omega);convert e using 2 <;> omega) (by decide)
  have copy (a n : Nat) (room : a+n≤MEMORY_BYTES) (sep : a+n≤rowBuf+72 ∨ rowBuf+96≤a) :
      readBuffer t a n=readBuffer u a n:=Open.outside_read y.outside (by decide) (by decide) a n room sep
  have before (a n : Nat) (room : a+n≤MEMORY_BYTES) (sep : a+n≤chainBuf+32 ∨ chainBuf+96≤a) :
      readBuffer u a n=readBuffer s a n:=Open.outside_read x.outside (by decide) (by decide) a n room sep
  refine ⟨t,x.run.trans y.run,y.last,fun q=>(y.regs q).trans (x.regs q),
    ⟨(copy _ _ (by decide) (by decide)).trans middle,(copy _ _ (by decide) (by decide)).trans last⟩,
    cleared_read t rowBuf 72 3 y.zero (by decide),(copy _ _ (by decide) (by decide)).trans (before _ _ (by decide) (by decide)),
    (copy _ _ (by decide) (by decide)).trans (before _ _ (by decide) (by decide)),
    (ChainOutside.inside x.outside (by decide) (by decide)).trans (ChainOutside.inside y.outside (by decide) (by decide))⟩
end CommitGolfCandidate.Chained.BinaryMachine.Check
