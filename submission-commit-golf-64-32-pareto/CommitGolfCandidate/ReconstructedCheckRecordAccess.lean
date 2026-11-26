import CommitGolfCandidate.ReconstructedCheckRecordSpec
import CommitGolfCandidate.ReconstructedCheckRecordOps
import CommitGolfCandidate.ReconstructedOpeningCursor

namespace CommitGolfCandidate.Reconstruction.CheckRecordAccess
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CheckLayout CheckRecorded LeafModel OpeningOps
open TwoPermutationPrototype TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
set_option maxRecDepth 16000
set_option maxHeartbeats 1400000
abbrev W:=BitVec.ofNat 64

def flag (k : Nat) := W (4259840+k)
def capWord (k j : Nat) := 524288+4*k+j
def keep : List Reg := [.x2,.x8,.x10,.x11,.x12,.x13,.x14,.x19,.x24]
def addrOps : List Op := [.reg .x15 (.lui 1040),.reg .x15 (.add .x23 .x15)]
def setup : List Op := [.reg .x23 (.slli .x23 5),.reg .x17 (.lui 1),.reg .x17 (.sub .x8 .x17),.ld .x5 .x17 1680 ((CheckLayout.fp-2416)/8),
  .reg .x6 (.addi .x8 2048),.reg .x6 (.addi .x6 3816),.reg .x7 (.addi .x8 2048),.reg .x7 (.addi .x7 4072)]

def Mem (s t : MachineState) := ∀ w,w<2^33→t.getMem (wordAddress w)=s.getMem (wordAddress w)

theorem bytes {s t : MachineState} (h : Mem s t) (a : Nat) (small : a<2^36) : t.getByte (W a)=s.getByte (W a) := by
  change extractByte (t.getMem (alignToDword (W a))) _=extractByte (s.getMem (alignToDword (W a))) _
  rw [OpeningCursor.aligned];exact congrArg (fun x=>extractByte x _) (h (a/8) (by omega))

theorem validFlag (k : Nat) (small : k<1024) : accessValid (flag k) 1=true := by
  simp only [accessValid,rangeValid,flag,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : 4259840+k<2^64),Bool.and_eq_true,decide_eq_true_eq,Nat.mod_one]
  exact ⟨by unfold MEMORY_BYTES;omega,True.intro⟩

theorem scale (k : Nat) : W k <<< (5 : Nat) = W (32*k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft,BitVec.toNat_ofNat,BitVec.toNat_ofNat,Nat.shiftLeft_eq,show 2^5=32 by decide,Nat.mul_comm 32 k]
  exact Nat.mod_mul_mod k 32 _

structure After (s t : MachineState) (k : Nat) : Prop where
  pc : t.pc=(if s.getByte (flag k)=0 then CommitBlocks.addr 109 else CommitBlocks.addr 398)
  flagAddr : t.getReg .x15=flag k
  shifted : t.getReg .x23=W (32*k)
  count : t.getReg .x5=s.getMem (W (CheckLayout.fp-2416))
  beginCopy : t.getReg .x6=W (CheckLayout.fp-2328)
  endCopy : t.getReg .x7=W (CheckLayout.fp-2072)
  preserved : ∀ r∈keep,t.getReg r=s.getReg r
  memory : Mem s t

def firstKeep (r : Reg):=r ≠ .x15 ∧ r ≠ .x16
deriving instance Decidable for firstKeep

private theorem before (o : Oracle) (s : MachineState) (k : Nat) (small : k<1024) (pc : s.pc=CommitBlocks.addr 386)
    (route : s.getReg .x23=W k) :
    ∃ v,Segment o 3 s v [] ∧ v.pc=CommitBlocks.addr 389 ∧ v.getReg .x15=flag k ∧
      v.getReg .x16=(s.getByte (flag k)).zeroExtend 64 ∧ (∀ r,firstKeep r→v.getReg r=s.getReg r) ∧ Mem s v := by
  let m:=CheckRecordHeader.model s
  have aok : Checked m addrOps:=by simp [addrOps,Checked,Op.Valid]
  obtain ⟨u,a,loc,fit⟩:=CheckStraight.block o m addrOps 386 (by decide) (CheckRecordOps.image _ _ (by decide)) aok s pc (CheckRecordHeader.fits s)
  have fa : u.getReg .x15=flag k:=by
    rw [fit.registers];change s.getReg .x23+4259840#64=_;rw [route,BitVec.add_comm];exact (BitVec.ofNat_add (n:=64) 4259840 k).symm
  let v:=(u.setReg .x16 ((u.getByte (flag k)).zeroExtend 64)).setPC (CommitBlocks.addr 389)
  have one:=CheckMemoryOps.loadB o u 388 .x16 .x15 (flag k) (by decide) loc fa (validFlag k small)
  refine ⟨v,by simpa only [List.nil_append,show addrOps.length=2 by decide] using compose a one,rfl,fa,?_,?_,fit.memory⟩
  · change (u.getByte (flag k)).zeroExtend 64=(s.getByte (flag k)).zeroExtend 64;exact congrArg (BitVec.zeroExtend 64) (bytes fit.memory (4259840+k) (by omega))
  · intro r h
    have mid : v.getReg r=u.getReg r:=by
      change ((u.setReg .x16 _).setPC _).getReg r=_
      rw [MachineState.getReg_setPC,TwoPermutationPrototype.Opening.getReg_setReg];simp [Ne.symm h.2,h.2]
    exact mid.trans (CheckRecordOps.physical addrOps fit (CheckRecordHeader.fits s) r (by simpa [addrOps,CheckRecordOps.dest] using h.1))

private theorem loaded (o : Oracle) (v : MachineState) (k : Nat) (pc : v.pc=CommitBlocks.addr 389)
    (vf : v.getReg .x8=W CheckLayout.fp) (vr : v.getReg .x23=W k) :
    ∃ z,Segment o 8 v z [] ∧ z.pc=CommitBlocks.addr 397 ∧ z.getReg .x23=W (32*k) ∧
      z.getReg .x5=v.getMem (W (CheckLayout.fp-2416)) ∧ z.getReg .x6=W (CheckLayout.fp-2328) ∧ z.getReg .x7=W (CheckLayout.fp-2072) ∧
      (∀ r,r∉setup.flatMap CheckRecordOps.dest→z.getReg r=v.getReg r) ∧ Mem v z := by
  have vo : Checked (CheckRecordHeader.model v) setup:=by
    simp only [setup,Checked,Op.Valid,Op.apply,true_and,and_true]
    refine ⟨by decide,?_⟩
    change v.getReg .x8-4096#64+1680#64=_;rw [vf];decide
  obtain ⟨z,c,pos,fz⟩:=CheckStraight.block o (CheckRecordHeader.model v) setup 389 (by decide) (CheckRecordOps.image _ _ (by decide)) vo v pc (CheckRecordHeader.fits v)
  refine ⟨z,c,pos,?_,?_,?_,?_,CheckRecordOps.physical setup fz (CheckRecordHeader.fits v),fz.memory⟩
  · rw [fz.registers];change v.getReg .x23 <<< (5 : Nat)=_;rw [vr,scale]
  · rw [fz.registers];rfl
  · rw [fz.registers];change v.getReg .x8+signExtend12 2048+signExtend12 3816=_;rw [vf];decide
  · rw [fz.registers];change v.getReg .x8+signExtend12 2048+signExtend12 4072=_;rw [vf];decide

private theorem zeroByte (x : BitVec 8) : x.zeroExtend 64=0#64 ↔ x=0#8 := by
  constructor
  · intro h;apply BitVec.eq_of_toNat_eq;have v:=congrArg BitVec.toNat h;have b:=x.isLt
    rw [BitVec.toNat_setWidth_of_le (show 8≤64 by decide)] at v;exact v
  · intro h;rw [h];rfl

theorem positive (o : Oracle) (s : MachineState) (k : Nat) (small : k<1024) (pc : s.pc=CommitBlocks.addr 386)
    (route : s.getReg .x23=W k) (fp : s.getReg .x8=W CheckLayout.fp) : ∃ t,Segment o 12 s t [] ∧ After s t k := by
  obtain ⟨v,pre,vpc,fa,flagValue,regs,mem⟩:=before o s k small pc route
  obtain ⟨z,middle,zpc,shift,count,copy1,copy2,regsZ,memZ⟩:=loaded o v k vpc ((regs .x8 (by decide)).trans fp) ((regs .x23 (by decide)).trans route)
  let next:=if CheckOrdinary.Cond.test .eq (z.getReg .x16) (z.getReg .x0) then CommitBlocks.addr 109 else CommitBlocks.addr 398
  have jump:=CheckBranch.event o z 397 109 .eq .x16 .x0 7040 (by decide) zpc (CheckDecode.same_sound (by decide)) (by decide)
  refine ⟨z.setPC next,by simpa only [List.nil_append] using compose (compose pre middle) jump,?_,(regsZ .x15 (by decide)).trans fa,shift,?_,copy1,copy2,?_,?_⟩
  · change (if (z.getReg .x16 == 0#64)=true then _ else _)=_
    rw [regsZ _ (by decide),flagValue];simp only [beq_iff_eq,zeroByte];rfl
  · apply count.trans;rw [show W (CheckLayout.fp-2416)=wordAddress 8589934164 by decide];exact mem _ (by decide)
  · intro r hr;have free : ∀ q : Reg,q∈keep→q∉setup.flatMap CheckRecordOps.dest ∧ firstKeep q:=by decide
    exact (regsZ r (free r hr).1).trans (regs r (free r hr).2)
  · intro w h;exact (memZ w h).trans (mem w h)

end CommitGolfCandidate.Reconstruction.CheckRecordAccess
