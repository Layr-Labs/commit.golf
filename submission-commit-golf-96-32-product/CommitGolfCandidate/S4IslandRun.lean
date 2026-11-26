import CommitGolfCandidate.S4Transfer
import CommitGolfCandidate.S4Island
namespace CommitGolfCandidate.S4.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (pcAt pc_succ Digest)
set_option maxRecDepth 8192
attribute [local irreducible] Code.word Code.image Runs

private def atSite (s : MachineState) (n : Nat) := s.setPC (pcAt n)

private theorem addZero (s : MachineState) : s.setReg .x10 (s.getReg .x10+0)=s := by
  cases s
  simp only [BitVec.add_zero,MachineState.getReg,MachineState.setReg,MachineState.mk.injEq,and_true,true_and]
  funext r;by_cases e:r=Reg.x10 <;> simp [e]

private theorem nop (s : MachineState) (n : Nat) (bound : n<Code.check.count) (word : stands .check n (.ADDI .x10 .x10 0)) :
    Runs .check (atSite s n) (atSite s (n+1)) 1 1 := by
  apply one bound rfl _ (stood word)
  change some ((s.setReg .x10 (s.getReg .x10+0)).setPC (pcAt n+4))=_
  rw [addZero,←pc_succ];rfl

private theorem lhu (s : MachineState) (n : Nat) (z : BitVec 16) (ad : Word)
    (addr : s.getReg .x12+signExtend12 28=ad) (value : s.getHalfword ad=z) (valid : accessValid ad 2=true)
    (bound : n<Code.check.count) (op : stands .check n (.LHU .x10 .x12 28)) :
    Runs .check (atSite s n) (atSite (s.setReg .x10 (z.zeroExtend 64)) (n+1)) 1 1 := by
  have ok : memoryArgumentsValid (atSite s n) (.LHU .x10 .x12 28)=true:=by
    change accessValid (s.getReg .x12+signExtend12 28) 2=true;rw [addr,valid]
  apply one bound rfl _ (stood op)
  simp only [ordinaryStep,if_pos ok]
  change some ((s.setReg .x10 ((s.getHalfword (s.getReg .x12+signExtend12 28)).zeroExtend 64)).setPC (pcAt n+4))=_
  rw [addr,value,←pc_succ];rfl

private theorem left50 (s : MachineState) (n : Nat) (v : Word) (hi : n<Code.check.count)
    (code : stands .check n (.SLLI .x10 .x10 50)) :
    Runs .check (atSite (s.setReg .x10 v) n) (atSite (s.setReg .x10 (v <<< 50)) (n+1)) 1 1 := by
  apply one hi rfl _ (stood code)
  change some (((s.setReg .x10 v).setReg .x10 (v <<< 50)).setPC (pcAt n+4))=_
  rw [Trunc.overwrite10,←pc_succ];rfl
private theorem right50 (s : MachineState) (n : Nat) (v result : Word) (same : v >>> 50=result) (hi : n<Code.check.count)
    (code : stands .check n (.SRLI .x10 .x10 50)) :
    Runs .check (atSite (s.setReg .x10 v) n) (atSite (s.setReg .x10 result) (n+1)) 1 1 := by
  apply one hi rfl _ (stood code)
  change some (((s.setReg .x10 v).setReg .x10 (v >>> 50)).setPC (pcAt n+4))=_
  rw [Trunc.overwrite10,same,←pc_succ];rfl
private theorem sw (s : MachineState) (n : Nat) (v ad : Word) (t : MachineState) (addr : s.getReg .x12+signExtend12 28=ad)
    (ok : accessValid ad 4=true) (update : s.setWord32 ad (v.truncate 32)=t) (hi : n<Code.check.count)
    (code : stands .check n (.SW .x12 .x10 28)) :
    Runs .check (atSite (s.setReg .x10 v) n) (atSite (t.setReg .x10 v) (n+1)) 1 1 := by
  have good : memoryArgumentsValid (atSite (s.setReg .x10 v) n) (.SW .x12 .x10 28)=true:=by
    change accessValid (s.getReg .x12+signExtend12 28) 4=true;rw [addr,ok]
  apply one hi rfl _ (stood code)
  simp only [ordinaryStep,if_pos good]
  change some (((s.setWord32 (s.getReg .x12+signExtend12 28) (v.truncate 32)).setReg .x10 v).setPC (pcAt n+4))=_
  rw [addr,update,←pc_succ];rfl
private theorem sh (s t : MachineState) (n : Nat) (ad : Word) (addr : s.getReg .x12+signExtend12 30=ad)
    (ok : accessValid ad 2=true) (update : s.setHalfword ad 0=t) (hi : n<Code.check.count)
    (code : stands .check n (.SH .x12 .x0 30)) : Runs .check (atSite s n) (atSite t (n+1)) 1 1 := by
  have good : memoryArgumentsValid (atSite s n) (.SH .x12 .x0 30)=true:=by
    change accessValid (s.getReg .x12+signExtend12 30) 2=true;rw [addr,ok]
  apply one hi rfl _ (stood code)
  simp only [ordinaryStep,if_pos good]
  change some ((s.setHalfword (s.getReg .x12+signExtend12 30) 0).setPC (pcAt n+4))=_
  rw [addr,update,←pc_succ];rfl

set_option maxHeartbeats 1200000 in
private theorem blockRun (raw narrow wide : MachineState) (n a dst : Nat) (equal : n+8192=a) (w : Digest) (member : n∈maskPCs)
    (rptr : raw.getReg .x12=W dst) (dr : AddrOK dst 32) (pc : raw.pc=pcAt n)
    (read : raw.getHalfword (W (dst+28))=w.extractLsb' 224 16)
    (short : raw.setWord32 (W (dst+28)) ((Trunc.maskValue w).truncate 32)=narrow)
    (lo : raw.setHalfword (W (dst+30)) 0=wide) :
    Runs .check raw (atSite (if narrowAt n then narrow.setReg .x10 (Trunc.maskValue w) else wide) (n+1)) 6 6 := by
  obtain ⟨front,back,limit,ops⟩:=islandOf member
  rw [equal] at front ops
  have endWord : a+4=n+8196:=by omega
  rw [←endWord] at back limit
  have go : Runs .check raw (atSite raw a) 1 1:=jump .check n a raw pc front
  have fits : dst+32≤2^64:=dr.2.trans (by decide)
  by_cases isN : narrowAt n=true
  · let z:=w.extractLsb' 224 16
    let h:=z.zeroExtend 64
    let l:=h <<< 50
    let m:=Trunc.maskValue w
    let p:=W (dst+28)
    have load : raw.getHalfword p=z:=read
    have addr : raw.getReg .x12+signExtend12 28=p:=by rw [rptr];exact (BitVec.ofNat_add ..).symm
    have safe2 : accessValid p 2=true:=Safe.valid ⟨by have:=dr.2;omega,by have:=dr.1;omega⟩
    have safe4 : accessValid p 4=true:=Safe.valid ⟨by have:=dr.2;omega,by have:=dr.1;omega⟩
    let out:=narrow.setReg .x10 m
    have f1:=lhu raw a z p addr load safe2 (by omega) (by
      simpa only [isN,islandOp,ite_true,Fin.val_mk,Nat.add_zero] using ops ⟨0,by decide⟩)
    have f2:=left50 raw (a+1) h (by omega) (by
      simpa only [isN,islandOp,ite_true,Fin.val_mk] using ops ⟨1,by decide⟩)
    have f3:=right50 raw (a+2) l m (Trunc.loadShiftMask z) (by omega) (by
      simpa only [isN,islandOp,ite_true,Fin.val_mk] using ops ⟨2,by decide⟩)
    have f4:=sw raw (a+3) m p narrow addr safe4 short (by omega) (by
      simpa only [isN,islandOp,ite_true,Fin.val_mk] using ops ⟨3,by decide⟩)
    have ret : Runs .check (atSite out (a+4)) (atSite out (n+1)) 1 1 := jump .check (a+4) (n+1) (atSite out (a+4)) rfl back
    rw [if_pos isN];exact (((((go.trans f1).trans f2).trans f3).trans f4).trans ret)
  · have isWide:=Bool.eq_false_iff.mpr isN
    let out:=wide
    have addr : raw.getReg .x12+signExtend12 30=W (dst+30):=by rw [rptr];exact (BitVec.ofNat_add ..).symm
    have f1:=sh raw out a (W (dst+30)) addr (Safe.valid ⟨by have:=dr.2;omega,by have:=dr.1;omega⟩) lo
      (by omega) (by simpa only [isWide,islandOp,Bool.false_eq_true,ite_false,Fin.val_mk,Nat.add_zero] using ops ⟨0,by decide⟩)
    have f2:=nop out (a+1) (by omega) (by simpa only [isWide,islandOp,Bool.false_eq_true,ite_false] using ops ⟨1,by decide⟩)
    have f3:=nop out (a+2) (by omega) (by simpa only [isWide,islandOp,Bool.false_eq_true,ite_false] using ops ⟨2,by decide⟩)
    have f4:=nop out (a+3) (by omega) (by simpa only [isWide,islandOp,Bool.false_eq_true,ite_false] using ops ⟨3,by decide⟩)
    have ret : Runs .check (atSite out (a+4)) (atSite out (n+1)) 1 1 := jump .check (a+4) (n+1) (atSite out (a+4)) rfl back
    rw [if_neg isN];exact (((((go.trans f1).trans f2).trans f3).trans f4).trans ret)

theorem islandRun (s : MachineState) (n dst : Nat) (w : Digest) (member : n∈maskPCs)
    (ptr : s.getReg .x12=W dst) (dr : AddrOK dst 32) (pc : (Late.store s dst w).pc=pcAt n) :
    Runs .check (Late.store s dst w)
      (atSite (scratch n true w (Late.store s dst (trimAt n true w))) (n+1)) 6 6 := by
  have e:=blockRun (Late.store s dst w) (Late.store s dst (Trunc.pad238 w)) (Late.store s dst (Trunc.padLow w))
    n (n+8192) dst rfl w member ((writeBits_register ..).trans ptr) dr pc
    (Trunc.loaded238 s dst w dr.1 (dr.2.trans (by decide))) (Trunc.cleared238 s dst w dr.1 (dr.2.trans (by decide)))
    (Trunc.clearedReply s dst w dr.1 (dr.2.trans (by decide)))
  cases b : narrowAt n <;> simpa only [scratch,trimAt,b,Bool.true_and,ite_true,Bool.false_eq_true,ite_false] using e
end CommitGolfCandidate.S4.Machine
