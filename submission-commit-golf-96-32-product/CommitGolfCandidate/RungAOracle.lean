import CommitGolfCandidate.RungAStore
import CommitGolfCandidate.RungARaw
set_option Elab.async false
set_option maxHeartbeats 700000
namespace CommitGolfCandidate.RungA
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open S4.Machine (W Code Runs Safe)
open Late (pcAt nodeAddress rowAddress levelCount Digest)
private theorem writePC (s : MachineState) (a : Word) (w : Digest) : (writeBits s a w).pc=s.pc+4:=rfl
attribute [local irreducible] DetRun execute readBuffer writeBits rebuildDigest Code.image
private theorem hashInput {H td ps C s} (g h n : Nat) (hh:h<4) (hn:n<sizeAt h)
    (real:baseIndex g h+n<levelCount h) (v : View H td ps (frontier C g h n) s) :
    let j:=baseIndex g h+n
    inputAddr h j%8=0 ∧ inputAddr h j+96≤MEMORY_BYTES ∧ readBuffer s (inputAddr h j) 96=inputBlock H td h j := by
  cases h with
  | zero=>
    intro j
    have hj:j<16777216:=real
    exact ⟨by change (Late.rowBase+184*(j/2)+88*(j%2))%8=0;unfold Late.rowBase;omega,
      by change Late.rowBase+184*(j/2)+88*(j%2)+96≤68719476736;unfold Late.rowBase;omega,v.row j hj⟩
  | succ h=>
    intro j
    have up:=Late.row_after h j (by change h<24;omega) real
    have cap:=Late.padded_region (h+1)
    exact ⟨Late.rowAligned h j,by change rowAddress h j+96≤68719476736;unfold Late.rowBase at cap;omega,
      readParent g h n (by omega) hn real v⟩
private theorem rawCall (o : Oracle) (s : MachineState) (p a b : Nat) (w : Digest)
    (pc:s.pc=pcAt p) (small:p<Code.opening.count) (word:S4.Machine.stands .opening p .ECALL)
    (mode:s.getReg .x5=0) (width:s.getReg .x11=96) (kind:s.getReg .x13=0)
    (inp:s.getReg .x10=W b) (dst:s.getReg .x12=W a) (ba:b%8=0) (aa:a%8=0)
    (br:b+96≤MEMORY_BYTES) (ar:a+32≤MEMORY_BYTES) (ans:o.compression (readBuffer s b 96)=w) :
    DetRun o image s 1 (writeBits s (W a) w) 8 1 := by
  have f:=(S4.Machine.fetched .opening p small s pc).trans (S4.Machine.stood word)
  exact rawInstruction o image s b a f mode width kind inp dst ba aa br ar w ans

private theorem maskCall (o : Oracle) (u : MachineState) (p a : Nat)
    (pc:u.pc=pcAt p) (dst:u.getReg .x12=W a) (aligned:a%8=0) (room:a+32≤MEMORY_BYTES)
    (bound:p<Code.opening.count) (word:S4.Machine.stands .opening p (.SH .x12 .x0 30)) :
    let t:=execInstrBr u (.SH .x12 .x0 30)
    DetRun o image u 1 t 1 0 ∧ t.pc=pcAt (p+1) ∧ (∀ r,t.getReg r=u.getReg r) ∧
      t.mem=(u.setHalfword (W (a+30)) 0).mem := by
  intro t
  have ptr:u.getReg .x12+signExtend12 30=W (a+30):=by rw [dst];exact (BitVec.ofNat_add ..).symm
  have ok : memoryArgumentsValid u (.SH .x12 .x0 30)=true:=by
    change accessValid _ 2=true;rw [ptr];exact Safe.valid ⟨by omega,by omega⟩
  have f:=(S4.Machine.fetched .opening p bound u pc).trans (S4.Machine.stood word)
  refine ⟨DetRun.step1 f ?_,(congrArg (·+4) pc).trans (Late.pc_succ _).symm,fun r=>by cases r <;> rfl,?_⟩
  · change (if memoryArgumentsValid u _ then some t else none)=some t
    rw [ok];rfl
  · change (u.setHalfword (u.getReg .x12+signExtend12 30) 0).mem=_
    rw [ptr]

private theorem hashStore (o : Oracle) (s : MachineState) (p a h : Nat) (w : Digest)
    (pc:s.pc=pcAt p) (dst:s.getReg .x12=W a) (aligned:a%8=0) (room:a+32≤MEMORY_BYTES)
    (enc:hashSite p h) (raw:DetRun o image s 1 (writeBits s (W a) w) 8 1) :
    ∃ t,DetRun o image s (hashLength h) t (hashCycles h) 1 ∧ t.pc=pcAt (p+hashLength h) ∧
       (∀ r,t.getReg r=s.getReg r) ∧ Stored s t a (if masked h then Trunc.padLow w else w) := by
  let u:=writeBits s (W a) w
  have inc:u.pc=pcAt (p+1):=(writePC s (W a) w).trans ((congrArg (·+4) pc).trans (Late.pc_succ p).symm)
  have regs (r:Reg) : u.getReg r=s.getReg r:=writeBits_register s (W a) w r
  by_cases m:masked h=true
  · have next:p+1<Code.opening.count:=by have size:=enc.1;rw [hashLength,if_pos m] at size;omega
    obtain ⟨one,ip,keep,wm⟩:=maskCall o u (p+1) a inc ((regs _).trans dst) aligned room next (enc.2.2 m)
    have mem:=wm.trans (congrArg MachineState.mem (Trunc.clearedReply s a w aligned (room.trans (by decide))))
    simp only [hashLength,hashCycles,if_pos m]
    exact ⟨_,raw.trans one,ip,fun r=>(keep r).trans (regs r),(written s a (Trunc.padLow w) room).mem mem⟩
  · simp only [hashLength,hashCycles,if_neg m]
    exact ⟨u,raw,inc,regs,written s a w room⟩

theorem runHash {o : Oracle} {td ps C s} (g h n p : Nat) (hh:h<4) (hn:n<sizeAt h)
    (real:baseIndex g h+n<levelCount h) (v : View o.compression td ps (frontier C g h n) s)
    (pc:s.pc=pcAt p) (enc:hashSite p h)
    (mode:s.getReg .x5=0) (width:s.getReg .x11=96) (kind:s.getReg .x13=0)
    (inPtr:s.getReg .x10=W (inputAddr h (baseIndex g h+n))) (outPtr:s.getReg .x12=W (nodeAddress h (baseIndex g h+n))) :
    ∃ t,DetRun o image s (hashLength h) t (hashCycles h) 1 ∧ t.pc=pcAt (p+hashLength h) ∧
      (∀ r,t.getReg r=s.getReg r) ∧ View o.compression td ps (frontier C g h (n+1)) t := by
  let j:=baseIndex g h+n
  let a:=nodeAddress h j
  let b:=inputAddr h j
  let w:=o.compression (inputBlock o.compression td h j)
  have room:a+32≤MEMORY_BYTES:=(Late.parent_below_salts h j real).trans (by decide)
  have aligned:a%8=0:=Late.nodeAligned h j
  have input:=hashInput g h n hh hn real v
  have small:p<Code.opening.count:=by have size:=enc.1;unfold hashLength at size;split at size <;> omega
  have raw:=rawCall o s p a b w pc small enc.2.1 mode width kind inPtr outPtr input.1 aligned input.2.1 room (congrArg o.compression input.2.2)
  obtain ⟨t,run,ip,regs,store⟩:=hashStore o s p a h w pc outPtr aligned room enc raw
  have digest:=realDigest o.compression td h j hh real
  have cell : Stored s t a (rebuildDigest o.compression td h j):=Eq.mp (congrArg (Stored s t a) digest.symm) store
  exact ⟨t,run,ip,regs,(v.add hh real cell).equiv (frontierValidStep C g h n hh hn real)⟩
end CommitGolfCandidate.RungA
