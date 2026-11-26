import CommitGolfCandidate.S5CheckCursor
import CommitGolfCandidate.S5CheckRowSites
namespace CommitGolfCandidate.S5Machine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W Outside)
def peerKeep (q : Reg) := q∈rowRegs ∨ q=.x4 ∨ q=.x14
structure PeerRead (o : Oracle) (batch : Bool) (x : CheckInput) (s t : MachineState)
    (start stop dst bit off width steps : Nat) : Prop where
  run : Flow o s t steps 0
  pc : t.pc=pcAt stop
  cursor : WireCursor batch x t (bit+width) (off+32)
  data : readBuffer t dst 32=wireValue batch x bit off width
  mem : Outside s t dst 32
  keep : ∀ q,peerKeep q→t.getReg q=s.getReg q
private theorem preserve_packed (q : Reg) (h : peerKeep q) : Reader.fieldKeep q ∧ q≠.x11 ∧ q≠.x1 := by
  cases q <;> simp_all [peerKeep,rowRegs,Reader.readKeep,Reader.fieldKeep]
theorem peer_packed (o : Oracle) (x : CheckInput) (s : MachineState) (n dst bit off width : Nat) (pc : s.pc=pcAt n)
    (ptr : s.getReg .x10=W dst) (cur : WireCursor true x s bit off) (sm : width≤256) (enough : bit+width≤8*69397)
    (low : dst+32≤proofBase) (al : dst%8=0) (back : n+2<2336)
    (imm : signExtend12 (BitVec.ofNat 12 width)=W width)
    (sizeOp : matchesWord .check (n,.ADDI .x11 .x0 (BitVec.ofNat 12 width))) (call : JumpSite (n+1) 21 .x1) :
    ∃ t steps,steps≤438 ∧ PeerRead o true x s t n (n+2) dst bit off width steps := by
  obtain ⟨k,kmax,queue⟩:=cur
  let u:=(s.setReg .x11 (W width)).setPC (pcAt (n+1))
  let z:=(u.setReg .x1 (pcAt (n+2))).setPC (pcAt 21)
  have set:=imm_step o s n .x11 .x0 _ (W width) pc (known sizeOp) ((BitVec.zero_add _).trans imm)
  have jump_:=jump o u (n+1) 21 .x1 call rfl
  have keep (q : Reg) (ne : q≠.x11) (ra : q≠.x1) : z.getReg q=s.getReg q:=
    MachineState.getReg_setPC.trans ((MachineState.getReg_setReg_ne _ _ _ _ ra.symm).trans
      (MachineState.getReg_setPC.trans (MachineState.getReg_setReg_ne _ _ _ _ ne.symm)))
  have cz:=queue.same (show z.mem=s.mem from rfl) (keep _ (by decide) (by decide)) (keep _ (by decide) (by decide))
    (keep _ (by decide) (by decide)) (keep _ (by decide) (by decide))
  obtain ⟨t,a,rem,atMost,small,run,ep,c,data,frame,same⟩:=Reader.read_field o z proofBase 69397 (S5.packedInput x) bit k width dst (n+2)
    sm (by decide) enough low al kmax rfl rfl back rfl ((keep _ (by decide) (by decide)).trans ptr) cz
  refine ⟨t,2+a,by omega,⟨(set.trans jump_).trans run,ep,⟨rem,small,c⟩,data,frame,?_⟩⟩
  intro q h;obtain ⟨safe,q11,q1⟩:=preserve_packed q h;exact (same q safe).trans (keep q q11 q1)

theorem peer_normal (o : Oracle) (x : CheckInput) (s : MachineState) (n dst bit off width : Nat)
    (pc : s.pc=pcAt n) (ptr : s.getReg .x6=W dst) (cur : WireCursor false x s bit off) (data : HighInput x s)
    (low : dst+32≤proofBase) (al : dst%8=0) (bounds : proofBase+off+32≤MEMORY_BYTES) (offAlign : off%8=0)
    (code : CopySites normalCopy n 4) (step : matchesWord .check (n+8,.ADDI .x19 .x19 32)) :
    ∃ t,PeerRead o false x s t n (n+9) dst bit off width 9 := by
  let src:=proofBase+off
  have rp : s.getReg .x19=W src:=cur
  have sa : src%8=0:=by dsimp [src,proofBase];omega
  obtain ⟨u,moved⟩:=copy_words o s n src dst 4 normalCopy code (by decide) (by decide) pc rp ptr ⟨sa,bounds⟩
    ⟨al,low.trans (by decide)⟩ (Or.inr (by change dst+32≤src;dsimp [src];omega))
  have initialValue:=data.read src 32 (by dsimp [src,proofBase,rootBase];omega) bounds
  let t:=(u.setReg .x19 (W (proofBase+(off+32)))).setPC (pcAt (n+9))
  have advance:=imm_step o u (n+8) .x19 .x19 32 (W (proofBase+(off+32))) moved.pc (known step)
    ((congrArg (·+signExtend12 32) ((moved.keep .x19 (by decide)).trans rp)).trans
       ((BitVec.ofNat_add src 32).symm.trans (congrArg W (by dsimp [src];omega))))
  have value : readBuffer t dst 32=readBuffer (initial x) src 32:=
    (read_buffer_memory_congr t u rfl _ _).trans ((copied_read (a:=src) (b:=dst) (n:=4) moved.data sa al).trans initialValue)
  refine ⟨t,⟨moved.run.trans advance,rfl,rfl,value,fun q h a sep=>moved.data.outside q h a sep,?_⟩⟩
  intro q h;apply MachineState.getReg_setPC.trans;apply Eq.trans (MachineState.getReg_setReg_ne _ _ _ _ ?_) (moved.keep q ?_)
  all_goals cases q <;> simp_all [peerKeep,rowRegs,normalCopy]
end CommitGolfCandidate.S5Machine.Check
