import CommitGolfCandidate.S5CheckSaltValue
namespace CommitGolfCandidate.S5Machine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W Outside)
attribute [local irreducible] S5.packedInput S5.atProof S5.complete Reader.window readBuffer
theorem load_salt (o : Oracle) (x : CheckInput) (s : MachineState) (r : Nat) (b : Bool) (hr : r<x.positions.card)
    (mode : b=decide (x.positions.card=BATCH)) (pc : s.pc=pcAt (recordBegin b+3)) (ptr : s.getReg (peerTarget b)=W saltBuf)
    (c : WireCursor b x s (4030*r) (824*r)) (high : HighInput x s) : ∃ t steps,steps≤saltCost b ∧ SaltGot o x s t b r steps := by
  cases b
  · let a:=proofBase+824*r
    have cap : x.positions.card≤LENGTH:=by simpa using Finset.card_le_univ x.positions
    change x.positions.card≤16777216 at cap
    have room : a+24≤MEMORY_BYTES:=by dsimp [a,proofBase,MEMORY_BYTES];omega
    have al : a%8=0:=by dsimp [a,proofBase];omega
    have sp : s.getReg .x19=W a:=c
    obtain ⟨u,copy⟩:=copy_words o s 1285 a saltBuf 3 normalCopy (by unfold CopySites;decide +kernel) (by decide) (by decide) pc sp ptr ⟨al,room⟩
      ⟨by decide,by decide⟩ (Or.inr (by change saltBuf+24≤a;dsimp [a,saltBuf,proofBase];omega))
    let t:=(u.setReg .x19 (W (a+24))).setPC (pcAt 1292)
    have update:=imm_step o u 1291 .x19 .x19 24 (W (a+24)) copy.pc (known (by decide +kernel))
      ((congrArg (·+signExtend12 24) ((copy.keep _ (by decide)).trans sp)).trans (BitVec.ofNat_add ..).symm)
    have value : readBuffer t saltBuf 24=readBuffer (initial x) a 24:=(read_buffer_memory_congr t u rfl _ _).trans
      ((copied_read (a:=a) (b:=saltBuf) (n:=3) copy.data al (by decide)).trans (high.read a 24 (by dsimp [a,rootBase,proofBase];omega) room))
    have payload : readBuffer t saltBuf 24=(view false x).salt r:=by
      simp only [view,Bool.false_eq_true,ite_false,S5.plainView,S5.atProof];exact value
    refine ⟨t,7,le_rfl,⟨copy.run.trans update,rfl,payload,fun q h aq sep=>copy.data.outside q h aq (by change q<saltBuf ∨ saltBuf+24≤q;omega),?_,?_⟩⟩
    · change W (a+24)=W (proofBase+peerOffset r 0);apply congrArg W;dsimp [a,peerOffset];omega
    · intro q hv
      apply MachineState.getReg_setPC.trans;apply Eq.trans (MachineState.getReg_setReg_ne _ _ _ _ ?_) (copy.keep q ?_)
      all_goals cases q <;> simp_all [peerKeep,rowRegs,normalCopy]
  · have size : x.positions.card=128:=of_decide_eq_true mode.symm
    obtain ⟨u,a,lim,get⟩:=peer_packed o x s 236 saltBuf (4030*r) (824*r) 192 pc ptr c (by decide) (by omega) (by decide) (by decide) (by decide) rfl
      (by decide +kernel) (by decide +kernel)
    have raw:=read_buffer_slice u saltBuf 32 0 24 (by decide)
    rw [get.data] at raw
    have c' : WireCursor true x u (peerBit r 0) (peerOffset r 0):=by
      exact get.cursor
    exact ⟨u,a,lim,⟨get.run,get.pc,raw.symm.trans (salt_window x r),get.mem,c',get.keep⟩⟩
end CommitGolfCandidate.S5Machine.Check
