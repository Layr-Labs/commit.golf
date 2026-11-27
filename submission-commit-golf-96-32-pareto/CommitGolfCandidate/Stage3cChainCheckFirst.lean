import CommitGolfCandidate.Stage3cChainCheckEntry
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Chained
open Open (W Outside)
def tagOps : List Sym.Calc := [.addi .x6 .x0 1,.slli .x6 .x6 63,.slli .x7 .x29 8,.bor .x7 .x6 .x7]
def startRoundOps : List Sym.Calc := [.addi .x6 .x0 1,.addi .x10 .x26 0]
def chainReply (H : Compression) (h : Height) (l r : Output) (j : Nat) := H (stageInput H h l r j)
structure InRound (H : Compression) (h : Height) (dst : Nat) (l r : Output) (j : Nat) (s : MachineState) : Prop where
  pc : s.pc=pcAt 201
  sys : ChainSys h dst s
  tag : s.getReg .x7=tagWord h 0
  counter : s.getReg .x6=W (j+1)
  source : s.getReg .x10=W chainBuf
  value : readBuffer s chainBuf 32=chainReply H h l r j
  scratch : ScratchFields s

private theorem tag_reg (s : MachineState) (h : Height) (layer : s.getReg .x29=W (h.val+1)) :
    ((tagOps.foldl Sym.bump Sym.original) .x7).eval s=tagWord h 0 := by
  change ((1#64 <<< 63) ||| (s.getReg .x29 <<< 8))=_
  rw [layer];unfold tagWord;rw [show BitVec.ofNat 64 (0 : Fin 16).val=0#64 by rfl,BitVec.add_zero];rfl

private theorem common (q : Reg) (h : q∈sysRegs ∨ parentLive q) :
    q≠.x6 ∧ q≠.x7 ∧ q≠.x10 ∧ q≠.x12 := by cases q <;> simp_all [sysRegs,parentLive]

structure FirstResult (o : Oracle) (s t : MachineState) (h : Height) (dst : Nat) : Prop where
  run : Flow o s t 26 1
  ready : InRound o.compression h dst (readBuffer s rowBuf 32) (readBuffer s (rowBuf+32) 32) 0 t
  keep : ParentPreserves s t
  frame : ChainOutside s t dst
theorem tag_regs (s : MachineState) (a : Nat) (w ip : Word) (q : Reg) : ((tagStore s a w).setPC ip).getReg q=s.getReg q:=by cases q <;> rfl
attribute [local irreducible] readBuffer stageInput Sym.evaluated
set_option maxRecDepth 12000 in
set_option maxHeartbeats 700000 in
theorem first_query (o : Oracle) (orig s : MachineState) (h : Height) (dst : Nat) (entry : ChainEntry o orig s h dst) (cut : 8≤h.val ∧ h.val<16) :
    ∃ t,FirstResult o orig t h dst := by
  let u:=Sym.evaluated tagOps s
  obtain ⟨mathRun,regs,um,up⟩:=Sym.compiled o tagOps 192 s entry.pc (by decide +kernel)
    (by change ∀ e∈([] : List (Sym.Expr×Nat)),_;simp)
  have uk (q : Reg) (a : q≠.x6) (b : q≠.x7) : u.getReg q=s.getReg q:=by
    apply (regs q).trans;cases q <;> first | rfl | contradiction
  let tag:=tagWord h 0
  have ut : u.getReg .x7=tag:=(regs _).trans (tag_reg s h entry.level)
  let z:=(tagStore u rowBuf tag).setPC (pcAt 197)
  have sz : u.getReg .x10=W rowBuf:=(uk _ (by decide) (by decide)).trans entry.source
  have mark:=store_step o u 196 .x10 .x7 64 (rowBuf+64) tag up (known (by decide +kernel))
    ((congrArg (·+signExtend12 64) sz).trans (BitVec.ofNat_add rowBuf 64).symm) ut (by decide) (by decide)
  have zk (q : Reg) : z.getReg q=u.getReg q:=tag_regs u _ tag _ q
  let p:=(z.setReg .x12 (W chainBuf)).setPC (pcAt 198)
  have zsrc:=(zk .x26).trans ((uk _ (by decide) (by decide)).trans entry.sys.address)
  have setup:=imm_step o z 197 .x12 .x26 0 (W chainBuf) rfl (known (by decide +kernel)) ((BitVec.add_zero _).trans zsrc)
  have pk (q : Reg) (ne : q≠.x12) : p.getReg q=z.getReg q:=MachineState.getReg_setPC.trans (MachineState.getReg_setReg_ne _ _ _ _ ne.symm)
  have hold (q : Reg) (a : q≠.x6) (b : q≠.x7) (d : q≠.x12) : p.getReg q=s.getReg q:=(pk _ d).trans ((zk _).trans (uk q a b))
  let l:=readBuffer orig rowBuf 32
  let r:=readBuffer orig (rowBuf+32) 32
  have left : readBuffer u rowBuf 32=l:=(read_buffer_memory_congr u s um _ _).trans entry.left
  have right : readBuffer u (rowBuf+32) 32=r:=(read_buffer_memory_congr u s um _ _).trans entry.right
  have gap : readBuffer u (rowBuf+72) 24=0:=(read_buffer_memory_congr u s um _ _).trans entry.pad
  have data : readBuffer p rowBuf 96=stageInput o.compression h l r 0 :=by
    unfold stageInput
    exact (read_buffer_memory_congr p (tagStore u rowBuf tag) rfl _ _).trans ((tagged_input u rowBuf l r tag (by decide) (by decide) left right gap).trans (parentBlock_first h l r cut))
  let v:=writeBits p (W chainBuf) (chainReply o.compression h l r 0)
  have query:=reply_flow o (s:=p) (pc:=198) rfl (known (by decide +kernel)) ((hold _ (by decide) (by decide) (by decide)).trans entry.sys.selector)
    ((hold _ (by decide) (by decide) (by decide)).trans entry.sys.bytes) ((hold _ (by decide) (by decide) (by decide)).trans entry.sys.mode)
    ((pk _ (by decide)).trans ((zk _).trans sz)) (show p.getReg .x12=W chainBuf from rfl) (by decide) (by decide) (by decide) (by decide)
  rw [data] at query
  have vk (q : Reg) : v.getReg q=p.getReg q:=writeBits_register ..
  let t:=Sym.evaluated startRoundOps v
  obtain ⟨advance,tk,tm,tp⟩:=Sym.compiled o startRoundOps 199 v (by rfl) (by decide +kernel)
    (by change ∀ e∈([] : List (Sym.Expr×Nat)),_;simp)
  have stable (q : Reg) (a : q≠.x6) (b : q≠.x10) : t.getReg q=v.getReg q:=by
    apply (tk q).trans;cases q <;> first | rfl | contradiction
  have frame (q : Reg) (qok : q∈sysRegs ∨ parentLive q) : t.getReg q=s.getReg q:=by
    obtain ⟨a,b,c,d⟩:=common q qok;exact (stable q a c).trans ((vk q).trans (hold q a b d))
  have vs : v.getReg .x26=W chainBuf:=(vk _).trans ((pk _ (by decide)).trans zsrc)
  have tagFrame : Outside s p (rowBuf+64) 8:=by
    intro q aq al sep;exact (store_far u (rowBuf+64) tag (by decide) q aq al sep).trans (congrFun um _)
  have hashFrame : Outside p t chainBuf 32:=by
    intro q aq al sep;exact (congrFun tm _).trans (reply_outside p chainBuf _ (by decide) (by decide) q aq al sep)
  have beyond (a n : Nat) (block : a+n≤MEMORY_BYTES) (sa : rowBuf+72≤a) (sb : chainBuf+32≤a) : readBuffer t a n=readBuffer s a n :=
    (Open.outside_read hashFrame (by decide) (by decide) _ _ block (Or.inr sb)).trans (Open.outside_read tagFrame (by decide) (by decide) _ _ block (Or.inr sa))
  have all:=((((entry.run.trans mathRun).trans mark).trans setup).trans query).trans advance
  refine ⟨t,⟨all,⟨tp,entry.sys.kept (fun q g=>frame q (Or.inl g)),?_,tk .x6,?_,?_,?_⟩,
    entry.keep.trans (fun q h=>frame q (Or.inr h)),entry.frame.trans ((ChainOutside.inside tagFrame (by decide) (by decide)).trans (ChainOutside.inside hashFrame (by decide) (by decide)))⟩⟩
  · exact (stable _ (by decide) (by decide)).trans ((vk _).trans ((pk _ (by decide)).trans ((zk _).trans ut)))
  · apply (tk .x10).trans;change v.getReg .x26+0#64=_;rw [vs,BitVec.add_zero]
  · exact (read_buffer_memory_congr t v tm _ _).trans (store_read p chainBuf _)
  · exact ⟨(beyond _ _ (by decide) (by decide) (by decide)).trans entry.scratch.second,
    (beyond _ _ (by decide) (by decide) (by decide)).trans entry.scratch.pad⟩
end CommitGolfCandidate.Chained.BinaryMachine.Check
