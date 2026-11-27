import CommitGolfCandidate.Stage3cChainCheckArm
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Chained
open Open (W Outside)
def roundSteps (h : Height) (j : Nat) :=armSteps h j+3
def continued (h : Height) (j : Nat) := if j+2<calls h then 201 else 210
def roundKeep (q : Reg) := q≠.x6 ∧ q≠.x12 ∧ q≠.x29
structure RoundResult (o : Oracle) (h : Height) (l r : Output) (dst j : Nat) (s t : MachineState) : Prop where
  run : Flow o s t (roundSteps h j) 1
  pc : t.pc=pcAt (continued h j)
  source : t.getReg .x10=W chainBuf
  sys : ChainSys h dst t
  tag : t.getReg .x7=tagWord h 0
  counter : t.getReg .x6=W (j+2)
  value : readBuffer t (armDest h dst j) 32=chainReply o.compression h l r (j+1)
  mem : let k : Fin 16:=⟨(j+1)%16,by omega⟩
        t.mem=(writeBits (tagStore s chainBuf (tagWord h k)) (W (armDest h dst j)) (chainReply o.compression h l r (j+1))).mem
  prior : ∀ a n,a+n≤MEMORY_BYTES → (a+n≤chainBuf+64 ∨ chainBuf+72≤a) →
    (a+n≤armDest h dst j ∨ armDest h dst j+32≤a) → readBuffer t a n=readBuffer s a n
  keep : ∀ q,roundKeep q→t.getReg q=s.getReg q
  frame : ChainOutside s t dst

private theorem arm_range {h dst j} (dstSpace : dst+32≤MEMORY_BYTES) (dstAlign : dst%8=0) :
    armDest h dst j+32≤MEMORY_BYTES ∧ armDest h dst j%8=0 := by unfold armDest;split <;> first | exact ⟨dstSpace,dstAlign⟩ | decide
private theorem common (q : Reg) (h : q∈sysRegs ∨ parentLive q) : roundKeep q:=by cases q <;> simp_all [sysRegs,parentLive,roundKeep]

private theorem close_round (o : Oracle) (s : MachineState) (h : Height) (j : Nat) (pc : s.pc=pcAt 208)
    (count : s.getReg .x30=W (calls h)) (r : s.getReg .x6=W (j+1)) (small : j+2≤calls h) (bound : calls h≤16) :
    ∃ t,Flow o s t 2 0 ∧ t.pc=pcAt (continued h j) ∧ t.getReg .x6=W (j+2) ∧ t.mem=s.mem ∧ ∀ q,q≠.x6→t.getReg q=s.getReg q := by
  let u:=(s.setReg .x6 (W (j+2))).setPC (pcAt 209)
  have inc:=imm_step o s 208 .x6 .x6 1 (W (j+2)) pc (known (by decide +kernel)) ((congrArg (·+signExtend12 1) r).trans (BitVec.ofNat_add (j+1) 1).symm)
  have flag : Rel.lt.test (u.getReg .x6) (u.getReg .x30)=decide (j+2<calls h) := by
    change BitVec.ult (W (j+2)) (s.getReg .x30)=_;rw [count];simp only [BitVec.ult,W,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : j+2<2^64),Nat.mod_eq_of_lt (by omega : calls h<2^64)]
  have back:=branch o u 209 201 .lt .x6 .x30 (by decide +kernel) rfl _ flag
  have eq : (if decide (j+2<calls h) then 201 else 209+1)=continued h j:=by simp [continued]
  rw [eq] at back
  exact ⟨_,inc.trans back,rfl,rfl,rfl,fun q neq=>MachineState.getReg_setPC.trans (MachineState.getReg_setPC.trans
    (MachineState.getReg_setReg_ne _ _ _ _ neq.symm))⟩

private theorem result_pc (s : MachineState) (a : Word) (v : Output) : (writeBits s a v).pc=s.pc+4:=rfl
private theorem stored_read (s : MachineState) (a : Nat) (v : Output) : readBuffer (writeBits s (W a) v) a 32=v:=store_read s a v
attribute [local irreducible] readBuffer writeBits
private theorem respond (o : Oracle) (h : Height) (dst j : Nat) (u : MachineState) (d : Nat) (arg : Input)
    (pc : u.pc=pcAt 207) (sys : ChainSys h dst u) (source : u.getReg .x10=W chainBuf) (dest : u.getReg .x12=W d)
    (read : readBuffer u chainBuf 96=arg) (cnt : u.getReg .x6=W (j+1)) (small : j+2≤calls h) (bound : calls h≤16)
    (space : d+32≤MEMORY_BYTES) (al : d%8=0) :
    ∃ t,Flow o u t 3 1 ∧ t.pc=pcAt (continued h j) ∧ t.getReg .x6=W (j+2) ∧
      t.mem=(writeBits u (W d) (o.compression arg)).mem ∧ ∀ q,q≠.x6→t.getReg q=u.getReg q := by
  let v:=writeBits u (W d) (o.compression arg)
  have raw:=reply_flow o pc (known (by decide +kernel)) sys.selector sys.bytes sys.mode source dest (by decide) (by decide) space al
  rw [read] at raw
  have pv : v.pc=pcAt 208:=(result_pc u _ _).trans ((congrArg (·+4) pc).trans (pc_succ 207))
  obtain ⟨t,tail,ip,inc,mem,keep⟩:=close_round o v h j pv ((writeBits_register ..).trans sys.amount) ((writeBits_register ..).trans cnt) small bound
  exact ⟨t,raw.trans tail,ip,inc,mem,fun q ne=>(keep q ne).trans (writeBits_register ..)⟩

set_option maxRecDepth 16000 in
set_option maxHeartbeats 800000 in
theorem round_query (o : Oracle) (h : Height) (l r : Output) (dst j : Nat) (s : MachineState) (old : InRound o.compression h dst l r j s)
    (small : j+2≤calls h) (bound : calls h≤16) (cut : 8≤h.val ∧ h.val<16) (da : dst%8=0) (ds : dst+32≤MEMORY_BYTES) :
    ∃ t,RoundResult o h l r dst j s t := by
  obtain ⟨u,a⟩:=arm_query o s h l r dst j old small bound cut
  let d:=armDest h dst j
  let val:=chainReply o.compression h l r (j+1)
  have bounds:=arm_range (h:=h) (j:=j) ds da
  have sysU:=old.sys.kept (fun q hq=>a.keep q (common q (Or.inl hq)).2.1 (common q (Or.inl hq)).2.2)
  obtain ⟨t,back,ep,inc,mem,keep⟩:=respond o h dst j u d _ a.pc sysU ((a.keep _ (by decide) (by decide)).trans old.source)
    a.dest a.input ((a.keep _ (by decide) (by decide)).trans old.counter) small bound bounds.1 bounds.2
  have raw : t.mem=(writeBits u (W d) val).mem:=by dsimp only [val,chainReply];exact mem
  have stable (q : Reg) (hq : roundKeep q) : t.getReg q=s.getReg q:=(keep q hq.1).trans (a.keep q hq.2.1 hq.2.2)
  let k : Fin 16:=⟨(j+1)%16,by omega⟩
  have tagMem : u.mem=(tagStore s chainBuf (tagWord h k)).mem:=a.mem
  have atEnd : t.mem=(writeBits (tagStore s chainBuf (tagWord h k)) (W d) val).mem:=
    raw.trans (write_bits_memory_congr u _ _ val tagMem)
  have tagging : Outside s u (chainBuf+64) 8:=fun q sm al out=>(congrFun tagMem _).trans (store_far s _ _ (by decide) q sm al out)
  have written : Outside u t d 32:=fun q sm al out=>(congrFun raw _).trans (reply_outside u d val bounds.1 bounds.2 q sm al out)
  have change1 : ChainOutside s u dst:=ChainOutside.inside tagging (by decide) (by decide)
  have change2 : ChainOutside u t dst:=by
    by_cases last : j+2=calls h
    · exact ChainOutside.output (by simpa only [d,armDest,if_pos last] using written)
    · apply ChainOutside.inside written <;> rw [show d=chainBuf from if_neg last] <;> decide
  refine ⟨t,⟨a.run.trans back,ep,(stable _ (by simp [roundKeep])).trans old.source,
    old.sys.kept (fun q hq=>stable q (common q (Or.inl hq))),(stable _ (by simp [roundKeep])).trans old.tag,inc,
    (read_buffer_memory_congr t _ raw _ _).trans (stored_read u d val),atEnd,?_,stable,change1.trans change2⟩⟩
  intro b n space away₁ away₂
  exact (Open.outside_read written bounds.2 (by decide) b n space away₂).trans
    (Open.outside_read tagging (by decide) (by decide) b n space away₁)
end CommitGolfCandidate.Chained.BinaryMachine.Check
