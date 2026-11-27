import CommitGolfCandidate.Stage3cChainCheckFirst
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Chained
open Open (W)
def armOps : List Sym.Calc:=[.addi .x12 .x26 0,.addi .x29 .x30 4095]
def armDest (h : Height) (dst j : Nat) := if j+2=calls h then dst else chainBuf
def armSteps (h : Height) (j : Nat) := if j+2=calls h then 6 else 5
def ArmKeeps (s t : MachineState) := ∀ q,q≠.x12 → q≠.x29 → t.getReg q=s.getReg q
structure Armed (o : Oracle) (h : Height) (l r : Output) (dst j : Nat) (s t : MachineState) : Prop where
  run : Flow o s t (armSteps h j) 0
  pc : t.pc=pcAt 207
  dest : t.getReg .x12=W (armDest h dst j)
  keep : ArmKeeps s t
  input : readBuffer t chainBuf 96=stageInput o.compression h l r (j+1)
  mem : let k : Fin 16:=⟨(j+1)%16,by omega⟩
        t.mem=(tagStore s chainBuf (tagWord h k)).mem

private theorem choose_dest (o : Oracle) (s : MachineState) (h : Height) (dst j : Nat) (pc : s.pc=pcAt 205)
    (counter : s.getReg .x6=W (j+1)) (last : s.getReg .x29=W (calls h-1)) (limit : j+2≤calls h) (count : calls h≤16)
    (saved : s.getReg .x28=W dst) (temp : s.getReg .x12=W chainBuf) :
    ∃ t,Flow o s t (if j+2=calls h then 2 else 1) 0 ∧ t.pc=pcAt 207 ∧ t.getReg .x12=W (armDest h dst j) ∧
      t.mem=s.mem ∧ ∀ q,q≠.x12→t.getReg q=s.getReg q := by
  by_cases finished : j+2=calls h
  · have eq : s.getReg .x6=s.getReg .x29:=counter.trans ((congrArg W (by omega)).trans last.symm)
    have br:=branch o s 205 207 .ne .x6 .x29 (by decide +kernel) pc false (by simp [Rel.test,eq])
    let u:=s.setPC (pcAt 206)
    let t:=(u.setReg .x12 (W dst)).setPC (pcAt 207)
    have mv:=imm_step o u 206 .x12 .x28 0 (W dst) rfl (known (by decide +kernel)) ((BitVec.add_zero _).trans saved)
    rw [if_pos finished,armDest,if_pos finished]
    exact ⟨t,br.trans mv,rfl,rfl,rfl,fun q ne=>MachineState.getReg_setPC.trans ((MachineState.getReg_setReg_ne _ _ _ _ ne.symm).trans MachineState.getReg_setPC)⟩
  · have ne : s.getReg .x6≠s.getReg .x29:=by
      rw [counter,last];intro e;have z:=congrArg BitVec.toNat e
      simp only [W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : j+1<2^64),Nat.mod_eq_of_lt (by omega : calls h-1<2^64)] at z;omega
    have br:=branch o s 205 207 .ne .x6 .x29 (by decide +kernel) pc true (bne_iff_ne.mpr ne)
    rw [if_neg finished,armDest,if_neg finished]
    exact ⟨_,br,rfl,MachineState.getReg_setPC.trans temp,rfl,fun q _=>MachineState.getReg_setPC⟩

set_option maxRecDepth 10000 in
private theorem arm_keep (z : MachineState) (q : Reg) (a : q≠.x12) (b : q≠.x29) : ((armOps.foldl Sym.bump Sym.original) q).eval z=z.getReg q:=by cases q <;> first | contradiction | rfl
attribute [local irreducible] readBuffer Sym.evaluated
theorem arm_query (o : Oracle) (s : MachineState) (h : Height) (l r : Output) (dst j : Nat)
    (old : InRound o.compression h dst l r j s) (limit : j+2≤calls h) (count : calls h≤16) (cut : 8≤h.val ∧ h.val<16) :
    ∃ t,Armed o h l r dst j s t := by
  let k : Fin 16:=⟨j+1,by omega⟩
  let tag:=tagWord h k
  let u:=execInstrBr s (.ADD .x12 .x7 .x6)
  have add:=one_flow o (t:=u) old.pc (known (by decide +kernel)) (i:=.ADD .x12 .x7 .x6) rfl
  have up : u.pc=pcAt 202:=(congrArg (·+4) old.pc).trans (pc_succ 201)
  have ut : u.getReg .x12=tag:=by
    change s.getReg .x7+s.getReg .x6=_;rw [old.tag,old.counter];unfold tag tagWord;simp only [show BitVec.ofNat 64 (0 : Fin 16).val=0#64 by rfl,BitVec.add_zero];rfl
  have uk (q : Reg) (a : q≠.x12) : u.getReg q=s.getReg q:=MachineState.getReg_setPC.trans (MachineState.getReg_setReg_ne _ _ _ _ a.symm)
  let z:=(tagStore u chainBuf tag).setPC (pcAt 203)
  have to_ : u.getReg .x26=W chainBuf:=(uk _ (by decide)).trans old.sys.address
  have mark:=store_step o u 202 .x26 .x12 64 (chainBuf+64) tag up (known (by decide +kernel))
    ((congrArg (·+signExtend12 64) to_).trans (BitVec.ofNat_add chainBuf 64).symm) ut (by decide) (by decide)
  have zk (q : Reg) (a : q≠.x12) : z.getReg q=s.getReg q:=(tag_regs u _ tag _ q).trans (uk q a)
  let v:=Sym.evaluated armOps z
  obtain ⟨code,regs,mem,ip⟩:=Sym.compiled o armOps 203 z rfl (by decide +kernel) (by change ∀ e∈([] : List (Sym.Expr×Nat)),_;simp)
  have vk (q : Reg) (a : q≠.x12) (b : q≠.x29) : v.getReg q=s.getReg q:=by
    exact (regs q).trans ((arm_keep z q a b).trans (zk q a))
  have saved : v.getReg .x28=W dst:=(vk _ (by decide) (by decide)).trans old.sys.save
  have temp : v.getReg .x12=W chainBuf:=(regs .x12).trans ((BitVec.add_zero _).trans ((zk _ (by decide)).trans old.sys.address))
  have release : v.getReg .x29=W (calls h-1):=by
    apply (regs .x29).trans;change z.getReg .x30+(-1#64)=_;rw [zk _ (by decide),old.sys.amount,←BitVec.sub_eq_add_neg]
    exact BitVec.ofNat_sub_ofNat_of_le _ 1 (by decide) (by omega)
  obtain ⟨t,choice,ep,dest,same,keep⟩:=choose_dest o v h dst j ip ((vk _ (by decide) (by decide)).trans old.counter) release limit count saved temp
  have memory : t.mem=(tagStore s chainBuf tag).mem:=same.trans mem
  have encoded:=tagged_input s chainBuf _ _ tag (by decide) (by decide) old.value old.scratch.second old.scratch.pad
  have next : parentBlock (chainReply o.compression h l r j) 0 tag=stageInput o.compression h l r (j+1) := by
    let ix : Fin 15:=⟨j,by omega⟩
    apply (parentBlock_next h ix _).trans
    unfold stageInput parentQueries
    rw [List.getLastD_concat,workClass,if_pos cut];rfl
  refine ⟨t,⟨?_,ep,dest,fun q a b=>(keep q a).trans (vk q a b),
    (read_buffer_memory_congr t _ memory _ _).trans (encoded.trans next),?_⟩⟩
  · have run:=((add.trans mark).trans code).trans choice
    unfold armSteps;split <;> rename_i e <;> simp only [e,ite_true,ite_false] at run <;> exact run
  · simpa only [Nat.mod_eq_of_lt (show j+1<16 by omega)] using memory
end CommitGolfCandidate.Chained.BinaryMachine.Check
