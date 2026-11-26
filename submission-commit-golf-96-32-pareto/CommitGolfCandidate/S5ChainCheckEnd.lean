import CommitGolfCandidate.S5ChainCheckRound
namespace CommitGolfCandidate.S5Machine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Chained
open Open (W)
structure ChainDone (o : Oracle) (s t : MachineState) (h : Height) (dst back steps queries : Nat) (l r : Output) : Prop where
  run : Flow o s t steps queries
  pc : t.pc=pcAt back
  value : readBuffer t dst 32=parentDigest o.compression h l r
  keep : ParentPreserves s t
  frame : ChainOutside s t dst

private theorem round_live (q : Reg) (good : parentLive q) : roundKeep q:=by
  cases q <;> simp_all [parentLive,roundKeep]
attribute [local irreducible] readBuffer writeBits
theorem last_query (o : Oracle) (s u : MachineState) (h : Height) (l r : Output) (dst j back : Nat)
    (step : RoundResult o h l r dst j s u) (last : j+2=calls h) (ra : s.getReg .x1=pcAt back) (limit : back<2336)
    (da : dst%8=0) (ds : dst+32≤MEMORY_BYTES) :
    ∃ t n,n≤22 ∧ ChainDone o s t h dst back n 1 l r := by
  let k : Fin 16:=⟨(j+1)%16,by omega⟩
  let z:=(u.setReg .x12 (W dst)).setPC (pcAt 211)
  have pu : u.pc=pcAt 210:=step.pc.trans (congrArg pcAt (if_neg (by omega)))
  have restore:=imm_step o u 210 .x12 .x28 0 (W dst) pu (known (by decide +kernel)) ((BitVec.add_zero _).trans step.sys.save)
  have zk (q : Reg) (ne : q≠.x12) : z.getReg q=u.getReg q:=MachineState.getReg_setPC.trans (MachineState.getReg_setReg_ne _ _ _ _ ne.symm)
  have loc : armDest h dst j=dst:=if_pos last
  have m : z.mem=(writeBits (tagStore s chainBuf (tagWord h k)) (W dst) (chainReply o.compression h l r (j+1))).mem:=by
    have eq:=step.mem;dsimp only at eq;rw [loc] at eq;exact eq
  obtain ⟨v,n,price,mask⟩:=check_projection o (tagStore s chainBuf (tagWord h k)) z h dst (chainReply o.compression h l r (j+1)) rfl
    ((zk _ (by decide)).trans step.sys.width) rfl da ds m
  have keep : ParentPreserves s v := by
    intro q ok;have safe:=round_live q ok;exact (mask.keep q ok).trans ((zk q safe.2.1).trans (step.keep q safe))
  have ret:=parent_return o v back limit mask.pc ((keep .x1 (by simp [parentLive])).trans ra)
  let t:=v.setPC (pcAt back)
  have digestEq : storeReply h (chainReply o.compression h l r (j+1))=parentDigest o.compression h l r:=by
    unfold parentDigest queries chainReply stageInput;rw [show calls h-1=j+1 by omega]
  have mem : t.mem=(writeBits (tagStore s chainBuf (tagWord h k)) (W dst) (parentDigest o.compression h l r)).mem:=
    mask.mem.trans (congrArg (fun v=> (writeBits (tagStore s chainBuf (tagWord h k)) (W dst) v).mem) digestEq)
  have spent : roundSteps h j=9:=by simp [roundSteps,armSteps,last]
  have actual:=((step.run.trans restore).trans mask.run).trans ret
  rw [spent] at actual
  refine ⟨t,9+1+n+1,by omega,⟨actual,rfl,(read_buffer_memory_congr t _ mem _ _).trans (store_read _ _ _),
    fun q good=>MachineState.getReg_setPC.trans (keep q good),?_⟩⟩
  intro q ok align lo hi
  apply (congrFun mem _).trans
  apply (reply_outside _ dst _ ds da q ok align hi).trans
  apply store_far s (chainBuf+64) _ (by decide) q ok align
  change q<65792 ∨ 65792+352≤q at lo;change q<66048+64 ∨ 66048+64+8≤q;omega

theorem chain_tail (o : Oracle) (h : Height) (l r : Output) (dst back n j : Nat) (s : MachineState)
    (old : InRound o.compression h dst l r j s) (num : j+2+n=calls h) (count : calls h≤16)
    (cut : 8≤h.val ∧ h.val<16) (ra : s.getReg .x1=pcAt back) (limit : back<2336) (da : dst%8=0) (ds : dst+32≤MEMORY_BYTES) :
    ∃ t steps,steps≤9*(n+1)+13 ∧ ChainDone o s t h dst back steps (n+1) l r := by
  induction n generalizing s j with
  | zero=>
    have last : j+2=calls h:=by omega
    obtain ⟨u,round⟩:=round_query o h l r dst j s old (by omega) count cut da ds
    exact last_query o s u h l r dst j back round last ra limit da ds
  | succ n ih=>
    have more : j+2<calls h:=by omega
    have loc : armDest h dst j=chainBuf:=if_neg (by omega)
    obtain ⟨u,round⟩:=round_query o h l r dst j s old (by omega) count cut da ds
    have keep : ParentPreserves s u:=fun q ok=>round.keep q (round_live q ok)
    have next : InRound o.compression h dst l r (j+1) u:=by
      refine ⟨round.pc.trans (congrArg pcAt (if_pos more)),round.sys,round.tag,round.counter,round.source,?_,?_,?_⟩
      · rw [←loc];exact round.value
      · apply (round.prior _ _ (by decide) (Or.inl (by decide)) (by rw [loc];decide)).trans old.scratch.second
      · apply (round.prior _ _ (by decide) (Or.inr (by decide)) (by rw [loc];decide)).trans old.scratch.pad
    obtain ⟨t,steps,budget,tail⟩:=ih (s:=u) (j:=j+1) next (by omega) ((keep _ (by simp [parentLive])).trans ra)
    have spent : roundSteps h j=8:=by simp [roundSteps,armSteps,Nat.ne_of_lt more]
    have all:=round.run.trans tail.run
    rw [spent] at all
    refine ⟨t,8+steps,by omega,⟨?_,tail.pc,tail.value,keep.trans tail.keep,round.frame.trans tail.frame⟩⟩
    simpa only [Nat.add_comm 1 (n+1)] using all

theorem chained_parent (o : Oracle) (s : MachineState) (h : Height) (dst back : Nat) (cut : 8≤h.val ∧ h.val<16)
    (pc : s.pc=pcAt 173) (count : s.getReg .x30=W (calls h)) (width : s.getReg .x31=W (wireWidth h))
    (level : s.getReg .x29=W (h.val+1)) (src : s.getReg .x10=W rowBuf) (dest : s.getReg .x12=W dst)
    (scratch : s.getReg .x26=W chainBuf) (ra : s.getReg .x1=pcAt back) (limit : back<2336) (da : dst%8=0) (ds : dst+32≤MEMORY_BYTES) :
    ∃ t steps,steps≤9*calls h+30 ∧ ChainDone o s t h dst back steps (calls h) (readBuffer s rowBuf 32) (readBuffer s (rowBuf+32) 32) := by
  have n : 2≤calls h ∧ calls h≤16:=
    (by decide +kernel : ∀ k : Height,8≤k.val ∧ k.val<16 → 2≤calls k ∧ calls k≤16) h cut
  obtain ⟨u,entry⟩:=chain_entry o s h dst (by omega) pc count width level src dest scratch
  obtain ⟨z,first⟩:=first_query o s u h dst entry cut
  obtain ⟨t,steps,b,tail⟩:=chain_tail o h _ _ dst back (calls h-2) 0 z first.ready (by omega) n.2 cut
    ((first.keep _ (by simp [parentLive])).trans ra) limit da ds
  refine ⟨t,26+steps,by omega,⟨?_,tail.pc,tail.value,first.keep.trans tail.keep,first.frame.trans tail.frame⟩⟩
  have all:=first.run.trans tail.run;convert all using 1 <;> omega
end CommitGolfCandidate.S5Machine.Check
