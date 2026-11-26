import CommitGolfCandidate.S5CapCounters
import CommitGolfCandidate.S5CapUpperMemory
import CommitGolfCandidate.S5CapPairBody
import CommitGolfCandidate.S5SlotLoop
namespace CommitGolfCandidate.S5Machine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W Outside)
theorem pair_entry (o : Oracle) (x : CheckInput) (s : MachineState) (st : SlotState o.compression x 171 s) :
    ∃ t,Flow o s t 4 0 ∧ PairState o.compression x 0 t := by
  let u:=s.setPC (pcAt 823)
  let v:=(u.setReg .x23 0).setPC (pcAt 824)
  let t:=(v.setReg .x14 171).setPC (pcAt 825)
  have test:=slots_finished o x s st
  have zero:=imm_step o u 823 .x23 .x0 0 0 rfl (known (by decide +kernel)) rfl
  have lim:=imm_step o v 824 .x14 .x0 171 171 rfl (known (by decide +kernel)) rfl
  have old : Evidence o.compression x 0 s:=⟨st.table.mark,st.table.data,st.previous,st.env.read⟩
  have cache : Cache s (progress o.compression x 0 0):=by
    have empty : progress o.compression x 0 0=(fun _ _=>0):=by funext h i;simp [progress]
    rw [empty];exact blank_cache s st.table.blank
  have same : t.mem=s.mem:=rfl
  exact ⟨t,(test.trans zero).trans lim,⟨rfl,rfl,rfl,⟨st.env.root,st.env.row,st.env.chain,(read_buffer_memory_congr t s same _ _).trans st.env.read⟩,old.same same,cache.same same⟩⟩

private theorem untouched {a b : Option Late.Digest} (h : touched a b=false):a=none ∧ b=none:=by
  cases a <;> cases b <;> simp_all [touched]

set_option maxRecDepth 14000 in
theorem make_pair (o : Oracle) (x : CheckInput) (p : Nat) (s : MachineState) (st : PairState o.compression x p s) (small : p<171) :
    let a:=lookup o.compression x 128 (2*p)
    let b:=lookup o.compression x 128 (2*p+1)
    ∃ t steps,steps≤239 ∧ PairMade o s t p 907 steps a b (slotValue x 0 p) := by
  let a:=lookup o.compression x 128 (2*p)
  let b:=lookup o.compression x 128 (2*p+1)
  let slot:=slotValue x 0 p
  obtain ⟨u,h⟩:=pair_head o s p small a b (st.pc.trans (congrArg pcAt (if_pos small))) st.ctr
    (st.entries.mark _ (by omega)) (st.entries.mark _ (by omega))
  have e:=st.entries.same h.mem
  have ctr:=(h.keep .x23 (by decide)).trans st.ctr
  have tail : ∃ t n,n≤222 ∧ PairMade o u t p 907 n a b slot:=by
    cases match_ : touched a b
    · obtain ⟨left,right⟩:=untouched match_
      obtain ⟨t,done_⟩:=copy_vacant o u p small slot (h.pc.trans (congrArg pcAt (by rw [match_];rfl))) ctr h.dest (e.slot p small)
      exact ⟨t,12,by decide,by rw [left,right];exact done_⟩
    · exact touched_pair o u p small a b slot match_ (h.pc.trans (congrArg pcAt (by rw [match_];rfl))) ctr h.left h.right h.dest
        ((h.keep _ (by decide)).trans st.env.row) ((h.keep _ (by decide)).trans st.env.chain) (e.slot p small)
        (e.computed (2*p) (by omega)) (e.computed (2*p+1) (by omega))
  obtain ⟨t,n,lim,body⟩:=tail
  exact ⟨t,17+n,by omega,⟨by simpa only [Nat.zero_add] using h.run.trans body.run,body.pc,body.output,h.keep.trans body.keep,
    (ChainOutside.same h.mem).trans body.frame⟩⟩

theorem pair_cycle (o : Oracle) (x : CheckInput) (p : Nat) (s : MachineState) (st : PairState o.compression x p s) (small : p<171) :
    ∃ t n q,n≤241 ∧ q≤16 ∧ Flow o s t n q ∧ PairState o.compression x (p+1) t := by
  obtain ⟨u,a,lim,body⟩:=make_pair o x p s st small
  have ctr:=(body.keep _ (by decide)).trans st.ctr
  have end_:=(body.keep _ (by decide)).trans st.bound
  have latch:=counted o u 907 825 p 171 .x14 (by decide) body.pc ctr end_ small (by decide) (by decide +kernel) (by decide +kernel)
  let t:=countedState u p (pairPC (p+1))
  have cap : p<paddedCount 0:=by change p<172;omega
  have bounds:=node_range 0 p (by decide) cap
  have geo:=cap_geometry ⟨0,by decide⟩
  have data:=st.entries.after_node body.frame (geo.1.trans bounds.1) (bounds.2.1.trans geo.2.1) bounds.2.2
  have same : t.mem=u.mem:=rfl
  have entries:=data.same (t:=t) same
  have keep (r : Reg) (h : r∈capRegs) (ne : r≠.x23) : t.getReg r=s.getReg r:=MachineState.getReg_setPC.trans
    ((MachineState.getReg_setReg_ne _ _ _ _ ne.symm).trans (body.keep r h))
  have cached:=st.cache.write (by decide) cap (capVal o.compression x 0 0 p) (body.output.trans (cache_base 0 p small).symm) body.frame
  rw [write_progress] at cached
  refine ⟨t,a+2,_,by omega,?_,body.run.trans latch,⟨rfl,rfl,(keep _ (by decide) (by decide)).trans st.bound,
    ⟨(keep _ (by decide) (by decide)).trans st.env.root,(keep _ (by decide) (by decide)).trans st.env.row,
     (keep _ (by decide) (by decide)).trans st.env.chain,entries.root⟩,entries,cached.same same⟩⟩
  unfold pairCalls;split <;> decide

theorem pairs (o : Oracle) (x : CheckInput) (p n : Nat) (s : MachineState) (st : PairState o.compression x p s) (bound : p+n≤171) :
    ∃ t k q,k≤241*n ∧ q≤16*n ∧ Flow o s t k q ∧ PairState o.compression x (p+n) t := by
  induction n generalizing p s with
  | zero=>exact ⟨s,0,0,by decide,by decide,Flow.refl o s,st⟩
  | succ n ih=>
    obtain ⟨u,a,q,al,ql,head,mid⟩:=pair_cycle o x p s st (by omega)
    obtain ⟨t,b,k,bl,kl,tail,last⟩:=ih (p+1) u mid (by omega)
    exact ⟨t,a+b,q+k,by omega,by omega,head.trans tail,by simpa only [Nat.add_assoc,Nat.add_comm 1 n] using last⟩
end CommitGolfCandidate.S5Machine.Check
