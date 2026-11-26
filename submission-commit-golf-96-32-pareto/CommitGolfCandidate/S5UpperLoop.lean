import CommitGolfCandidate.S5UpperArgs
import CommitGolfCandidate.S5CapCounters
namespace CommitGolfCandidate.S5Machine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W)
def upperPC (d p : Nat):=if p<layerCount (d+1) then upperLoop d else upperEntry (d+1)
structure UpperState (H : Compression) (x : CheckInput) (d p : Nat) (s : MachineState) : Prop where
  pc : s.pc=pcAt (upperPC d p)
  ctr : s.getReg .x23=W p
  count : s.getReg .x9=W (layerCount (d+1))
  src : s.getReg .x14=W (layerStart d)
  dst : s.getReg .x15=W (layerStart (d+1))
  env : CapEnv x s
  entries : Evidence H x 0 s
  cache : Cache s (progress H x (d+1) p)
structure TierState (H : Compression) (x : CheckInput) (d : Nat) (s : MachineState) : Prop where
  pc : s.pc=pcAt (upperEntry d)
  env : CapEnv x s
  entries : Evidence H x 0 s
  cache : Cache s (progress H x (d+1) 0)

theorem upper_header (o : Oracle) (x : CheckInput) (s : MachineState) (d : Nat) (hd : d<8) (st : TierState o.compression x d s) :
    ∃ t,Flow o s t (upperHeader d).length 0 ∧ UpperState o.compression x d 0 t := by
  obtain ⟨req,_,write,_,src,dst,ctr,cnt,_,_⟩:=upper_symbols ⟨d,hd⟩
  have sites:=upper_sites ⟨d,hd⟩
  obtain ⟨run,regs,mem,ip⟩:=Sym.compiled o _ _ s st.pc sites.1 (by change Sym.requirements Sym.original (upperHeader d)=[] at req;rw [req];simp)
  let t:=Sym.evaluated (upperHeader d) s
  have keep (q : Reg) (h : q∉[Reg.x14,.x15,.x23,.x9]) : t.getReg q=s.getReg q:=(regs q).trans (sym_keep s _ _ write q h)
  have pos:= (cap_geometry ⟨d+1,by omega⟩).2.2.2.1
  have ev:=st.entries.same mem
  exact ⟨t,run,⟨ip.trans (congrArg pcAt (sites.2.1.trans (if_pos pos).symm)),(regs _).trans (congrArg (fun e : Sym.Expr=>e.eval s) ctr),
    (regs _).trans (congrArg (fun e : Sym.Expr=>e.eval s) cnt),(regs _).trans (congrArg (fun e : Sym.Expr=>e.eval s) src),
    (regs _).trans (congrArg (fun e : Sym.Expr=>e.eval s) dst),⟨(keep _ (by decide)).trans st.env.root,
    (keep _ (by decide)).trans st.env.row,(keep _ (by decide)).trans st.env.chain,ev.root⟩,ev,st.cache.same mem⟩⟩

attribute [local irreducible] readBuffer Sym.evaluated
theorem upper_cycle (o : Oracle) (x : CheckInput) (s : MachineState) (d p : Nat) (hd : d<8) (hp : p<layerCount (d+1))
    (st : UpperState o.compression x d p s) :
    ∃ t n,n≤37 ∧ Flow o s t n 1 ∧ UpperState o.compression x d (p+1) t := by
  obtain ⟨_,_,_,_,alen,code,legal,inc,br,latchEnd,_,_⟩:=upper_sites ⟨d,hd⟩
  obtain ⟨u,addr,ip,source,dest,um,keepA⟩:=upper_args o s d p hd hp (st.pc.trans (congrArg pcAt (if_pos hp))) st.ctr st.src st.dst
  have row:=cache_row u _ (st.cache.same um) d p hd hp
  simp only [progress,Nat.lt_succ_self,true_or,ite_true] at row
  obtain ⟨v,k,lim,body⟩:=hash_upper o x 0 u d p (configPC d) hd hp code legal ip source dest ((keepA _ (by decide)).trans st.env.chain) row
  have keep:=keepA.trans body.keep
  have width : layerCount (d+1)<2^64:=((cap_geometry ⟨d+1,by omega⟩).2.2.2.2.1.trans (cap_geometry ⟨d+1,by omega⟩).2.2.2.2.2.1).trans_lt (by decide)
  have lat:=counted o v (upperLatch d) (upperLoop d) p (layerCount (d+1)) .x9 (by decide) body.pc ((keep _ (by decide)).trans st.ctr)
    ((keep _ (by decide)).trans st.count) hp width inc br
  change upperLatch d+2=upperEntry (d+1) at latchEnd
  rw [latchEnd] at lat
  let t:=countedState v p (upperPC d (p+1))
  have tk (q : Reg) (h : q∈capRegs) (ne : q≠.x23) : t.getReg q=s.getReg q:=MachineState.getReg_setPC.trans
    ((MachineState.getReg_setReg_ne _ _ _ _ ne.symm).trans (keep q h))
  have geo:=cap_geometry ⟨d+1,by omega⟩
  have inBounds:=hp.trans_le geo.2.2.2.2.1
  have bounds:=node_range (d+1) p (by omega) inBounds
  have ev:=((st.entries.same um).after_node body.frame (geo.1.trans bounds.1) (bounds.2.1.trans geo.2.1) bounds.2.2).same (t:=t) rfl
  have cache:=(st.cache.same um).write (by omega) inBounds _ body.value body.frame
  rw [write_progress] at cache
  change (upperAddress d).length≤12 at alen
  exact ⟨t,(upperAddress d).length+k+2,by omega,(addr.trans body.run).trans lat,⟨rfl,rfl,
    (tk _ (by decide) (by decide)).trans st.count,(tk _ (by decide) (by decide)).trans st.src,(tk _ (by decide) (by decide)).trans st.dst,
    ⟨(tk _ (by decide) (by decide)).trans st.env.root,(tk _ (by decide) (by decide)).trans st.env.row,(tk _ (by decide) (by decide)).trans st.env.chain,ev.root⟩,
    ev,cache.same rfl⟩⟩

theorem upper_rows (o : Oracle) (x : CheckInput) (d n p : Nat) (s : MachineState) (hd : d<8) (bound : p+n≤layerCount (d+1))
    (st : UpperState o.compression x d p s) : ∃ t k,k≤37*n ∧ Flow o s t k n ∧ UpperState o.compression x d (p+n) t := by
  induction n generalizing p s with
  | zero=>exact ⟨s,0,Nat.zero_le _,Flow.refl o s,st⟩
  | succ n ih=>
    obtain ⟨u,a,al,front,mid⟩:=upper_cycle o x s d p hd (by omega) st
    obtain ⟨t,b,bl,back,final⟩:=ih (p+1) u (by omega) mid
    exact ⟨t,a+b,by omega,by simpa only [Nat.add_comm 1 n] using front.trans back,by simpa only [Nat.add_assoc,Nat.add_comm 1 n] using final⟩

theorem upper_tier (o : Oracle) (x : CheckInput) (d : Nat) (s : MachineState) (hd : d<8) (st : TierState o.compression x d s) :
    ∃ t k,k≤6+37*layerCount (d+1) ∧ Flow o s t k (layerCount (d+1)) ∧ TierState o.compression x (d+1) t := by
  obtain ⟨u,head,mid⟩:=upper_header o x s d hd st
  obtain ⟨t,k,lim,back,last⟩:=upper_rows o x d (layerCount (d+1)) 0 u hd (by omega) mid
  rw [Nat.zero_add] at last
  have len:=(upper_sites ⟨d,hd⟩).2.2.1
  change (upperHeader d).length≤6 at len
  have cache:=last.cache
  rw [advance_progress] at cache
  exact ⟨t,(upperHeader d).length+k,by omega,by simpa only [Nat.zero_add] using head.trans back,
    ⟨last.pc.trans (congrArg pcAt (if_neg (Nat.lt_irrefl _))),last.env,last.entries,cache⟩⟩

def upperTotal (d n : Nat) : Nat:=match n with
  | 0=>0
  | k+1=>layerCount (d+1)+upperTotal (d+1) k
theorem upper_tiers (o : Oracle) (x : CheckInput) (d n : Nat) (s : MachineState) (bound : d+n≤8) (st : TierState o.compression x d s) :
    ∃ t k,k≤6*n+37*upperTotal d n ∧ Flow o s t k (upperTotal d n) ∧ TierState o.compression x (d+n) t := by
  induction n generalizing s d with
  | zero=>exact ⟨s,0,Nat.zero_le _,Flow.refl o s,st⟩
  | succ n ih=>
    obtain ⟨u,a,al,head,mid⟩:=upper_tier o x d s (by omega) st
    obtain ⟨t,b,bl,back,last⟩:=ih (d+1) u (by omega) mid
    exact ⟨t,a+b,by simp only [upperTotal];omega,head.trans back,by simpa only [Nat.add_assoc,Nat.add_comm 1 n] using last⟩

theorem build_upper (o : Oracle) (x : CheckInput) (s : MachineState) (st : PairState o.compression x 171 s) :
    ∃ t k,k≤6486 ∧ Flow o s t k 174 ∧ t.pc=pcAt 1094 ∧ CapEnv x t ∧ Evidence o.compression x 0 t ∧ Cache t (capVal o.compression x 0) := by
  have cache:=st.cache
  rw [show 171=layerCount 0 by decide,advance_progress] at cache
  obtain ⟨t,k,lim,flow,last⟩:=upper_tiers o x 0 8 s (by decide) ⟨st.pc,st.env,st.entries,cache⟩
  refine ⟨t,k,lim,flow,last.pc,last.env,last.entries,⟨?_,last.cache.gap⟩⟩
  intro h hr j bound
  have eq:=last.cache.node h hr j bound
  change readBuffer t (nodeAt h j) 32=progress o.compression x 9 0 h j at eq
  simpa only [progress,hr,true_or,ite_true] using eq
end CommitGolfCandidate.S5Machine.Check
