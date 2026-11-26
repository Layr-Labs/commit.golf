import CommitGolfCandidate.S5PairRow
import CommitGolfCandidate.S5CapChooseChild
namespace CommitGolfCandidate.S5Machine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W Outside)
def pairCalls (a b : Option Late.Digest) :=if touched a b then 16 else 0
structure PairMade (o : Oracle) (s t : MachineState) (p stop steps : Nat) (a b : Option Late.Digest) (slot : Late.Digest) : Prop where
  run : Flow o s t steps (pairCalls a b)
  pc : t.pc=pcAt stop
  output : readBuffer t (nodeAt 0 p) 32=pairValue o.compression a b slot
  keep : CapKeeps s t
  frame : ChainOutside s t (nodeAt 0 p)

private def vacantOps : List Sym.Calc:=[.lui .x6 21,.slli .x29 .x23 5,.add .x6 .x6 .x29]
private def vacantCopy : CopySpec:=⟨.x29,.x6,.x4,0,0⟩
private theorem outside_pair (p : Nat) (bound : p<171) : capBase≤nodeAt 0 p ∧ nodeAt 0 p+32≤saltBuf ∧ nodeAt 0 p%8=0 := by
  obtain ⟨lo,hi,al⟩:=node_range 0 p (by decide) (by change p<172;omega);exact ⟨lo,hi.trans (by decide),al⟩
private theorem vacant_math (s : MachineState) (q : Reg) (a : q≠.x6) (b : q≠.x29) :
    ((vacantOps.foldl Sym.bump Sym.original) q).eval s=s.getReg q:=by cases q <;> first | contradiction | rfl
theorem copy_vacant (o : Oracle) (s : MachineState) (p : Nat) (bound : p<171) (slot : Late.Digest)
    (pc : s.pc=pcAt 842) (pos : s.getReg .x23=W p) (dst : s.getReg .x4=W (nodeAt 0 p))
    (read : readBuffer s (slotAddr p) 32=slot) :
    ∃ t,PairMade o s t p 907 12 none none slot := by
  let u:=Sym.evaluated vacantOps s
  obtain ⟨math_,regs,mem,ip⟩:=Sym.compiled o vacantOps 842 s pc (by decide +kernel) (by change ∀ e∈([] : List (Sym.Expr×Nat)),_;simp)
  have keep (q : Reg) (a : q≠.x6) (b : q≠.x29):u.getReg q=s.getReg q:=(regs q).trans (vacant_math s q a b)
  have src : u.getReg .x6=W (slotAddr p):=by
    apply (regs .x6).trans;change W slotBase+(s.getReg .x23 <<< 5)=_;rw [pos];unfold W;rw [Open.shifted,←BitVec.ofNat_add];apply congrArg (BitVec.ofNat 64);dsimp [slotAddr];omega
  have where_:=outside_pair p bound
  have al : slotAddr p%8=0:=by dsimp [slotAddr,slotBase];omega
  have apart : slotAddr p+32≤nodeAt 0 p:=(by dsimp [slotAddr,slotBase,capBase];omega : slotAddr p+32≤capBase).trans where_.1
  obtain ⟨v,copy⟩:=copy_words o u 845 (slotAddr p) (nodeAt 0 p) 4 vacantCopy (by unfold CopySites;decide +kernel) (by decide) (by decide) ip src
    ((keep _ (by decide) (by decide)).trans dst) ⟨al,apart.trans (by have :=where_.2.1;unfold saltBuf MEMORY_BYTES at *;omega)⟩
    ⟨where_.2.2,where_.2.1.trans (by decide)⟩ (Or.inl apart)
  have jump_:=jump o v 853 907 .x0 (by decide +kernel) copy.pc
  let t:=v.setPC (pcAt 907)
  have data : readBuffer t (nodeAt 0 p) 32=slot:=(copied_read (a:=slotAddr p) (b:=nodeAt 0 p) (n:=4) copy.data al where_.2.2).trans
    ((read_buffer_memory_congr u s mem _ _).trans read)
  refine ⟨t,⟨(math_.trans copy.run).trans jump_,rfl,data,?_,ChainOutside.output (fun q h a e=>(copy.data.outside q h a e).trans (congrFun mem _))⟩⟩
  intro q h;apply MachineState.getReg_setPC.trans;apply (copy.keep q ?_).trans (keep q ?_ ?_)
  all_goals cases q <;> simp_all [capRegs,vacantCopy]

private theorem side_keeps (q : Reg) (h : q∈capRegs ∨ q=.x4 ∨ q=.x28) : q≠.x6 ∧ q≠.x29:=by cases q <;> simp_all [capRegs]
private theorem hit_model (H : Compression) (l r : Option Late.Digest) (slot : Late.Digest) (hit : touched l r=true) :
    pairValue H l r slot=Chained.parentDigest H (S5.height 15) (l.getD slot) (r.getD slot) := by cases l <;> cases r <;> first | rfl | contradiction
attribute [local irreducible] readBuffer
set_option maxRecDepth 10000 in
theorem touched_pair (o : Oracle) (s : MachineState) (p : Nat) (small : p<171) (a b : Option Late.Digest) (slot : Late.Digest)
    (hit : touched a b=true) (pc : s.pc=pcAt 854) (pos : s.getReg .x23=W p)
    (left : s.getReg .x7=markedWord a) (right : s.getReg .x28=markedWord b) (dst : s.getReg .x4=W (nodeAt 0 p))
    (row : s.getReg .x25=W rowBuf) (scratch : s.getReg .x26=W chainBuf)
    (read : readBuffer s (slotAddr p) 32=slot)
    (aVal : ∀ v,a=some v → readBuffer s (bucketAddress (2*p)) 32=v) (bVal : ∀ v,b=some v → readBuffer s (bucketAddress (2*p+1)) 32=v) :
    ∃ t n,n≤222 ∧ PairMade o s t p 907 n a b slot := by
  obtain ⟨u,erase⟩:=clear_words o s 854 rowBuf 12 .x25 (by unfold ZeroSites;decide +kernel) (by decide) pc row (by decide) (by decide)
  have area (j : Nat) (bj : j<342) : rowBuf+96≤bucketAddress j ∧ bucketAddress j+32≤MEMORY_BYTES := by dsimp [rowBuf,bucketAddress,compBase,MEMORY_BYTES];omega
  have sa : rowBuf+96≤slotAddr p ∧ slotAddr p+32≤MEMORY_BYTES:=by dsimp [rowBuf,slotAddr,slotBase,MEMORY_BYTES];omega
  have readU (where_ : Nat) (lo : rowBuf+96≤where_) (size : where_+32≤MEMORY_BYTES) :
      readBuffer u where_ 32=readBuffer s where_ 32:=Open.outside_read erase.outside (by decide) (by decide) _ _ size (Or.inr lo)
  have sU:=(readU _ sa.1 sa.2).trans read
  have gL:=area (2*p) (by omega)
  obtain ⟨v,m,ml,left_⟩:=fill_child o u false p small a slot erase.last ((erase.regs _).trans pos) ((erase.regs _).trans row)
    ((erase.regs _).trans left) sU (fun val prev=>(readU _ gL.1 gL.2).trans (aVal val prev))
  have vk (q : Reg) (h : q∈capRegs ∨ q=.x4 ∨ q=.x28) : v.getReg q=s.getReg q:=(left_.keep q (side_keeps q h).1 (side_keeps q h).2).trans (erase.regs q)
  have readV (where_ : Nat) (lo : rowBuf+96≤where_) (size : where_+32≤MEMORY_BYTES) :
      readBuffer v where_ 32=readBuffer s where_ 32:=(Open.outside_read left_.mem (by decide) (by decide) _ _ size
        (Or.inr (by change rowBuf+32≤where_;omega))).trans (readU _ lo size)
  have gR:=area (2*p+1) (by omega)
  obtain ⟨w,k,kl,right_⟩:=fill_child o v true p small b slot left_.pc ((vk _ (Or.inl (by decide))).trans pos)
    ((vk _ (Or.inl (by decide))).trans row) ((vk _ (Or.inr (Or.inr rfl))).trans right) ((readV _ sa.1 sa.2).trans read)
    (fun val prev=>(readV _ gR.1 gR.2).trans (bVal val prev))
  have wk (q : Reg) (h : q∈capRegs ∨ q=.x4 ∨ q=.x28) : w.getReg q=s.getReg q:=(right_.keep q (side_keeps q h).1 (side_keeps q h).2).trans (vk q h)
  have cells:=put_cell (put_cell (blank_cells u erase.zero) 0 (by decide) _ left_.data left_.mem) 1 (by decide) _ right_.data right_.mem
  have filled : readBuffer w rowBuf 96=Late.parentBlock (a.getD slot) (b.getD slot):=pair_cells w _ _ cells
  have limits:=outside_pair p small
  obtain ⟨t,n,lim,hash,ep,out,kept,wr⟩:=pair_hash o w false (nodeAt 0 p) _ _ right_.pc ((wk _ (Or.inl (by decide))).trans row)
    ((wk _ (Or.inr (Or.inl rfl))).trans dst) ((wk _ (Or.inl (by decide))).trans scratch) limits.2.2 (limits.2.1.trans (by decide)) filled
  have fr : ChainOutside s w (nodeAt 0 p):=((ChainOutside.inside erase.outside (by decide) (by decide)).trans
    (ChainOutside.inside left_.mem (by decide) (by decide))).trans (ChainOutside.inside right_.mem (by decide) (by decide))
  refine ⟨t,12+m+k+n,by omega,⟨?_,ep,out.trans (hit_model _ _ _ _ hit).symm,fun q h=>(kept q h).trans (wk q (Or.inl h)),fr.trans wr⟩⟩
  rw [pairCalls,if_pos hit];exact ((erase.run.trans left_.run).trans right_.run).trans hash
end CommitGolfCandidate.S5Machine.Check
