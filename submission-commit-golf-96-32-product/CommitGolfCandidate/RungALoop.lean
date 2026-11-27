import CommitGolfCandidate.RungACommitGroup
import CommitGolfCandidate.RungAHead
namespace CommitGolfCandidate.RungA.Kernel
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 R4 Late
set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 1400000
attribute [local irreducible] readBuffer DetRun execute
theorem State.move {o m r g s t} (p : State o m r g s) (mem : t.mem=s.mem)
    (keep : ∀ q,q≠.x22 → t.getReg q=s.getReg q) : State o m r g t := by
  have same (a n : Nat) := readBuffer_of_mem_eq mem a n
  exact ⟨⟨(keep _ (by decide)).trans p.env.mode,(keep _ (by decide)).trans p.env.kind,
    (keep _ (by decide)).trans p.env.width,(keep _ (by decide)).trans p.env.root⟩,
    (keep _ (by decide)).trans p.src,(keep _ (by decide)).trans p.stride,(keep _ (by decide)).trans p.stop,
    p.ground.kept (fun a n _ _ _=>same a n) (fun h j k z=>(same _ _).trans (p.ground.gaps h j k z)),
    fun j b x=>(same _ _).trans (p.blank j b x),fun j b=>(same _ _).trans (p.roots j b)⟩

theorem geometryOff (b k : Nat) (even : b%2=0) :
    nodeAddress 4 b+off k=nodeAddress 4 (b+k) := by
  dsimp [nodeAddress,Late.gapOffset,off]
  omega

private theorem insideOff (k : Nat) (fit : k<8) : off k<2048:=by dsimp [off];omega

theorem groups (o : Oracle) (m : Message) (r : Tape) (s : MachineState) (base n span : Nat)
    (even : base%2=0) (size : base+span≤699050) (len : span≤8)
    (enc : ∀ j,j<span → listed (n+114*j) (code full (off j)) ∧ hasOp (n+114*j+113) (.ADD .x21 .x21 .x25))
    (start : State o m r base s) (pc : s.pc=pcAt n) (dst : s.getReg .x22=Z (nodeAddress 4 base))
    (k : Nat) (fit : k≤span) :
    ∃ t,MRun o s (114*k) t (387*k) (39*k) ∧ t.pc=pcAt (n+114*k) ∧
      State o m r (base+k) t ∧ t.getReg .x22=Z (nodeAddress 4 base) := by
  induction k with
  | zero=>exact ⟨s,DetRun.refl o (R4.submission.image .commit) s,by simpa using pc,by simpa using start,dst⟩
  | succ k ih=>
    obtain ⟨u,run,ip,live,ptr⟩:=ih (by omega)
    let c : Layout:=⟨base+k,24,nodeAddress 4 base,off k,by omega,le_rfl,insideOff _ (by omega),geometryOff _ _ even⟩
    have limit : c.limit=min 24 (16777216-24*c.group):=by dsimp [c];omega
    obtain ⟨sites,add⟩:=enc k (by omega)
    obtain ⟨t,end_,pc',st,dt⟩:=group o m r c u _ true limit rfl live ip ptr sites (hasOp_sound add)
    refine ⟨t,?_,?_,st,dt⟩
    · rw [Nat.mul_succ,Nat.mul_succ,Nat.mul_succ];exact run.trans end_
    · change t.pc=pcAt (n+114*k+114) at pc';rw [Nat.mul_succ,←Nat.add_assoc];exact pc'

def tilePC (b : Nat) := if b<87381 then 131140 else 132054
private theorem latchOps : hasOp 132052 (.ADDI .x22 .x22 384)=true ∧
    hasOp 132053 (.BNE .x22 .x20 4540)=true := by decide +kernel

theorem latch (o : Oracle) (m : Message) (r : Tape) (s : MachineState) (b : Nat) (size : b<87381)
    (live : State o m r (8*b+8) s) (pc : s.pc=pcAt 132052) (ptr : s.getReg .x22=Z (nodeAddress 4 (8*b))) :
    ∃ t,MRun o s 2 t 2 0 ∧ t.pc=pcAt (tilePC (b+1)) ∧ State o m r (8*(b+1)) t ∧
      t.getReg .x22=Z (nodeAddress 4 (8*(b+1))) := by
  let next:=nodeAddress 4 (8*(b+1))
  have layerFour : levelOffset 4=1006633152:=by decide
  have val : s.getReg .x22+signExtend12 384=Z next:=by
    rw [ptr]
    apply (add_signExtend12_ofNat_small (nodeAddress 4 (8*b)) 384 (by decide)).trans
    apply congrArg Z;dsimp [nodeAddress,Late.gapOffset,next];omega
  obtain ⟨u,first,ip,mem,dx,st⟩:=setPointer o s 132052 .x22 .x22 _ _ (by decide) (hasOp_sound latchOps.1) pc val
  have ux:= (st _ (by decide)).trans live.stop
  let op:=Instr.BNE .x22 .x20 4540
  let t:=execInstrBr u op
  have go : MRun o u 1 t 1 0:=DetRun.step1 (hasOp_sound latchOps.2 u ip) rfl
  have it : t.pc=pcAt (tilePC (b+1)) := by
    have bound : next<2^64 :=by dsimp [next,nodeAddress,Late.gapOffset];omega
    by_cases more : b+1<87381
    · have ne : Z next≠Z (nodeAddress 4 699048):=by
        intro eq;have same:=congrArg BitVec.toNat eq
        rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt bound] at same
        change next=5335158880 at same
        dsimp [next,nodeAddress,Late.gapOffset] at same;omega
      simp [t,op,execInstrBr,dx,ux,ne,ip,tilePC,more,pcAt,signExtend13] <;> rfl
    · have last : b+1=87381:=by omega
      have eq : next=nodeAddress 4 699048:=by dsimp [next];rw [last]
      simp [t,op,execInstrBr,dx,ux,eq,ip,tilePC,more,pcAt] <;> rfl
  have state:=live.move mem (fun q h=>st q h.symm)
  rw [Nat.mul_succ]
  exact ⟨t,first.trans go,it,state.move (mem_exec_BNE ..) (fun q _=>reg_exec_BNE u .x22 .x20 4540 q),(reg_exec_BNE ..).trans dx⟩

theorem bulk (o : Oracle) (m : Message) (r : Tape) (s : MachineState) (start : State o m r 0 s)
    (pc : s.pc=pcAt 131140) (dst : s.getReg .x22=Z (nodeAddress 4 0)) (b : Nat) (limit : b≤87381) :
    ∃ t,MRun o s (914*b) t (3098*b) (312*b) ∧ t.pc=pcAt (tilePC b) ∧
      State o m r (8*b) t ∧ t.getReg .x22=Z (nodeAddress 4 (8*b)) := by
  induction b with
  | zero=>exact ⟨s,DetRun.refl o (R4.submission.image .commit) s,pc,start,dst⟩
  | succ b ih=>
    obtain ⟨u,pre,ip,live,ptr⟩:=ih (by omega);rw [tilePC,if_pos (by omega : b<87381)] at ip
    obtain ⟨z,inner,zpc,after,pz⟩:=groups o m r u (8*b) 131140 8 (by omega) (by omega) le_rfl
      (fun j hj=>sitesFull ⟨j,hj⟩) live ip ptr 8 le_rfl
    obtain ⟨t,br,ep,final_,pt⟩:=latch o m r z b (by omega) after zpc pz
    refine ⟨t,?_,ep,final_,pt⟩
    have run:=(pre.trans inner).trans br
    rw [Nat.mul_succ,Nat.mul_succ,Nat.mul_succ];simpa only [Nat.add_assoc] using run
end CommitGolfCandidate.RungA.Kernel
