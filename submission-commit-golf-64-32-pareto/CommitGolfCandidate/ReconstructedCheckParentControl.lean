import CommitGolfCandidate.ReconstructedCheckParentHeap

namespace CommitGolfCandidate.Reconstruction.CheckParentControl
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CheckRecorded CommitBlocks CheckCapArith CheckGroupRadix CheckGroupControl CheckParentHeap
set_option maxRecDepth 14000
set_option maxHeartbeats 1150000

def here (p stop : Nat):=if p<stop then 610 else 629

structure Local (s : MachineState) (e size p : Nat) : Prop where
  depth : s.getReg .x9=W e
  child : s.getReg .x18=W (base (2*p))
  active : s.getReg .x19=CheckCapScanData.flag p
  limit : s.getReg .x20=W (4*size)
  dest : s.getReg .x22=W (base p)
  ordinal : s.getReg .x25=W (2*p)

structure Context (s : MachineState) (cursor : Word) : Prop where
  one : s.getReg .x1=65
  sp : s.getReg .x2=W CheckLayout.sp
  fp : s.getReg .x8=W CheckLayout.fp
  heap : s.getReg .x23=W cap
  bits : s.getReg .x24=cursor
  scratch : s.getReg .x29=W CheckCapScanData.scratch

def prep : List Line := [(.x9,.op (.addi .x9 4095)),(.x11,.op (.slli .x11 5)),(.x18,.op (.add .x11 .x23)),
  (.x10,.op (.slli .x10 5)),(.x22,.op (.add .x10 .x23))]

theorem geBranch (o : Oracle) (s : MachineState) (pc dest : Nat) (off : BitVec 13) (i j : Nat)
    (small : pc<796) (pos : s.pc=addr pc) (word : CheckStraight.actualAt pc=some (.base (.BGEU .x25 .x20 off)))
    (target : addr pc+signExtend13 off=addr dest) (ii : s.getReg .x25=W i) (jj : s.getReg .x20=W j)
    (bi : i<2^64) (bj : j<2^64) :
    Segment o 1 s (s.setPC (addr (if i<j then pc+1 else dest))) [] := by
  have br:=CheckBranch.event o s pc dest .ge .x25 .x20 off small pos word target
  change Segment o 1 s (s.setPC (if !(s.getReg .x25).ult (s.getReg .x20) then addr dest else addr (pc+1))) [] at br
  rw [ii,jj,BitVec.ult_eq_decide] at br
  simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt bi,Nat.mod_eq_of_lt bj] at br
  split <;> simp_all

private theorem minus1 (e : Nat) : W (e+1)+signExtend12 4095=W e := by
  rw [show W (e+1)=W e+W 1 from BitVec.ofNat_add ..,BitVec.add_assoc,show W 1+signExtend12 4095=0#64 by decide,BitVec.add_zero]

private theorem ptr (p : Nat) : (W p <<< (5 : Nat))+W cap = W (base p) := by
  rw [CheckGroupRadix.shift,←BitVec.ofNat_add]
  change W (p*32+4194304)=W (4194304+32*p);congr 1;omega

theorem enter (o : Oracle) (s : MachineState) (e size : Nat) (c : Word) (pc : s.pc=addr 598) (spos : 0<size)
    (bound : size≤256) (depth : s.getReg .x9=W (e+1)) (parentId : s.getReg .x10=W size)
    (childId : s.getReg .x11=W (2*size)) (active : s.getReg .x19=CheckCapScanData.flag size)
    (limit : s.getReg .x20=W (4*size)) (ordinal : s.getReg .x25=W (2*size)) (ctx : Context s c) :
    ∃ t,Segment o 7 s t [] ∧ t.pc=addr 610 ∧ Local t e size size ∧ Context t c ∧ t.mem=s.mem ∧
      Kept [.x9,.x10,.x11,.x18,.x22] s t := by
  have b:=geBranch o s 598 423 7492 (2*size) (4*size) (by decide) pc rfl (by decide) ordinal limit (by omega) (by omega)
  rw [ite_eq_left (by omega : 2*size<4*size)] at b
  let u:=s.setPC (addr 599)
  let v:=effect u prep
  have arithmetic:=CheckCapArith.positive o u 599 prep rfl (by decide)
  have jump:=CheckBranch.jump o v 604 610 24 (by decide) (CheckCapArith.location u 599 prep rfl) rfl (by decide)
  let t:=v.setPC (addr 610)
  have shared : Kept [.x9,.x10,.x11,.x18,.x22] s t := by
    intro r hv;apply outside u prep r;simpa [prep,and_comm,and_left_comm,and_assoc] using hv
  have context : Context t c:=⟨(shared _ (by decide)).trans ctx.one,(shared _ (by decide)).trans ctx.sp,
    (shared _ (by decide)).trans ctx.fp,(shared _ (by decide)).trans ctx.heap,(shared _ (by decide)).trans ctx.bits,
    (shared _ (by decide)).trans ctx.scratch⟩
  refine ⟨t,compose (compose b arithmetic) jump,rfl,⟨?_,?_,(shared _ (by decide)).trans active,(shared _ (by decide)).trans limit,
    ?_,(shared _ (by decide)).trans ordinal⟩,context,memory u prep,shared⟩
  · change v.getReg .x9=_;rw [register];change s.getReg .x9+signExtend12 4095=_;rw [depth,minus1]
  · change v.getReg .x18=_;rw [register];change ((s.getReg .x11) <<< (5 : Nat))+s.getReg .x23=_;rw [childId,ctx.heap,ptr]
  · change v.getReg .x22=_;rw [register];change ((s.getReg .x10) <<< (5 : Nat))+s.getReg .x23=_;rw [parentId,ctx.heap,ptr]

def inc : List Line := [(.x25,.addiw .x25 2),(.x18,.op (.addi .x18 64)),(.x22,.op (.addi .x22 32)),(.x19,.op (.addi .x19 1))]

private theorem plus2 (i : Fin 1025) : ((W i.val).truncate 32+(signExtend12 2).truncate 32).signExtend 64=W (i.val+2) :=
  (by decide +kernel : ∀ k : Fin 1025,((W k.val).truncate 32+(signExtend12 2).truncate 32).signExtend 64=W (k.val+2)) i

theorem advance (o : Oracle) (s : MachineState) (e size p : Nat) (c : Word) (pc : s.pc=addr 605) (bound : size≤256)
    (small : p<2*size) (state : Local s e size p) (ctx : Context s c) :
    ∃ t,Segment o 5 s t [] ∧ t.pc=addr (here (p+1) (2*size)) ∧ Local t e size (p+1) ∧ Context t c ∧
      t.mem=s.mem ∧ Kept [.x25,.x18,.x22,.x19] s t := by
  let u:=effect s inc
  have arithmetic:=CheckCapArith.positive o s 605 inc pc (by decide)
  have shared (r : Reg) (h : r∉[Reg.x25,.x18,.x22,.x19]) : u.getReg r=s.getReg r:=outside s inc r h
  have ord : u.getReg .x25=W (2*(p+1)):=by
    rw [register];change ((s.getReg .x25).truncate 32+(signExtend12 2).truncate 32).signExtend 64=_
    rw [state.ordinal,plus2 ⟨2*p,by omega⟩,show 2*p+2=2*(p+1) by omega]
  have lim:=(shared .x20 (by decide)).trans state.limit
  have b:=geBranch o u 609 629 80 _ _ (by decide) (CheckCapArith.location s 605 inc pc) rfl (by decide) ord lim (by omega) (by omega)
  have point : (if 2*(p+1)<4*size then 609+1 else 629)=here (p+1) (2*size) := by
    unfold here;split <;> split <;> first | rfl | omega
  rw [point] at b
  let t:=u.setPC (addr (here (p+1) (2*size)))
  refine ⟨t,compose arithmetic b,rfl,⟨(shared _ (by decide)).trans state.depth,?_,?_,lim,?_,ord⟩,
    ⟨(shared _ (by decide)).trans ctx.one,(shared _ (by decide)).trans ctx.sp,(shared _ (by decide)).trans ctx.fp,
      (shared _ (by decide)).trans ctx.heap,(shared _ (by decide)).trans ctx.bits,(shared _ (by decide)).trans ctx.scratch⟩,
    memory s inc,shared⟩
  · change u.getReg .x18=_;rw [register];change s.getReg .x18+W 64=_
    rw [state.child,←BitVec.ofNat_add];congr 1
  · change u.getReg .x19=_;rw [register];change s.getReg .x19+W 1=_
    rw [state.active];unfold CheckCapScanData.flag;rw [←BitVec.ofNat_add];congr 1
  · change u.getReg .x22=_;rw [register];change s.getReg .x22+W 32=_
    rw [state.dest,←BitVec.ofNat_add,←next]

end CommitGolfCandidate.Reconstruction.CheckParentControl

