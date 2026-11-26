import CommitGolfCandidate.ReconstructedCheckPair
import CommitGolfCandidate.ReconstructedCheckRegion

namespace CommitGolfCandidate.Reconstruction.CheckPairPhysical
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding Binding.Machine CheckValues CheckRecorded CheckParentRun CheckParentWords CheckParentGeometry
set_option maxRecDepth 15000
set_option maxHeartbeats 1200000
attribute [local irreducible] readBuffer

def child (s : MachineState) (get : Fin 4→Reg) (x : Binding.Digest) := ∀ i, s.getReg (get i)=digWord x i

private theorem cell_words (s : MachineState) (a : Nat) (x : Binding.Digest) (align : a%8=0)
    (val : ∀ i : Fin 4,s.getMem (BitVec.ofNat 64 (a+8*i.val))=digWord x i) : CommitParents.cell s a=x := by
  have read:=CheckParentCall.read_words_eq s a 4 (pack x) align (fun i hi=>val ⟨i,hi⟩)
  change (readBuffer s a 32).cast _ =pack x at read
  rw [BitVec.cast_eq] at read;exact (congrArg unpack read).trans (Binding.unpack_pack x)

structure Called (s : MachineState) (g : Geometry) (d : Fin 24) (side : Bool) : Prop where
  pc : s.pc=CommitBlocks.addr 248
  fp : s.getReg .x8=BitVec.ofNat 64 (g.pair+2360)
  sp : s.getReg .x2=BitVec.ofNat 64 (g.stack+144)
  branch : s.getReg .x15=(if side then 1 else 0)
  depth : s.getReg .x21=BitVec.ofNat 64 d.val
  output : g.pair+2048=g.out

def sides (side : Bool) (cur sib : Binding.Digest) :=
  (if side then sib else cur,if side then cur else sib)

def log (o : Oracle) (d : Nat) (side : Bool) (cur sib : Binding.Digest) :=
  let pair:=sides side cur sib
  CheckParentExecution.rows o (pairKey (d+1) pair.1 pair.2) 0 (work d)

private theorem ro_bounds (a : Nat) (w : Word) (registered : CheckParentRun.ro a=some w) :
    2097560≤a ∧ a<2098152 := by
  unfold CheckParentRun.ro at registered
  split_ifs at registered <;> first | contradiction | omega

attribute [local irreducible] CheckParentRun.ro

private theorem table_preserved (s t : MachineState) (g : Geometry) (placed : Placed g) (h : constants s)
    (keep : ∀ a, (∀ i : Fin 8, a≠BitVec.ofNat 64 (g.pair+8*i.val))→t.getMem a=s.getMem a) : constants t := by
  intro a w al ro
  rw [keep];exact h a w al ro
  intro i same
  have bounds:=ro_bounds a w ro
  have apart:=placed.apart 0 2 (by decide)
  simp only [Fin.val_zero,show ((2 : Fin 4) : Nat)=2 by rfl,base,CheckParentGeometry.hi,lo,Nat.zero_add,Nat.add_zero] at apart
  have room : g.pair+64≤MEMORY_BYTES := placed.room 2
  unfold MEMORY_BYTES at room
  have eq:=congrArg BitVec.toNat same;have lim:=i.isLt
  simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega :a<2^64),
    Nat.mod_eq_of_lt (by omega :g.pair+8*i.val<2^64)] at eq
  omega

def carried : List Reg := [.x3,.x4,.x9,.x18,.x19,.x20,.x21,.x22,.x24,.x25,.x27]

private theorem keep : ∀ b : Bool,
    (CheckPair.done b).get .x26=.bin .add (.reg .x26) (.lit (-1)) ∧
    ∀ r∈carried,(CheckPair.done b).get r=(CheckPair.start b).get r ∧ r∈CheckParentPlan.preserved := by decide +kernel

theorem complete (o : Oracle) (s : MachineState) (g : Geometry) (placed : Placed g) (d : Fin 24) (side : Bool)
    (call : Called s g d side) (ro : constants s) (cur sib : Binding.Digest)
    (current : child s CheckPair.current cur) (sibling : child s CheckPair.sibling sib) :
    ∃ t, Segment o (23+CheckParent.Cost d) s t (log o d side cur sib) ∧
      t.pc=CommitBlocks.addr 271 ∧ CommitParents.cell t g.out=
        parent (oracleCompression o) d (sides side cur sib).1 (sides side cur sib).2 ∧
      t.getReg .x23=s.getReg .x23 >>> (1 : Nat) ∧ t.getReg .x8=s.getReg .x8 ∧
      (∀ p, (∀ i : Fin 8,p≠BitVec.ofNat 64 (g.pair+8*i.val)) →
        (∀ i : Fin 18,p≠BitVec.ofNat 64 (g.stack+8*i.val)) →
        (∀ i : Fin 4,p≠BitVec.ofNat 64 (g.out+8*i.val)) → t.getMem p=s.getMem p) ∧
      t.getReg .x2=s.getReg .x2 ∧ t.getReg .x26=s.getReg .x26+(-1) ∧
      (∀ v∈carried,t.getReg v=s.getReg v) := by
  let e:=CheckRegion.env s g.pair
  have owner : Layout e CheckPair.table := CheckRegion.layout s g.pair 64 (placed.align 2) (by decide) (placed.room 2)
  have init : Matches e (CheckPair.start side) s := by
    refine ⟨call.pc,?_,fun _=>rfl⟩;intro r;cases r <;> try rfl
    · change s.getReg .x8=physical (CheckRegion.env s g.pair) (loc 1 2360)
      rw [CheckRegion.point];exact call.fp
    · exact call.branch
  obtain ⟨u,before,hm,safe,pc,ra,sp,fp,out,depth,pair,route,lw,rw₁⟩:=CheckPair.positive o e owner side s init
  have preserve (p : Word) (fresh : ∀ i : Fin 8,p≠BitVec.ofNat 64 (g.pair+8*i.val)) : u.getMem p=s.getMem p := by
    rw [hm.mem];apply CheckRegion.frame _ _ 64 _ safe;intro j bound;exact fresh ⟨j,by omega⟩
  have regs : CheckParent.Called u d g := by
    refine ⟨hm.pc.trans pc,?_,?_,?_,?_⟩
    · rw [hm.regs,sp];exact call.sp
    · rw [hm.regs,out];change physical (CheckRegion.env s g.pair) (loc 1 2048)=_
      rw [CheckRegion.point,call.output]
    · rw [hm.regs,depth];exact call.depth
    · rw [hm.regs,pair];change physical (CheckRegion.env s g.pair) (loc 1 0)=_
      rw [CheckRegion.point,Nat.add_zero]
  have mem (n : Nat) (valid : CheckPair.table.allowed (loc 1 n)=true) (r : Reg)
      (v : look CheckPair.table (loc 1 n) (CheckPair.done side).writes=.reg r) :
      u.getMem (BitVec.ofNat 64 (g.pair+n))=s.getReg r := by
    have x:=look_sound e CheckPair.table owner _ (loc 1 n) valid safe
    rw [v,←hm.mem] at x;change s.getReg r=u.getMem (physical (CheckRegion.env s g.pair) (loc 1 n)) at x
    rw [CheckRegion.point] at x;exact x.symm
  have slots : ∀ i : Fin 4,CheckPair.table.allowed (loc 1 (8*i.val))=true ∧ CheckPair.table.allowed (loc 1 (32+8*i.val))=true := by decide
  have left : CommitParents.cell u g.pair=(sides side cur sib).1 := by
    apply cell_words u g.pair _ (placed.align 2);intro i;rw [mem _ (slots i).1 _ (lw i)]
    cases side <;> first | exact current i | exact sibling i
  have right : CommitParents.cell u (g.pair+32)=(sides side cur sib).2 := by
    apply cell_words _ _ _ (by have al : g.pair%8=0:=placed.align 2;omega);intro i
    rw [Nat.add_assoc,mem _ (slots i).2 _ (rw₁ i)]
    cases side <;> first | exact current i | exact sibling i
  obtain ⟨t,par,post⟩:=CheckParent.positive o g placed u d regs (table_preserved s u g placed ro preserve) _ _ left right
  refine ⟨t,by simpa only [log,List.nil_append] using compose before par,?_,post.output,?_,?_,?_,?_,?_,?_⟩
  · rw [post.returnPC,hm.regs,ra];exact (by decide : ((CommitBlocks.addr 271 + signExtend12 0) &&& ~~~1#64)=CommitBlocks.addr 271)
  · rw [post.calleeSaved .x23 (by decide),hm.regs,route];rfl
  · rw [post.framePointer,hm.regs,fp];change physical (CheckRegion.env s g.pair) (loc 1 2360)=_
    rw [CheckRegion.point];exact call.fp.symm
  · intro p a b c;exact (post.memory p b c).trans (preserve p a)
  · rw [post.stack,hm.regs,sp];rfl
  · rw [post.calleeSaved .x26 (by decide),hm.regs,(keep side).1];rfl
  · intro v hv;obtain ⟨unchanged,registered⟩:=(keep side).2 v hv
    rw [post.calleeSaved v registered,hm.regs,unchanged,←init.regs]

theorem positive (o : Oracle) (s : MachineState) (g : Geometry) (placed : Placed g) (d : Fin 24) (side : Bool)
    (call : Called s g d side) (ro : constants s) (cur sib : Binding.Digest)
    (current : child s CheckPair.current cur) (sibling : child s CheckPair.sibling sib) :
    ∃ t, Segment o (23+CheckParent.Cost d) s t (log o d side cur sib) ∧
      t.pc=CommitBlocks.addr 271 ∧ CommitParents.cell t g.out=
        parent (oracleCompression o) d (sides side cur sib).1 (sides side cur sib).2 ∧
      t.getReg .x23=s.getReg .x23 >>> (1 : Nat) ∧ t.getReg .x8=s.getReg .x8 ∧
      (∀ p, (∀ i : Fin 8,p≠BitVec.ofNat 64 (g.pair+8*i.val)) →
        (∀ i : Fin 18,p≠BitVec.ofNat 64 (g.stack+8*i.val)) →
        (∀ i : Fin 4,p≠BitVec.ofNat 64 (g.out+8*i.val)) → t.getMem p=s.getMem p) := by
  obtain ⟨t,sg,pc,value,route,fp,frame,_⟩:=complete o s g placed d side call ro cur sib current sibling
  exact ⟨t,sg,pc,value,route,fp,frame⟩

end CommitGolfCandidate.Reconstruction.CheckPairPhysical
