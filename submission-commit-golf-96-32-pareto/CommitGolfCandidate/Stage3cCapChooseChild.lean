import CommitGolfCandidate.Stage3cCapPairHead
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W Outside)
def sidePC (r : Bool):=if r then 875 else 858
def slotArmPC (r : Bool):=if r then 882 else 864
def copyPC (r : Bool):=if r then 885 else 867
def sideIndex (right : Bool) (p : Nat):=2*p+right.toNat
def sideReg (r : Bool):=if r then Reg.x28 else .x7
def pickOps (right present : Bool) : List Sym.Calc:=
  if present then [.lui .x6 17,.addi .x6 .x6 2048,.slli .x29 .x23 6,.add .x6 .x6 .x29]++
    (if right then [.addi .x6 .x6 32] else [])
  else [.lui .x6 21,.slli .x29 .x23 5,.add .x6 .x6 .x29]
def pickPC (right present : Bool):=if present then sidePC right+1 else slotArmPC right
def childCopy (right : Bool) : CopySpec:=⟨.x29,.x6,.x25,0,32*right.toNat⟩
private theorem choices : ∀ r b : Bool,Sym.Listed (pickOps r b) (pickPC r b) ∧
    BranchSite (sidePC r) (slotArmPC r) .eq (sideReg r) .x0 ∧ CopySites (childCopy r) (copyPC r) 4 ∧
    (if b then JumpSite (pickPC r b+(pickOps r b).length) (copyPC r) .x0 else pickPC r b+(pickOps r b).length=copyPC r) ∧ (pickOps r b).length≤5 := by
  unfold CopySites;decide +kernel
private theorem pick_addr (s : MachineState) (r b : Bool) (p : Nat) (ctr : s.getReg .x23=W p) :
    (((pickOps r b).foldl Sym.bump Sym.original) .x6).eval s=W (if b then bucketAddress (sideIndex r p) else slotAddr p) := by
  cases b
  · cases r <;> change W slotBase+(s.getReg .x23 <<< 5)=_ <;> rw [ctr] <;> unfold W <;> rw [Open.shifted,←BitVec.ofNat_add] <;>
      apply congrArg (BitVec.ofNat 64) <;> dsimp [slotAddr] <;> omega
  · cases r
    · change W compBase+(s.getReg .x23 <<< 6)=_;rw [ctr];unfold W;rw [Open.shifted,←BitVec.ofNat_add]
      apply congrArg (BitVec.ofNat 64);dsimp [bucketAddress,sideIndex];omega
    · change W compBase+(s.getReg .x23 <<< 6)+32#64=_;rw [ctr];unfold W;rw [Open.shifted,←BitVec.ofNat_add,←BitVec.ofNat_add]
      apply congrArg (BitVec.ofNat 64);dsimp [bucketAddress,sideIndex];omega
private theorem pick_keeps (s : MachineState) (r b : Bool) (q : Reg) (q6 : q≠.x6) (q29 : q≠.x29) :
    (((pickOps r b).foldl Sym.bump Sym.original) q).eval s=s.getReg q := by cases r <;> cases b <;> cases q <;> first | contradiction | rfl

attribute [local irreducible] Sym.evaluated readBuffer
set_option maxRecDepth 8000 in
private theorem reach_copy (o : Oracle) (s : MachineState) (r present : Bool) (p : Nat) (pc : s.pc=pcAt (sidePC r))
    (ctr : s.getReg .x23=W p) (test : Rel.eq.test (s.getReg (sideReg r)) (s.getReg .x0)= !present) :
    ∃ t n,n≤7 ∧ Flow o s t n 0 ∧ t.pc=pcAt (copyPC r) ∧ t.getReg .x6=W (if present then bucketAddress (sideIndex r p) else slotAddr p)
      ∧ t.mem=s.mem ∧ ∀ q,q≠.x6→q≠.x29→t.getReg q=s.getReg q := by
  obtain ⟨code,cond,_,end_,price⟩:=choices r present
  have head:=branch o s (sidePC r) (slotArmPC r) .eq (sideReg r) .x0 cond pc _ test
  let u:=s.setPC (pcAt (pickPC r present))
  have landing : (if !present then slotArmPC r else sidePC r+1)=pickPC r present:=by cases present <;> rfl
  rw [landing] at head
  obtain ⟨arg,regs,mem,ip⟩:=Sym.compiled o _ _ u rfl code (by cases r <;> cases present <;> change ∀ e∈([] : List (Sym.Expr×Nat)),_ <;> simp)
  let v:=Sym.evaluated (pickOps r present) u
  have dst:=(regs .x6).trans (pick_addr u r present p ctr)
  have k (q : Reg) (a : q≠.x6) (b : q≠.x29):v.getReg q=s.getReg q:=(regs q).trans ((pick_keeps u r present q a b).trans MachineState.getReg_setPC)
  cases present
  · exact ⟨v,1+(pickOps r false).length,by omega,head.trans arg,ip.trans (congrArg pcAt end_),dst,mem,k⟩
  · have leap:=jump o v _ _ .x0 end_ ip
    exact ⟨_,1+(pickOps r true).length+1,by omega,(head.trans arg).trans leap,rfl,MachineState.getReg_setPC.trans dst,mem,fun q a b=>MachineState.getReg_setPC.trans (k q a b)⟩

structure FilledChild (o : Oracle) (s t : MachineState) (right : Bool) (v : Late.Digest) (steps : Nat) : Prop where
  run : Flow o s t steps 0
  pc : t.pc=pcAt (copyPC right+8)
  data : readBuffer t (rowCell right.toNat) 32=v
  mem : Outside s t (rowCell right.toNat) 32
  keep : ∀ q,q≠.x6→q≠.x29→t.getReg q=s.getReg q
theorem fill_child (o : Oracle) (s : MachineState) (right : Bool) (p : Nat) (inside : p<256) (prev : Option Late.Digest)
    (fallback : Late.Digest) (pc : s.pc=pcAt (sidePC right)) (ctr : s.getReg .x23=W p) (row : s.getReg .x25=W rowBuf)
    (flag : s.getReg (sideReg right)=markedWord prev) (slot : readBuffer s (slotAddr p) 32=fallback)
    (computed : ∀ a,prev=some a → readBuffer s (bucketAddress (sideIndex right p)) 32=a) :
    ∃ t n,n≤15 ∧ FilledChild o s t right (prev.getD fallback) n := by
  have test : Rel.eq.test (s.getReg (sideReg right)) (s.getReg .x0)= !prev.isSome:=by
    change (s.getReg (sideReg right)==0#64)=_;rw [flag];cases prev <;> rfl
  obtain ⟨u,a,lim,head,ep,from_,mem,keep⟩:=reach_copy o s right prev.isSome p pc ctr test
  let src:=if prev.isSome then bucketAddress (sideIndex right p) else slotAddr p
  have bounds : src%8=0 ∧ src+32≤MEMORY_BYTES ∧ rowCell right.toNat+32≤src:=by
    dsimp [src];split <;> cases right <;> dsimp [bucketAddress,sideIndex,slotAddr,slotBase,rowCell,rowBuf,compBase,MEMORY_BYTES] <;> omega
  have al : rowCell right.toNat%8=0:=by cases right <;> decide
  have da : rowCell right.toNat+32≤MEMORY_BYTES:=by cases right <;> decide
  have actual : readBuffer s src 32=prev.getD fallback:=by
    dsimp only [src];cases prev with
    | none=>exact slot
    | some v=>exact computed v rfl
  obtain ⟨t,done_⟩:=copy_words o u (copyPC right) src rowBuf 4 (childCopy right) (choices right false).2.2.1
    (by cases right <;> decide) (by cases right <;> decide) ep from_ ((keep .x25 (by decide) (by decide)).trans row)
    ⟨bounds.1,bounds.2.1⟩ ⟨al,da⟩ (Or.inr bounds.2.2)
  refine ⟨t,a+8,by omega,⟨head.trans done_.run,done_.pc,(copied_read (a:=src) (b:=rowCell right.toNat) (n:=4) done_.data bounds.1 al).trans
    ((read_buffer_memory_congr u s mem _ _).trans actual),fun q h aq outside=>(done_.data.outside q h aq outside).trans (congrFun mem _),?_⟩⟩
  intro q a b;exact (done_.keep q b).trans (keep q a b)
end CommitGolfCandidate.Chained.BinaryMachine.Check
