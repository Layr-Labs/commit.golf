import CommitGolfCandidate.Stage3cBucketState
import CommitGolfCandidate.Stage3cReadField
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W Outside)
def slotAddr (j : Nat):=slotBase+32*j
def slotBit (j : Nat):=483840+230*j
def slotPC (j : Nat):=if j<256 then 805 else 811
def slotOps : List Sym.Calc:=[.slli .x6 .x23 5,.add .x10 .x14 .x6,.addi .x11 .x0 230]
def slotRegs : List Reg:=[.x8,.x14,.x15,.x23,.x25,.x26]
def SlotPrefix (x : CheckInput) (s : MachineState) (n : Nat) := ∀ j<n,readBuffer s (slotAddr j) 32=(view true x).slot j
structure CapEnv (x : CheckInput) (s : MachineState) : Prop where
  root : s.getReg .x8=W rootBase
  row : s.getReg .x25=W rowBuf
  chain : s.getReg .x26=W chainBuf
  read : readBuffer s rootBase 32=x.commitment
structure SlotState (H : Compression) (x : CheckInput) (p : Nat) (s : MachineState) : Prop where
  pc : s.pc=pcAt (slotPC p)
  counter : s.getReg .x23=W p
  slots : s.getReg .x14=W slotBase
  limit : s.getReg .x15=W 256
  env : CapEnv x s
  cursor : ∃ k<8,Reader.Cursor s proofBase 67840 (Pw.packedInput x) (slotBit p) k
  previous : SlotPrefix x s p
  table : BucketTable H x 128 s
private theorem slot_wire (x : CheckInput) (p : Nat) :
    Reader.decoded (Pw.packedInput x) (slotBit p) 230=(view true x).slot p := by
  simp only [Reader.decoded,slotBit,Pw.batchView,view,ite_true,↓reduceIte]
private theorem slot_safe (q : Reg) (h : q∈slotRegs) : Reader.fieldKeep q ∧ q≠.x1 ∧ q∉([.x6,.x10,.x11] : List Reg) := by
  cases q <;> simp_all [slotRegs,Reader.fieldKeep,Reader.readKeep]
private theorem ops_keep (s : MachineState) (q : Reg) (h : q∉([.x6,.x10,.x11] : List Reg)) :
    ((slotOps.foldl Sym.bump Sym.original) q).eval s=s.getReg q:=by cases q <;> first | (exfalso;apply h;decide) | rfl

attribute [local irreducible] Pw.packedInput readBuffer Reader.window
theorem read_slot (o : Oracle) (x : CheckInput) (p : Nat) (s : MachineState) (state : SlotState o.compression x p s) (small : p<256) :
    ∃ t n,n≤440 ∧ Flow o s t n 0 ∧ t.pc=pcAt 809 ∧ (∃ k<8,Reader.Cursor t proofBase 67840 (Pw.packedInput x) (slotBit (p+1)) k) ∧
      readBuffer t (slotAddr p) 32=(view true x).slot p ∧ Outside s t (slotAddr p) 32 ∧
      ∀ q∈slotRegs,t.getReg q=s.getReg q := by
  let u:=Sym.evaluated slotOps s
  have ip : s.pc=pcAt 805:=state.pc.trans (congrArg pcAt (if_pos small))
  obtain ⟨args,regs,mem,up⟩:=Sym.compiled o slotOps 805 s ip (by decide +kernel)
    (by change ∀ e∈([] : List (Sym.Expr×Nat)),_;simp)
  have dst : u.getReg .x10=W (slotAddr p):=by
    apply (regs .x10).trans;change s.getReg .x14+(s.getReg .x23 <<< 5)=_;rw [state.slots,state.counter];unfold W
    rw [Open.shifted,←BitVec.ofNat_add];apply congrArg (BitVec.ofNat 64);dsimp [slotAddr];omega
  let z:=(u.setReg .x1 (pcAt 809)).setPC (pcAt 21)
  have call:=jump o u 808 21 .x1 (by decide +kernel) up
  have zk (q : Reg) (h : q≠.x1) : z.getReg q=u.getReg q:=MachineState.getReg_setPC.trans (MachineState.getReg_setReg_ne _ _ _ _ h.symm)
  have same (q : Reg) (a : q≠.x1) (b : q∉([.x6,.x10,.x11] : List Reg)) : z.getReg q=s.getReg q:=(zk _ a).trans ((regs q).trans (ops_keep s q b))
  obtain ⟨k,lim,c⟩:=state.cursor
  have cz:=c.same (t:=z) mem (same _ (by decide) (by decide)) (same _ (by decide) (by decide))
    (same _ (by decide) (by decide)) (same _ (by decide) (by decide))
  obtain ⟨t,n,buf,steps,rb,run,ep,ct,data,frame,keep⟩:=Reader.read_field o z proofBase 67840 _ (slotBit p) k 230 (slotAddr p) 809
    (by decide) (by decide) (by dsimp [slotBit];omega) (by dsimp [slotAddr,slotBase,proofBase];omega) (by dsimp [slotAddr,slotBase];omega)
    lim rfl rfl (by decide) ((zk _ (by decide)).trans (regs .x11)) ((zk _ (by decide)).trans dst) cz
  have moved : slotBit p+230=slotBit (p+1):=by dsimp [slotBit];omega
  refine ⟨t,4+n,by omega,(args.trans call).trans run,ep,⟨buf,rb,moved ▸ ct⟩,data.trans (slot_wire x p),?_,?_⟩
  · intro q h al sep;exact (frame q h al sep).trans (congrFun mem _)
  · intro q h;obtain ⟨a,b,c⟩:=slot_safe q h;exact (keep q a).trans (same q b c)

theorem BucketTable.slots_away {H x n s t} (table : BucketTable H x n s) (p : Nat) (small : p<256) (frame : Outside s t (slotAddr p) 32) :
    BucketTable H x n t := by
  have al : slotAddr p%8=0:=by dsimp [slotAddr,slotBase];omega
  refine ⟨?_,?_,?_⟩
  · intro j h;exact (Open.outside_byte frame al (by decide) (by dsimp [marksBuf,MEMORY_BYTES];omega)
      (Or.inl (by dsimp [slotAddr,marksBuf,slotBase];omega))).trans (table.mark j h)
  · intro j h v mem;exact (Open.outside_read frame al (by decide) (compBase+32*j) 32 (by dsimp [compBase,MEMORY_BYTES];omega)
      (Or.inl (by dsimp [slotAddr,compBase,slotBase];omega))).trans (table.data j h v mem)
  · intro j lo hi a;exact (frame j (by unfold saltBuf at hi;unfold MEMORY_BYTES;omega) a
      (Or.inr (by dsimp [slotAddr,slotBase];unfold capBase at lo;omega))).trans (table.blank j lo hi a)
end CommitGolfCandidate.Chained.BinaryMachine.Check
