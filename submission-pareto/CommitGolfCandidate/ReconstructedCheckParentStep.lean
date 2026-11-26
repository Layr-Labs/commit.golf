import CommitGolfCandidate.ReconstructedCheckParentControl
import CommitGolfCandidate.ReconstructedCheckParentCallCopy
import CommitGolfCandidate.ReconstructedCheckCapScanFlags

namespace CommitGolfCandidate.Reconstruction.CheckParentStep
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CheckRecorded CommitBlocks CheckGroupRadix Binding CheckParentHeap CheckParentControl
open TwoPermutationPrototype.Sampling
set_option maxRecDepth 14000
set_option maxHeartbeats 1400000

def preserve := [Reg.x2,.x8,.x21,.x23,.x24,.x26,.x27]
def rows (o : Oracle) (e p : Nat) (active : Nat→Bool) (child : Nat→Binding.Digest) :=
  if active p then CheckParentCallCopy.log o e (child (2*p)) (child (2*p+1)) else []

def nextDigest (o : Oracle) (e p : Nat) (child : Nat→Binding.Digest) :=
  parent (oracleCompression o) e (child (2*p)) (child (2*p+1))

def selected (s : MachineState) (on : Bool) := (s.setReg .x10 (W on.toNat)).setPC (addr (if on then 612 else 605))

private theorem choose (o : Oracle) (s : MachineState) (p : Nat) (small : p<512) (on : Bool) (pc : s.pc=addr 610)
    (active : s.getReg .x19=CheckCapScanData.flag p) (read : s.getByte (CheckCapScanData.flag p)=HonestFlagState.code on) :
    Segment o 2 s (selected s on) [] := by
  have ld:=CheckMemoryOps.loadB o s 610 .x10 .x19 _ (by decide) pc active (CheckCapScanData.flag_valid p (by omega))
  rw [read,CheckCapScanFlags.extCode] at ld
  let u:=(s.setReg .x10 (W on.toNat)).setPC (addr 611)
  have br:=CheckBranch.event o u 611 605 .eq .x10 .x0 8168 (by decide) rfl rfl (by decide)
  change Segment o 1 u (u.setPC (if W on.toNat==0#64 then addr 605 else addr 612)) [] at br
  cases on <;> exact compose ld br

private theorem selected_reg (s : MachineState) (on : Bool) (r : Reg) (fresh : r≠.x10) :
    (selected s on).getReg r=s.getReg r := by
  simp [selected,MachineState.getReg_setPC,TwoPermutationPrototype.Opening.getReg_setReg,Ne.symm fresh]

private theorem carryLocal {s t : MachineState} {e size p : Nat} (old : Local s e size p)
    (keep : ∀ r∈CheckParentCallCopy.preserved,t.getReg r=s.getReg r) : Local t e size p :=
  ⟨(keep .x9 (by decide)).trans old.depth,(keep .x18 (by decide)).trans old.child,(keep .x19 (by decide)).trans old.active,
    (keep .x20 (by decide)).trans old.limit,(keep .x22 (by decide)).trans old.dest,(keep .x25 (by decide)).trans old.ordinal⟩

private theorem segBody (o : Oracle) (s : MachineState) (e : Fin 24) (size p : Nat) (c : Word) (active : Nat→Bool)
    (child : Nat→Binding.Digest) (small : p<512) (pc : s.pc=addr 610) (st : Local s e.val size p) (ctx : Context s c)
    (flags : s.getByte (CheckCapScanData.flag p)=HonestFlagState.code (active p)) (tables : CheckParentGeometry.constants s)
    (kids : active p=true → CommitParents.cell s (base (2*p))=child (2*p) ∧ CommitParents.cell s (base (2*p+1))=child (2*p+1)) :
    ∃ n t,n≤19+CheckParent.Cost e ∧ Segment o n s t (rows o e p active child) ∧ t.pc=addr 605 ∧
      Local t e.val size p ∧ Context t c ∧ Frame p (p+1) s t ∧
      (active p=true→CommitParents.cell t (base p)=nextDigest o e p child) ∧
      (active p=false→t.mem=s.mem) ∧
      (∀ r∈preserve,t.getReg r=s.getReg r) := by
  let u:=selected s (active p)
  have chooseSeg:=choose o s p small (active p) pc st.active flags
  have shared (r : Reg) (h : r∈CheckParentCallCopy.preserved) : u.getReg r=s.getReg r := by
    apply selected_reg;intro eq;subst r;exact (by decide : Reg.x10∉CheckParentCallCopy.preserved) h
  have cu : Context u c := ⟨(selected_reg _ _ _ (by decide)).trans ctx.one,(shared _ (by decide)).trans ctx.sp,
    (shared _ (by decide)).trans ctx.fp,(shared _ (by decide)).trans ctx.heap,(shared _ (by decide)).trans ctx.bits,
    (selected_reg _ _ _ (by decide)).trans ctx.scratch⟩
  have localU:=carryLocal st shared
  have um : u.mem=s.mem:=rfl
  cases enabled : active p with
  | false=>
    refine ⟨2,u,by omega,?_,?_,localU,cu,same um _ _,by simp [enabled],fun _=>um,?_⟩
    · rw [rows,enabled];exact chooseSeg
    · change addr (if active p then 612 else 605)=_;rw [enabled];rfl
    · intro r h;apply shared;cases r <;> first | decide | simp [preserve] at h
  | true=>
    have atCall : u.pc=addr 612:=by change addr (if active p then 612 else 605)=_;rw [enabled];rfl
    have ys:=kids enabled
    obtain ⟨t,hash,atT,computed,one,scratch,frame,regs⟩:=CheckParentCallCopy.run o u e p small atCall cu.sp cu.fp localU.depth
      localU.child localU.dest (fun a w al v=>(congrFun um _).trans (tables a w al v)) _ _
      ((CommitParents.cell_congr um _).trans ys.1) ((CommitParents.cell_congr um _).trans ys.2)
    refine ⟨2+(5+CheckParent.Cost e+12),t,by omega,?_,atT,carryLocal localU regs,⟨one,(regs _ (by decide)).trans cu.sp,(regs _ (by decide)).trans cu.fp,
      (regs _ (by decide)).trans cu.heap,(regs _ (by decide)).trans cu.bits,scratch⟩,?_,fun _=>computed,by simp [enabled],?_⟩
    · simpa only [rows,enabled,ite_true,List.nil_append] using compose chooseSeg hash
    · intro w bd sep st dest;exact (frame w bd sep st dest).trans (congrFun um _)
    · intro r hr;have h : r∈CheckParentCallCopy.preserved:=by cases r <;> first | decide | simp [preserve] at hr
      exact (regs r h).trans (shared r h)

theorem run (o : Oracle) (s : MachineState) (e : Fin 24) (size p : Nat) (c : Word) (active : Nat→Bool)
    (child : Nat→Binding.Digest) (bound : size≤256) (small : p<2*size) (pc : s.pc=addr 610) (st : Local s e.val size p)
    (ctx : Context s c) (flags : s.getByte (CheckCapScanData.flag p)=HonestFlagState.code (active p))
    (tables : CheckParentGeometry.constants s)
    (kids : active p=true → CommitParents.cell s (base (2*p))=child (2*p) ∧ CommitParents.cell s (base (2*p+1))=child (2*p+1)) :
    ∃ n t,n≤24+CheckParent.Cost e ∧ Segment o n s t (rows o e p active child) ∧ t.pc=addr (here (p+1) (2*size)) ∧
      Local t e.val size (p+1) ∧ Context t c ∧ Frame p (p+1) s t ∧
      (active p=true→CommitParents.cell t (base p)=nextDigest o e p child) ∧ (active p=false→t.mem=s.mem) ∧
      (∀ r∈preserve,t.getReg r=s.getReg r) := by
  obtain ⟨n,u,lim,sg,atU,loc,localCtx,frame,hash,blank,kept⟩:=segBody o s e size p c active child (by omega) pc st ctx flags tables kids
  obtain ⟨t,next,atT,stT,ct,mem,save⟩:=advance o u e.val size p c atU bound small loc localCtx
  refine ⟨n+5,t,by omega,by simpa only [List.append_nil] using compose sg next,atT,stT,ct,
    fun w hb sep st dest=>(congrFun mem _).trans (frame w hb sep st dest),fun h=>(CommitParents.cell_congr mem _).trans (hash h),
    fun off=>mem.trans (blank off),?_⟩
  intro r h
  exact (save r (by cases r <;> first | decide | simp [preserve] at h)).trans (kept r h)

end CommitGolfCandidate.Reconstruction.CheckParentStep

