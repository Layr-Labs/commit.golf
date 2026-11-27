import CommitGolfCandidate.Stage3cReadEnter
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Reader
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W Outside wordAt)
open Check (Flow)

def fieldReads (o : Oracle) (s t : MachineState) (base bytes v bit k n dest steps back : Nat) :=
  Flow o s t steps 0 ∧ t.pc=pcAt back ∧ Cursor t base bytes v (bit+n) k ∧
  readBuffer t dest 32=decoded v bit n ∧ Outside s t dest 32 ∧ ∀ q,fieldKeep q→t.getReg q=s.getReg q

attribute [local irreducible] readBuffer window
theorem remaining_field (o : Oracle) (s : MachineState) (base bytes v bit k n dst j used count back : Nat)
    (size : n≤256) (done_ : used=min n (64*j)) (num : count=(n-used+63)/64)
    (jbound : j≤4) (room : base+bytes≤MEMORY_BYTES) (space : bit+n≤8*bytes) (low : dst+32≤base) (al : dst%8=0)
    (kmax : k<8) (pc : s.pc=pcAt 27) (ret : s.getReg .x1=pcAt back) (legal : back<2147)
    (rem : s.getReg .x13=W (n-used)) (dest : s.getReg .x12=W (dst+8*j))
    (c : Cursor s base bytes v (bit+used) k) (prior : FieldMemory s dst v bit n j) :
    ∃ t steps rest,steps≤107*count+2 ∧ rest<8 ∧ fieldReads o s t base bytes v bit rest n dst steps back := by
  induction count generalizing s k j used with
  | zero=>
    have exhausted : used=n := by omega
    rw [exhausted] at rem c done_
    let u:=s.setPC (pcAt 61)
    let t:=u.setPC (pcAt back)
    have zero : s.getReg .x13=0:=rem.trans (by rw [Nat.sub_self];rfl)
    have head:=select_zero o .word s pc zero
    have leave:=return_field o u back legal rfl (MachineState.getReg_setPC.trans ret)
    have same : t.mem=s.mem:=rfl
    have regs (q : Reg) : t.getReg q=s.getReg q:=MachineState.getReg_setPC.trans MachineState.getReg_setPC
    have value:=field_memory_done s dst v bit n j size (by omega) (by omega) al prior
    exact ⟨t,2,k,by decide,kmax,head.trans leave,rfl,c.same same (regs _) (regs _) (regs _) (regs _),
      (read_buffer_memory_congr t s same dst 32).trans value,fun q _ _ _=>congrFun same _,fun q _=>regs q⟩
  | succ count ih=>
    have left : 0<n-used:=by omega
    have scale : used=64*j:=by omega
    have idx : j<4:=by omega
    let w:=min (n-used) 64
    have parts : used+w=min n (64*(j+1)) ∧ count=(n-(used+w)+63)/64 := by dsimp [w];omega
    have narrow : n-used≤256:=by omega
    obtain ⟨u,a,k',lim,buffer,g⟩:=field_word o s base bytes v (bit+used) k (n-used) (dst+8*j) left narrow room
      (by omega) kmax pc rem c dest (by omega) (by omega)
    have here : W (window v (bit+used) w)=fieldSlice v bit n j:=by dsimp only [w];rw [field_slice _ _ _ _ size,scale]
    have write : u.mem=(Check.store s (dst+8*j) (fieldSlice v bit n j)).mem:=by
      rw [←here];exact g.mem
    have after:=field_memory_step (s:=s) (t:=u) dst v bit n j size idx (by omega) al prior write
    have urem : u.getReg .x13=W (n-(used+w)):=g.rem.trans (congrArg W (by omega))
    have udst : u.getReg .x12=W (dst+8*(j+1)):=g.dest.trans (congrArg W (by omega))
    have uc : Cursor u base bytes v (bit+(used+w)) k':=by simpa only [Nat.add_assoc,w] using g.cursor
    obtain ⟨t,b,rest,meter,lt,tail⟩:=ih (s:=u) (k:=k') (j:=j+1) (used:=used+w) parts.1 parts.2 (by omega) buffer g.pc
      ((g.keep .x1 (by simp [fieldKeep,readKeep])).trans ret) urem udst uc after
    obtain ⟨run,ep,cursor,data,away,preserved⟩:=tail
    have localFrame:=Check.store_far s (dst+8*j) (fieldSlice v bit n j) (by omega)
    refine ⟨t,a+b,rest,by omega,lt,g.run.trans run,ep,cursor,data,?_,fun q h=>(preserved q h).trans (g.keep q h)⟩
    intro q h aligned separate
    exact (away q h aligned separate).trans ((congrFun write _).trans (localFrame q h aligned (by omega)))

theorem read_field (o : Oracle) (s : MachineState) (base bytes v bit k n dst back : Nat) (size : n≤256)
    (room : base+bytes≤MEMORY_BYTES) (space : bit+n≤8*bytes) (low : dst+32≤base) (al : dst%8=0)
    (kmax : k<8) (pc : s.pc=pcAt 21) (ret : s.getReg .x1=pcAt back) (legal : back<2147)
    (rem : s.getReg .x11=W n) (dest : s.getReg .x10=W dst) (c : Cursor s base bytes v bit k) :
    ∃ t steps rest,steps≤436 ∧ rest<8 ∧ fieldReads o s t base bytes v bit rest n dst steps back := by
  obtain ⟨u,start,ip,udst,urem,queue,clear,frame,keep⟩:=enter_field o s base bytes v bit k dst n pc dest rem low room al c
  obtain ⟨t,b,rest,lim,small,run,ep,cursor,data,away,regs⟩:=remaining_field o u base bytes v bit k n dst 0 0 ((n+63)/64) back
    size (by simp) (by simp) (by decide) room space low al kmax ip ((keep .x1 (by simp [fieldKeep,readKeep])).trans ret) legal
    (by simpa using urem) (by simpa using udst) (by simpa using queue) clear
  exact ⟨t,6+b,rest,by omega,small,start.trans run,ep,cursor,data,
    fun q h a away_ =>(away q h a away_).trans (frame q h a away_),fun q h=>(regs q h).trans (keep q h)⟩
end CommitGolfCandidate.Chained.BinaryMachine.Reader
