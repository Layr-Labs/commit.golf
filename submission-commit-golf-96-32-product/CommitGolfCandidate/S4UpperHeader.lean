import CommitGolfCandidate.S4UpperCode
import CommitGolfCandidate.S4Inputs
namespace CommitGolfCandidate.S4.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (pcAt)
abbrev envReg (r : Reg) := r∈[Reg.x5,.x13,.x11,.x23,.x27]
theorem Env.move {x : CheckInput} {s t : MachineState} (old : Env x s) (reg : ∀ r,envReg r → t.getReg r=s.getReg r)
    (input : InputsStill x t) : Env x t :=
  ⟨(reg _ (by decide)).trans old.mode,(reg _ (by decide)).trans old.kind,(reg _ (by decide)).trans old.width,
    (reg _ (by decide)).trans old.three,(reg _ (by decide)).trans old.root,input⟩
structure UpperCursor (H : Compression) (x : CheckInput) (k i : Nat) (s : MachineState) extends Env x s : Prop where
  pc : s.pc=pcAt (if i<nextWidth k then upperLoop k else upperHeader (k+1))
  source : s.getReg .x29=W (upperAddr (2*i))
  dest : s.getReg .x30=W (upperAddr i)
  remaining : s.getReg .x19=W (nextWidth k-i)
  table : RowMemory H (readView x) k i s

private theorem maybePad (k : Fin 8) (s : MachineState) (x : CheckInput) (H : Compression) (old : Level H (readView x) k s)
    (pc : s.pc=pcAt (paddingPC k)) (ptr : needsPad k=true → s.getReg .x14=W (upperAddr (width (16+k.val)))) :
    ∃ t n,n≤4 ∧ Runs .check s t n n ∧ t.pc=pcAt (countPC k) ∧ (∀ r,t.getReg r=s.getReg r) ∧
      HighExcept s t (upperAddr (width (16+k.val))) 32 ∧ RowMemory H (readView x) k 0 t := by
  let size:=width (16+k.val)
  have counts:=upperBounds k.val k.isLt
  by_cases yes : needsPad k=true
  · have al : upperAddr size%8=0:=by unfold upperAddr;omega
    obtain ⟨run,last,keep,frame,z⟩:=upperPad s (paddingPC k) (upperAddr size) pc (ptr yes) al (by unfold upperAddr MEMORY_BYTES size;omega)
      (by have e:=(upperSites k).loop;have b:=(upperSites k).small;have limit : ∀ k : Fin 8, paddingPC k+4≤4858:=by decide
          exact limit k) ((upperSites k).pad yes)
    let t:=padState s 4
    have still : Level H (readView x) k t:=by
      intro j bj
      exact (frame.read (b:=upperAddr j) (m:=32) (by unfold upperAddr;omega)
        (Or.inl (by unfold upperAddr;dsimp only [size];omega))).trans (old j bj)
    exact ⟨t,4,le_rfl,run,by simpa only [countPC,yes,ite_true] using last,keep,highWrite frame,
      rowStartMemory H _ _ k.isLt t still (fun _=>z)⟩
  · have no:=Bool.eq_false_iff.mpr yes
    have w:=((upperGeometry k).2.2.1 no)
    refine ⟨s,0,by decide,Runs.refl _ _,?_,fun _=>rfl,fun _ _ _ _=>rfl,rowStartMemory H _ _ k.isLt s old (fun h=>False.elim (by unfold nextWidth at w;omega))⟩
    simpa only [countPC,no,Bool.false_eq_true,ite_false,Nat.add_zero] using pc

theorem upperEnter (o : Oracle) (k : Fin 8) (s : MachineState) (x : CheckInput) (env : Env x s)
    (pc : s.pc=pcAt (upperHeader k)) (level : Level o.compression (readView x) k s) :
    ∃ t n,n≤14 ∧ CheckRuns o s t n 0 ∧ UpperCursor o.compression x k 0 t := by
  let ops:=upperHeaderOps k
  let u:=Sym.evaluated ops s
  have facts:=upperSites k
  obtain ⟨upperCap,sizeCap,_,imm,allowed,nz,reads,src,dest,ptr,price⟩:=upperGeometry k
  obtain ⟨run,regs,mem,atPad⟩:=evalMath .check ops _ _ s pc facts.setup
    (fun c h=>bne_iff_ne.mp (List.all_eq_true.mp nz c h)) (fun _ h=>by rw [reads] at h;cases h)
  have live (r : Reg) (hr : r∉[Reg.x29,.x30,.x14]) : u.getReg r=s.getReg r :=outsideCalc ops s u regs _ allowed r hr
  have old : Level o.compression (readView x) k u:=fun j bj=>(read_buffer_memory_congr u s mem _ _).trans (level j bj)
  obtain ⟨v,n,nb,pad,padPC,keep,frame,ready⟩:=maybePad k u x o.compression old atPad
    (fun yes=>(regs .x14).trans ((congrArg (Sym.Expr.eval s) (ptr yes)).trans rfl))
  let t:=execInstrBr v (numOp k)
  have fits : ∀ h : Fin 8,countPC h<4858:=by decide
  have set:=stepAdd .check v (countPC k) .x19 .x0 _ (fits k) padPC (stood facts.count)
  have mr (r : Reg) (ne : r≠.x19) : t.getReg r=v.getReg r:=keepAdd v .x19 .x0 r _ (Ne.symm ne)
  have inputs : InputsStill x t:=((frame.env (by unfold upperAddr;omega) (env.data.regs mem))).regs (show t.mem=v.mem from rfl)
  have preserved : ∀ r : Reg,envReg r → r≠.x19 ∧ r∉[Reg.x29,.x30,.x14]:=by intro r;cases r <;> decide
  have fixed:=env.move (fun r hr=>(mr r (preserved r hr).1).trans ((keep r).trans (live r (preserved r hr).2))) inputs
  have memory : RowMemory o.compression (readView x) k 0 t:=⟨fun _ h=>False.elim (by omega),fun j l h=>(read_buffer_memory_congr t v rfl _ _).trans (ready.rest j l h)⟩
  have success : t.pc=pcAt (upperLoop k):=(addPC _ _ _ padPC).trans (congrArg pcAt facts.loop)
  have positive := (upperBounds _ k.isLt).2.2.1
  refine ⟨t,ops.length+n+1,by change ops.length≤9 at price;omega,((ofRuns o run).trans (ofRuns o pad)).trans (ofRuns o set),?_⟩
  refine ⟨fixed,?_,?_,?_,?_,memory⟩
  · rw [if_pos (show 0<nextWidth k from positive)];exact success
  · exact (mr .x29 (by decide)).trans ((keep .x29).trans ((regs .x29).trans ((congrArg (Sym.Expr.eval s) src).trans rfl)))
  · exact (mr .x30 (by decide)).trans ((keep .x30).trans ((regs .x30).trans ((congrArg (Sym.Expr.eval s) dest).trans rfl)))
  · apply (getAfterAdd v .x19 .x0 _ (by decide)).trans;exact (BitVec.zero_add _).trans imm
end CommitGolfCandidate.S4.Machine
