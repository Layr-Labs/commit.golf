import CommitGolfCandidate.S4Header
import CommitGolfCandidate.S4UpperBody
namespace CommitGolfCandidate.S4.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (pcAt)
theorem upperStep (o : Oracle) (x : CheckInput) (k : Fin 8) (i : Nat) (s : MachineState) (inside : i<nextWidth k)
    (f : UpperCursor o.compression x k i s) : ∃ t steps,steps≤32 ∧ CheckRuns o s t steps 1 ∧ UpperCursor o.compression x k (i+1) t := by
  obtain ⟨u,h⟩:=upperBody o x k i s inside f
  have code:=upperSites k
  let t:=Sym.evaluated addUpper u
  obtain ⟨incs,regs,mem,ip⟩:=evalMath .check addUpper _ _ u h.pc code.advance
    (fun c m=>bne_iff_ne.mp (List.all_eq_true.mp (by decide : addUpper.all (fun c=>c.dst != .x0)=true) c m))
    (fun _ m=>by cases m)
  have preserve (r : Reg) (away : r∉[Reg.x29,.x30,.x19]) : t.getReg r=u.getReg r:=
    outsideCalc addUpper u t regs _ rfl r away
  have src : t.getReg .x29=W (upperAddr (2*(i+1))):=by
    apply (regs .x29).trans;change u.getReg .x29+W 64=_
    rw [(h.keep _ (by decide)).trans f.source]
    exact (BitVec.ofNat_add ..).symm.trans (congrArg W (by unfold upperAddr;omega))
  have dst : t.getReg .x30=W (upperAddr (i+1)):=by
    apply (regs .x30).trans;change u.getReg .x30+W 32=_
    rw [(h.keep _ (by decide)).trans f.dest]
    exact (BitVec.ofNat_add ..).symm.trans (congrArg W (by unfold upperAddr;omega))
  have remaining : t.getReg .x19=W (nextWidth k-(i+1)):=by
    apply (regs .x19).trans;change u.getReg .x19+18446744073709551615=_
    rw [(h.keep _ (by decide)).trans f.remaining]
    exact (prev (nextWidth k-i) (by omega)).trans (congrArg W (by omega))
  have edge:=alternate .check (afterHash k+3) (afterHash k+5) (upperLoop k) .x19 .x0 true code.last code.more rfl t ip
  have small:=(upperGeometry k).1
  have test : ((t.getReg .x19==t.getReg .x0)==true)=decide (nextWidth k ≤ i+1):=by
    change ((t.getReg .x19==W 0)==true)=_;rw [remaining,eqNatural _ _ (by omega) (by decide)]
    by_cases e:nextWidth k ≤ i+1
    · rw [decide_eq_true e,decide_eq_true (by omega : nextWidth k-(i+1)=0)];rfl
    · rw [decide_eq_false e,decide_eq_false (by omega : ¬nextWidth k-(i+1)=0)];rfl
  rw [test,code.next] at edge
  let z:=t.setPC (pcAt (if i+1<nextWidth k then upperLoop k else upperHeader (k.val+1)))
  have eMem : z.mem=u.mem:=mem
  have members : ∀ r : Reg,envReg r → r∉[Reg.x29,.x30,.x19]:=by intro r;cases r <;> decide
  have envNext:=h.env.move (fun r m=>MachineState.getReg_setPC.trans (preserve r (members r m))) (h.env.data.regs eMem)
  have tab : RowMemory o.compression (readView x) k (i+1) z:=⟨fun j bj=>(read_buffer_memory_congr z u eMem _ _).trans (h.table.done j bj),
    fun j lo hi=>(read_buffer_memory_congr z u eMem _ _).trans (h.table.rest j lo hi)⟩
  have next : UpperCursor o.compression x k (i+1) z:=⟨envNext,rfl,src,dst,remaining,tab⟩
  have bound : callSteps (cutUpper k)≤2:=by unfold callSteps;split <;> decide
  by_cases more : i+1<nextWidth k
  · rw [decide_eq_false (Nat.not_le_of_lt more)] at edge
    have go : Runs .check t z 2 2:=by dsimp only [z];rw [if_pos more];exact edge
    exact ⟨z,21+(2+callSteps (cutUpper k))+3+2,by omega,(h.run.trans (ofRuns o incs)).trans (ofRuns o go),next⟩
  · rw [decide_eq_true (Nat.le_of_not_gt more)] at edge
    have go : Runs .check t z 1 1:=by dsimp only [z];rw [if_neg more];exact edge
    exact ⟨z,21+(2+callSteps (cutUpper k))+3+1,by omega,(h.run.trans (ofRuns o incs)).trans (ofRuns o go),next⟩

theorem layerBody (o : Oracle) (x : CheckInput) (k : Fin 8) (s : MachineState) (init : UpperCursor o.compression x k 0 s)
    (j : Nat) (limit : j≤nextWidth k) : ∃ t fuel,fuel≤32*j ∧ CheckRuns o s t fuel j ∧ UpperCursor o.compression x k j t := by
  induction j with
  | zero=>exact ⟨s,0,le_rfl,CheckRuns.refl o s,init⟩
  | succ j ih=>
    obtain ⟨u,a,ba,prev,cur⟩:=ih (by omega)
    obtain ⟨t,b,bb,next,after⟩:=upperStep o x k j u (by omega) cur
    exact ⟨t,a+b,by omega,prev.trans next,after⟩

def upperQueries : Nat→Nat | 0=>0 | k+1=>upperQueries k+nextWidth k
theorem upperLayers (o : Oracle) (x : CheckInput) (s : MachineState) (env : Env x s) (pc : s.pc=pcAt (upperHeader 0))
    (base : Level o.compression (readView x) 0 s) (k : Nat) (bound : k≤8) :
    ∃ t n,n≤3000*k ∧ CheckRuns o s t n (upperQueries k) ∧ t.pc=pcAt (upperHeader k) ∧ Env x t ∧ Level o.compression (readView x) k t := by
  induction k with
  | zero=>exact ⟨s,0,le_rfl,CheckRuns.refl o s,pc,env,base⟩
  | succ k ih=>
    obtain ⟨u,n,nBound,go,atPC,henv,tab⟩:=ih (by omega)
    let d : Fin 8:=⟨k,by omega⟩
    obtain ⟨v,h,hb,header,init⟩:=upperEnter o d u x henv atPC tab
    obtain ⟨t,l,lb,body,done⟩:=layerBody o x d v init (nextWidth k) le_rfl
    have small : nextWidth k≤86:=(upperGeometry d).1
    refine ⟨t,n+(h+l),by omega,?_,?_,done.toEnv,?_⟩
    · exact go.trans (by simpa only [Nat.zero_add] using header.trans body)
    · have e:=done.pc;rw [if_neg (show ¬nextWidth k<nextWidth d from Nat.lt_irrefl _)] at e;exact e
    · intro j bj;apply done.table.done j;change j<width (17+k);simpa only [show 16+(k+1)=17+k by omega] using bj
end CommitGolfCandidate.S4.Machine
