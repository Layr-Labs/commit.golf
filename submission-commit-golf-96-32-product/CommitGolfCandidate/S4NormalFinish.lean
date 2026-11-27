import CommitGolfCandidate.S4NormalOpen

set_option Elab.async false
namespace CommitGolfCandidate.S4.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open Machine (W Runs proofBase indexBase)
open Late (Trapdoor pcAt)
set_option maxRecDepth 7000
attribute [local irreducible] Machine.Sym.evaluated
def normalExitOps : List Machine.Sym.Calc := [.sub .x11 .x19 .x15,.addi .x5 .x0 1,.addi .x10 .x0 0]
def exitState (s : MachineState) := Machine.Sym.evaluated normalExitOps s
private theorem exitCode : (Machine.Fragment.arithmetic normalExitOps).valid .opening 5872 5875 := by decide

theorem normalExit (s : MachineState) (k : Nat) (pc : s.pc=pcAt 5872) (dst : s.getReg .x19=W (proofBase+824*k))
    (out : s.getReg .x15=W proofBase) :
    let t:=exitState s
    (∀ fuel,execute Machine.Code.opening.image (fuel+4) s true=pure ⟨.success,t,4,0⟩) ∧
      t.mem=s.mem ∧ t.getReg .x11=W (824*k) := by
  obtain ⟨run,regs,mem,endPC⟩:=Machine.evalMath .opening normalExitOps 5872 5875 s pc exitCode
    (by intro c hc;simp only [normalExitOps,List.mem_cons,List.not_mem_nil,or_false] at hc;rcases hc with rfl|rfl|rfl <;> decide)
    (fun _ mem=>by cases mem)
  have done (fuel : Nat) := Machine.stop (by decide : 5875<Machine.Code.opening.count) endPC (by rfl)
    ((regs .x5).trans rfl) fuel true
  rw [show (Machine.Sym.evaluated normalExitOps s).getReg .x10=0 from (regs .x10).trans rfl,if_pos rfl] at done
  have length : (Machine.Sym.evaluated normalExitOps s).getReg .x11=W (824*k):=by
    rw [regs .x11];change s.getReg .x19-s.getReg .x15=_
    rw [dst,out];exact (congrArg (·-W proofBase) (BitVec.ofNat_add (n:=64) proofBase (824*k))).trans (by rw [BitVec.add_comm (W proofBase) _,BitVec.add_sub_cancel])
  refine ⟨?_,mem,length⟩
  intro fuel;rw [show fuel+4=(fuel+1)+normalExitOps.length by rfl,run,done,pure_bind];rfl

theorem normalEntry (td : Trapdoor) (ps : Positions) (normal : ps.card≠128) (s : MachineState) (ready : ReadyAtOne td ps s) :
    ∃ t n m,NormalCursor td ps t 0 ∧ Runs .opening s t n m ∧ n≤8 := by
  let u:=resumeState s ps.card
  have modeRun:=resumeMode ps s ready.pc (ready.regs .x16) (ready.regs .x6)
  have regs (r : Reg) (ne : r≠.x6) : u.getReg r=(initial td ps).getReg r :=
    (ready.regs r).trans (MachineState.getReg_setReg_ne _ _ _ _ ne.symm)
  have p : u.pc=pcAt (entrySite false):=by simp [u,resumeState,modePC,entrySite,normal,MachineState.setPC]
  obtain ⟨setupRun,at5279,mem,dst,three,_,output,_,normalRegs⟩:=entrySetup false u p
  obtain ⟨left,positions⟩:=normalRegs rfl
  let a:=setup false u
  have outBase : a.getReg .x15=W proofBase:=output.trans (regs .x15 (by decide))
  have cur : a.getReg .x19=W proofBase:=dst.trans (regs .x15 (by decide))
  have cnt : a.getReg .x20=W ps.card:=left.trans (regs .x16 (by decide))
  have ix : a.getReg .x21=W indexBase:=positions.trans (regs .x13 (by decide))
  have edge:=Machine.alternate .opening 5279 5281 5872 .x20 .x0 false (by decide) (by decide) rfl a at5279
  have small : ps.card≤LENGTH:=by simpa using Finset.card_le_univ ps
  change ps.card≤16777216 at small
  have test : ((a.getReg .x20==a.getReg .x0)==false)=decide (0<ps.card):=by
    change ((a.getReg .x20==W 0)==false)=_
    rw [cnt,Machine.eqNatural _ _ (by omega) (by decide)]
    by_cases emp : ps.card=0
    · simp [emp]
    · simp [emp,Nat.pos_of_ne_zero emp]
  rw [test] at edge
  let t:=a.setPC (pcAt (normalEndPC ps.card 0))
  have source : Sources td ps t:=ready.sources.sameMem mem
  have st : NormalCursor td ps t 0:=⟨rfl,cur,ix,cnt,outBase,three,source,containsEmpty t proofBase⟩
  rw [resumeSteps,if_neg normal] at modeRun
  by_cases pos : 0<ps.card
  · rw [decide_eq_true pos] at edge
    have e : Runs .opening a t 1 1:=by dsimp only [t,normalEndPC];rw [if_pos pos];exact edge
    exact ⟨t,7,7,st,(modeRun.trans setupRun).trans e,by decide⟩
  · rw [decide_eq_false pos] at edge
    have e : Runs .opening a t 2 2:=by dsimp only [t,normalEndPC];rw [if_neg pos];exact edge
    exact ⟨t,8,8,st,(modeRun.trans setupRun).trans e,by decide⟩

structure Resumed (td : Trapdoor) (ps : Positions) (start : MachineState) (fuel : Nat) (e : Execution) : Prop where
  run : execute Machine.Code.opening.image fuel start true=pure e
  noCalls : e.oracleCalls=0
  exit : e.exit=.success
  success : Late.submission.openingSucceeded e=true
  bytes : Late.submission.readProof e=codedOutput td ps

attribute [local irreducible] execute
private theorem rawABI (td : Trapdoor) (ps : Positions) :
    Late.submission.run .opening (td,ps)=execute Machine.Code.opening.image 1099511627776 (initial td ps) true := by
  have run (c : Submission) (a : BitVec (8*c.sizes.trapdoor)) :
      c.run .opening (a,ps)=execute (c.image .opening) (c.steps .opening) (c.initialState .opening (a,ps)) true:=rfl
  exact (run Late.submission td).trans (congrArg (fun fuel=>execute (Late.submission.image .opening) fuel
    (Late.submission.initialState .opening (td,ps)) true) (show Late.submission.steps .opening=1099511627776 from rfl))

private theorem endTrace (s u t : MachineState) (n m k c slack fuel : Nat)
    (e : fuel=(slack+4)+(n+k)) (first : Runs .opening s u n m) (second : Runs .opening u t k c)
    (done : execute Machine.Code.opening.image (slack+4) t true=pure ⟨.success,exitState t,4,0⟩) :
    execute Machine.Code.opening.image fuel s true=pure ⟨.success,exitState t,m+c+4,0⟩ := by
  rw [e,(first.trans second) (slack+4) true,done,pure_bind];rfl

private theorem finalBytes (td : Trapdoor) (ps : Positions) (normal : ps.card≠128) (s t : MachineState)
    (m : Nat) (mem : t.mem=s.mem) (st : NormalCursor td ps s ps.card) (len : t.getReg .x11=W (824*ps.card)) :
    Late.submission.readProof ⟨.success,t,m,0⟩=rawOutput td ps := by
  have pay : returnedRecords td ps false ps.card=rawOutput td ps:=by
    unfold rawOutput;dsimp only;rw [if_neg (show ps.card≠BATCH from normal)]
    have bound : (indices ps).length≤ps.card:=by rw [indices,Finset.length_sort]
    rw [returnedRecords,List.take_of_length_le bound]
  have written : Contains t proofBase (rawOutput td ps):=pay ▸ st.data.mem mem
  have sz := returnedLen td ps false ps.card le_rfl
  rw [pay] at sz;change (rawOutput td ps).length=824*ps.card at sz
  apply reportBytes t (rawOutput td ps) m _ _ written
  · rw [sz];exact len
  · have small : ps.card≤LENGTH:=by simpa using Finset.card_le_univ ps
    change ps.card≤16777216 at small
    change (rawOutput td ps).length≤17179869184;rw [sz];omega

private theorem readSuccess (t : MachineState) (cycles k : Nat) (small : k≤16777216) (len : t.getReg .x11=W (824*k)) :
    Late.submission.openingSucceeded ⟨.success,t,cycles,0⟩=true := by
  change true && decide ((t.getReg .x11).toNat≤17179869184)=true
  rw [len,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)];simp;omega

attribute [local irreducible] rawOutput recordState initial exitState
theorem ordinaryResumed (td : Trapdoor) (ps : Positions) (normal : ps.card≠128) (s0 : MachineState) (ready : ReadyAtOne td ps s0) (fuel : Nat) (enough : 591*ps.card+12≤fuel) : ∃ e,Resumed td ps s0 fuel e := by
  obtain ⟨s,n,m,cursor,initRun,hb⟩:=normalEntry td ps normal s0 ready
  obtain ⟨t,l,c,finalState,body,lb⟩:=normalAll td ps s cursor ps.card le_rfl
  have pc : t.pc=pcAt 5872:=by simpa only [normalEndPC,lt_self_iff_false,ite_false] using finalState.pc
  obtain ⟨exitRun,mem,len⟩:=normalExit t ps.card pc finalState.dest finalState.output
  have count : ps.card≤LENGTH:=by simpa using Finset.card_le_univ ps
  change ps.card≤16777216 at count
  let slack:=fuel-(n+l+4)
  have eqv : fuel=(slack+4)+(n+l):=by dsimp [slack];omega
  refine ⟨⟨.success,exitState t,m+c+4,0⟩,?_,rfl,rfl,readSuccess _ _ _ count len,?_⟩
  · exact endTrace _ _ _ _ _ _ _ _ _ eqv initRun body (exitRun slack)
  · rw [codedOutput,if_neg (show ps.card≠BATCH from normal)];exact finalBytes td ps normal t (exitState t) _ mem finalState len
end CommitGolfCandidate.S4.Open
