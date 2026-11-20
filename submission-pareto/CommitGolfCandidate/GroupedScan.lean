import CommitGolfCandidate.GroupedPacketRun
import CommitGolfCandidate.TwoPermutationCounted

namespace TwoPermutationPrototype.Grouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open TwoPermutationPrototype.QuartetCommit (qSource qSalt)
set_option maxRecDepth 18000
set_option maxHeartbeats 2000000

abbrev N : Nat := 16777216
def startPC (i : Nat) := if i=N then wordPC 181041 else wordPC (firstWord4 (i%16384))
/-- The latch after slot 16383: `srli x12,x10,32; bne x12,x0,+8` (2 cycles on final exit, + `jal` = 3 on loop). -/
def edgeCost (i : Nat) := if i%16384=16383 then (if i+1=N then 2 else 3) else 0
/-- Instructions (steps) before slot `i`: 181,003 per 4-tile pass, minus 1 on final exit. -/
def S (i : Nat) := 181003*(i/16384)+45250*((i%16384)/4096)+firstWord (i%4096)-38-(if i=N then 1 else 0)
/-- Oracle calls before slot `i`: the A leaf also runs the first call of its C leaf; one quartet call
per four leaves. -/
def Q (i : Nat) := 2*i+heads i+(if rank i=1 then 1 else 0)+i/4
def C (i : Nat) := S i+7*Q i

theorem calls_plan (i : Nat) :
    opCalls (plan i)=(if rank i=0 then 4 else if rank i=1 then 1 else 2)+(if i%4=3 then 1 else 0) := by
  unfold plan bodyPlan tailPlan saltPlan
  have h := rank_lt i
  have m : i%4096%4=i%4 := by omega
  by_cases kd : keyed (i%4096)
  all_goals
    by_cases t : i%4=3
    · by_cases e : i%4096/4%2=0
      · generalize rank i=r at *
        interval_cases r <;> simp [opCalls,Action.calls,m,t,e,kd]
      · generalize rank i=r at *
        interval_cases r <;> simp [opCalls,Action.calls,m,t,e,kd]
    · generalize rank i=r at *
      interval_cases r <;> simp [opCalls,Action.calls,m,t,kd]

theorem length_plan (i : Nat) : (plan i).length+chainLen (i%4096)=leafLen (rank i)+extraLen (i%4096) := by
  have h:=congrArg List.length (plan_words i)
  simp only [List.length_map] at h
  rw [h];have := packet_length (i%4096);rwa [within_rank] at this

theorem first_word_ge (n : Nat) : 38≤firstWord n := first_word_ge38 n

theorem cumul (i : Nat) (hi : i<N) :
    S (i+1)=S i+(plan i).length+edgeCost i ∧ Q (i+1)=Q i+opCalls (plan i) := by
  constructor
  · have len : (plan i).length=(packet (i%4096)).length := by
      have h:=congrArg List.length (plan_words i);simpa using h
    rw [len];unfold S edgeCost
    have g0 := first_word_ge (i%4096)
    have hnotN : i≠N := by omega
    rw [if_neg hnotN]
    by_cases edge16 : i%16384=16383
    · have edge4 : i%4096=4095 := by omega
      have step := packet_next 4095 (by decide)
      have top : firstWord (4095+1)=45288 := by decide
      have zero : firstWord 0=38 := by decide
      rw [if_pos edge16,show (i+1)/16384=i/16384+1 by omega,show (i+1)%16384=0 by omega,
        show (i+1)%4096=0 by omega,edge4,show (i%16384)/4096=3 by omega]
      rw [edge4] at g0
      by_cases last : i+1=N
      · rw [if_pos last,if_pos last]; omega
      · rw [if_neg last,if_neg last]; omega
    · have notLast : i+1≠N := by dsimp [N] at hi ⊢; omega
      rw [if_neg edge16,if_neg notLast,show (i+1)/16384=i/16384 by omega]
      by_cases edge4 : i%4096=4095
      · have step := packet_next 4095 (by decide)
        have top : firstWord (4095+1)=45288 := by decide
        have zero : firstWord 0=38 := by decide
        rw [show ((i+1)%16384)/4096=(i%16384)/4096+1 by omega,show (i+1)%4096=0 by omega,edge4]
        rw [edge4] at g0; omega
      · have step := packet_next (i%4096) (by omega)
        rw [show ((i+1)%16384)/4096=(i%16384)/4096 by omega,show (i+1)%4096=i%4096+1 by omega]
        omega
  · rw [calls_plan];unfold Q
    rw [heads_succ]
    have g : (i+1)/4=i/4+(if i%4=3 then 1 else 0) := by split <;> omega
    rw [g]
    by_cases r0 : rank i=0
    · rw [if_pos r0,if_pos r0,if_neg (show ¬rank i=1 by omega),if_pos (head_pair i r0)];omega
    · rw [if_neg r0,if_neg r0]
      by_cases r1 : rank i=1
      · have : rank (i+1)≠1 := by
          by_cases z : rank (i+1)=0
          · omega
          · rw [rank_next i z];omega
        rw [if_pos r1,if_pos r1,if_neg this];omega
      · have : rank (i+1)≠1 := by
          by_cases z : rank (i+1)=0
          · omega
          · rw [rank_next i z];omega
        rw [if_neg r1,if_neg r1,if_neg this];omega

/-- After slot 16383 of a 4-tile pass, the latch's `srli x12,x10,32` leaves `x10 >>> 32` in x12. -/
def latchReg (t : MachineState) (i : Nat) : MachineState :=
  if i%16384=16383 then t.setReg .x12 (t.getReg .x10 >>> (32:Nat)) else t

theorem latch_getReg (t : MachineState) (i : Nat) (r : Reg) (h : r≠.x12) : (latchReg t i).getReg r=t.getReg r := by
  unfold latchReg;split
  · exact MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h)
  · rfl

theorem latch_mem (t : MachineState) (i : Nat) : (latchReg t i).mem=t.mem := by
  unfold latchReg;split <;> rfl

def stepTrace (s : MachineState) (i : Nat) : OracleComp World MachineState := do
  let t ← runOps (plan i) s
  return (latchReg t i).setPC (startPC (i+1))

structure Live (s : MachineState) (i : Nat) extends PacketRegs s i where
  pc : s.pc=startPC i

theorem step_live (s : MachineState) (i : Nat) (hi : i<N) (r : Live s i)
    (u : MachineState) (reach : u∈support (stepTrace s i)) : Live u (i+1) := by
  simp only [stepTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reach
  obtain ⟨t,hit,rfl⟩ := reach
  have post := (walk_post _ _ _ (packet_walk s i hi r.toPacketRegs)).2 t hit
  have lg : ∀ reg, reg≠.x12 → ((latchReg t i).setPC (startPC (i+1))).getReg reg=t.getReg reg :=
    fun reg h => (MachineState.getReg_setPC).trans (latch_getReg t i reg h)
  obtain ⟨src,k20,k23,ct,sel,sz,pr,k8,k9,k19,k21,k25,k26,k27,k28,k29,k30,k6,k1,k2,k3,k18,k22,k4,k7,k31⟩ := post
  have L (reg : Reg) (h : reg≠.x12) {v : Word} (k : t.getReg reg=v) :
      ((latchReg t i).setPC (startPC (i+1))).getReg reg=v := (lg reg h).trans k
  exact ⟨⟨L _ (by decide) src,L _ (by decide) (k20.trans r.s0),L _ (by decide) (k23.trans r.s1),
    L _ (by decide) (k25.trans r.s2),L _ (by decide) (k26.trans r.s3),L _ (by decide) (k27.trans r.a0),
    L _ (by decide) (k28.trans r.a1),L _ (by decide) (k29.trans r.a2),L _ (by decide) (k30.trans r.a3),
    L _ (by decide) (k8.trans r.o0),L _ (by decide) (k9.trans r.o1),L _ (by decide) (k18.trans r.o2),
    L _ (by decide) (k19.trans r.o3),L _ (by decide) (k21.trans r.b0),L _ (by decide) (k22.trans r.b1),
    L _ (by decide) (k4.trans r.b2),L _ (by decide) (k7.trans r.b3),L _ (by decide) (k1.trans r.far),
    L _ (by decide) (k2.trans r.close),L _ (by decide) (k31.trans r.farOdd),L _ (by decide) (k6.trans r.closeOdd),
    L _ (by decide) (k3.trans r.link),L _ (by decide) ct,L _ (by decide) sel,L _ (by decide) sz,L _ (by decide) pr⟩,rfl⟩

theorem edge_run (s : MachineState) (i fuel : Nat) (hi : i<N)
    (start : s.pc=wordPC (firstWord4 (i%16384)+(plan i).length))
    (hp : s.getReg .x10=wordAddress (entryWord (i+1))) :
    execute image (edgeCost i+fuel) s true = (do
      let z ← execute image fuel ((latchReg s i).setPC (startPC (i+1))) true
      return z.charge (edgeCost i) 0) := by
  have len : (plan i).length=(packet (i%4096)).length := by
    have h:=congrArg List.length (plan_words i); simpa using h
  have mod4 : (i%16384)%4096=i%4096 := by omega
  have stepNext : firstWord4 (i%16384)+(plan i).length = 45250*((i%16384)/4096)+firstWord (i%4096+1) := by
    unfold firstWord4; rw [mod4,len,Nat.add_assoc,←packet_next (i%4096) (by omega)]
  rw [stepNext] at start
  by_cases edge : i%16384=16383
  · have e4 : i%4096=4095 := by omega
    have pc : s.pc=wordPC 181038 := by
      rw [start,show (i%16384)/4096=3 by omega,e4,show firstWord (4095+1)=45288 by decide]
    have fetchS : fetch image s=some (.base (.SRLI .x12 .x10 32)) :=
      fetch_decoded s 181038 (by decide) pc _ (by decide +kernel)
    have head : entryWord (i+1)=msgWord (i+1)+7 := by
      have r0 : rank (i+1)=0 := by unfold rank;rw [show (i+1)%4096=0 by omega]
      unfold entryWord;rw [if_pos (by omega : rank (i+1)≤1)]
    let s1 := execInstrBr s (.SRLI .x12 .x10 32)
    have opS : ordinaryStep s (.base (.SRLI .x12 .x10 32))=some s1 := by
      simp [ordinaryStep,memoryArgumentsValid,memAccess,s1]
    have pc1 : s1.pc=wordPC 181039 := by simp only [s1,execInstrBr,MachineState.setPC,pc];rfl
    have fetchB : fetch image s1=some (.base (.BNE .x12 .x0 8)) :=
      fetch_decoded s1 181039 (by decide) pc1 _ (by decide +kernel)
    have lr : latchReg s i=s.setReg .x12 (s.getReg .x10 >>> (32:Nat)) := by unfold latchReg;rw [if_pos edge]
    have high : s1.getReg .x12=s.getReg .x10 >>> (32:Nat) := by
      simp only [s1,execInstrBr,MachineState.getReg_setPC];exact MachineState.getReg_setReg_eq (by decide)
    have x0z : s1.getReg .x0=0#64 := rfl
    have big : 8*(msgWord (i+1)+7)<2^64 := by unfold msgWord;dsimp [N] at hi;omega
    have shr : s.getReg .x10 >>> (32:Nat)=BitVec.ofNat 64 (8*(msgWord (i+1)+7)/2^32) := by
      rw [hp,head];unfold wordAddress;apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,BitVec.toNat_ofNat,Nat.mod_eq_of_lt big]
      exact (Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) big)).symm
    by_cases last : i+1=N
    · have one : 8*(msgWord (i+1)+7)/2^32=1 := by unfold msgWord;rw [last];decide
      have nz : s1.getReg .x12≠s1.getReg .x0 := by rw [high,shr,one,x0z];decide
      have op : ordinaryStep s1 (.base (.BNE .x12 .x0 8))=some ((latchReg s i).setPC (wordPC 181041)) := by
        have stepB : ordinaryStep s1 (.base (.BNE .x12 .x0 8)) = some (s1.setPC (wordPC 181041)) := by
          simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,pc1,nz,wordPC,signExtend13]
        rw [stepB, lr]; rfl
      rw [edgeCost,if_pos edge,if_pos last,startPC,if_pos last,
        show 2+fuel=(fuel+1)+1 by omega,execute_ordinary_step _ _ _ _ _ _ fetchS opS,
        execute_ordinary_step _ _ _ _ _ _ fetchB op]
      simp [Execution.charge,instructionCycles,←Nat.add_assoc]
    · have lt : 8*(msgWord (i+1)+7)<2^32 := by unfold msgWord;dsimp [N] at hi last;omega
      have zz : s1.getReg .x12=s1.getReg .x0 := by rw [high,shr,Nat.div_eq_of_lt lt,x0z]
      let mid := s1.setPC (wordPC 181040)
      have next : (i+1)%16384=0 := by omega
      have op : ordinaryStep s1 (.base (.BNE .x12 .x0 8))=some mid := by
        simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,pc1,zz,mid] <;> rfl
      have fj : fetch image mid=some (.base (.JAL .x0 1373144)) := fetch_decoded mid 181040 (by decide) rfl _ (by decide +kernel)
      have jump : ordinaryStep mid (.base (.JAL .x0 1373144))=some ((latchReg s i).setPC (wordPC 38)) := by
        rw [lr];simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,mid,s1,MachineState.setPC,MachineState.setReg] <;> rfl
      rw [edgeCost,if_pos edge,if_neg last,startPC,if_neg last,next,show firstWord4 0=38 by decide,
        show 3+fuel=((fuel+1)+1)+1 by omega,execute_ordinary_step _ _ _ _ _ _ fetchS opS,
        execute_ordinary_step _ _ _ _ _ _ fetchB op,execute_ordinary_step _ _ _ _ _ _ fj jump]
      simp [Execution.charge,instructionCycles,←Nat.add_assoc]
  · have more : i+1≠N := by dsimp [N] at *;omega
    have lr : latchReg s i=s := by unfold latchReg;rw [if_neg edge]
    have nextPC : firstWord4 ((i+1)%16384) = 45250*((i%16384)/4096)+firstWord (i%4096+1) := by
      unfold firstWord4
      by_cases e4 : i%4096=4095
      · rw [e4,show firstWord (4095+1)=45288 by decide,show ((i+1)%16384)/4096=(i%16384)/4096+1 by omega,
          show ((i+1)%16384)%4096=0 by omega,show firstWord 0=38 by decide]; omega
      · rw [show ((i+1)%16384)/4096=(i%16384)/4096 by omega,show ((i+1)%16384)%4096=i%4096+1 by omega]
    rw [edgeCost,if_neg edge,Nat.zero_add,startPC,if_neg more,nextPC,lr,←start]
    cases s;simp [MachineState.setPC,Execution.charge]

theorem packet_execute (s : MachineState) (i fuel : Nat) (hi : i<N) (r : Live s i) :
    execute image ((plan i).length+edgeCost i+fuel) s true =
      (do let t ← stepTrace s i; let z ← execute image fuel t true
          return z.charge ((plan i).length+edgeCost i+7*opCalls (plan i)) (opCalls (plan i))) := by
  have walkOK := walk_post _ _ _ (packet_walk s i hi r.toPacketRegs)
  have pc : s.pc=wordPC (firstWord4 (i%16384)) := by simpa [startPC,Nat.ne_of_lt hi] using r.pc
  rw [Nat.add_assoc,run_ops (plan i) _ _ s true pc (plan_fetch i) walkOK.1]
  simp only [stepTrace,bind_assoc,pure_bind]
  apply bind_congr_of_forall_mem_support; intro t hit
  have p := walkOK.2 t hit
  have pct : t.pc=wordPC (firstWord4 (i%16384)+(plan i).length) := by
    rw [ops_pc _ s t hit,pc];unfold wordPC;rw [←BitVec.ofNat_add];congr 1; omega
  rw [edge_run t i fuel hi pct p.1]
  simp only [bind_assoc,pure_bind]
  apply bind_congr;intro z;apply congrArg pure
  cases z;simp [Execution.charge,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

def scan : Nat → Nat → MachineState → OracleComp World MachineState
  | 0,_,s => pure s
  | n+1,i,s => do let t ← stepTrace s i; scan n (i+1) t

theorem scan_post (n i : Nat) (s t : MachineState) (bound : i+n≤N) (r : Live s i)
    (reach : t∈support (scan n i s)) : Live t (i+n) := by
  induction n generalizing i s with
  | zero => simp only [scan,support_pure,Set.mem_singleton_iff] at reach;subst t;exact r
  | succ n ih =>
    rw [scan,mem_support_bind_iff] at reach
    obtain ⟨u,h,rest⟩ := reach
    simpa only [show i+(n+1)=(i+1)+n by omega] using ih (i+1) u (by omega) (step_live s i (by omega) r u h) rest

theorem monotone_counts (i n : Nat) (bound : i+n≤N) :
    S i≤S (i+n) ∧ Q i≤Q (i+n) ∧ C i≤C (i+n) := by
  induction n with
  | zero => simp
  | succ k ih =>
    have h := ih (by omega)
    have g:=cumul (i+k) (by omega)
    rw [show i+(k+1)=i+k+1 by omega]
    unfold C at *;omega

attribute [local irreducible] stepTrace S Q C edgeCost opCalls plan

theorem run_scan (n i : Nat) (s : MachineState) (bound : i+n≤N) (r : Live s i) (fuel : Nat) :
    execute image (S (i+n)-S i+fuel) s true = (do
      let t ← scan n i s;let z ← execute image fuel t true
      return z.charge (C (i+n)-C i) (Q (i+n)-Q i)) := by
  induction n generalizing i s with
  | zero => simp [scan,Execution.charge]
  | succ n ih =>
    have h:=cumul i (by omega)
    have m:=monotone_counts (i+1) n (by omega)
    have next : i+(n+1)=(i+1)+n := by omega
    have price : C (i+1)=C i+((plan i).length+edgeCost i+7*opCalls (plan i)) := by
      unfold C;rw [h.1,h.2];omega
    rw [next,show S ((i+1)+n)-S i+fuel=(plan i).length+edgeCost i+(S ((i+1)+n)-S (i+1)+fuel) by omega,
      packet_execute s i _ (by omega) r]
    simp only [scan,bind_assoc]
    apply bind_congr_of_forall_mem_support;intro u reach
    rw [ih (i+1) u (by omega) (step_live s i (by omega) r u reach)]
    simp only [bind_assoc,pure_bind]
    apply bind_congr;intro last;apply bind_congr;intro out;apply congrArg pure
    cases out;simp only [Execution.charge,Execution.mk.injEq,true_and];constructor <;> omega

end TwoPermutationPrototype.Grouped
