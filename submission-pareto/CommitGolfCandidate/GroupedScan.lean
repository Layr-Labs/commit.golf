import CommitGolfCandidate.GroupedPacketRun
import CommitGolfCandidate.TwoPermutationCounted

namespace TwoPermutationPrototype.Grouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open TwoPermutationPrototype.QuartetCommit (qSource qSalt)
set_option maxRecDepth 18000
set_option maxHeartbeats 2000000

abbrev N : Nat := 16777216
def startPC (i : Nat) := if i=N then wordPC 181041 else wordPC (firstWord4 (i%16384))
/-- The latch after slot 16383: `bge x10,x14,+12` (2 cycles on loop, 1 on final exit). -/
def edgeCost (i : Nat) := if i%16384=16383 then (if i+1=N then 1 else 2) else 0
/-- Instructions (steps) before slot `i`: 181,002 per 4-tile pass, minus 1 on final exit. -/
def S (i : Nat) := 181002*(i/16384)+45250*((i%16384)/4096)+firstWord (i%4096)-38-(if i=N then 1 else 0)
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

/-- The latch is a pure `bge x10,x14,+12`, so it leaves all registers unchanged. -/
def latchReg (t : MachineState) (i : Nat) : MachineState := t

theorem latch_getReg (t : MachineState) (i : Nat) (r : Reg) : (latchReg t i).getReg r=t.getReg r := rfl

theorem latch_mem (t : MachineState) (i : Nat) : (latchReg t i).mem=t.mem := by
  rfl

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
  have lg : ∀ reg, ((latchReg t i).setPC (startPC (i+1))).getReg reg=t.getReg reg :=
    fun reg => MachineState.getReg_setPC.trans (latch_getReg t i reg)
  obtain ⟨src,k20,k23,ct,sel,sz,pr,thr,k8,k9,k19,k21,k25,k26,k27,k28,k29,k30,k6,k1,k2,k3,k18,k22,k4,k7,k31⟩ := post
  have L (reg : Reg) {v : Word} (k : t.getReg reg=v) :
      ((latchReg t i).setPC (startPC (i+1))).getReg reg=v := (lg reg).trans k
  exact ⟨⟨L _ src,L _ (k20.trans r.s0),L _ (k23.trans r.s1),
    L _ (k25.trans r.s2),L _ (k26.trans r.s3),L _ (k27.trans r.a0),
    L _ (k28.trans r.a1),L _ (k29.trans r.a2),L _ (k30.trans r.a3),
    L _ (k8.trans r.o0),L _ (k9.trans r.o1),L _ (k18.trans r.o2),
    L _ (k19.trans r.o3),L _ (k21.trans r.b0),L _ (k22.trans r.b1),
    L _ (k4.trans r.b2),L _ (k7.trans r.b3),L _ (k1.trans r.far),
    L _ (k2.trans r.close),L _ (k31.trans r.farOdd),L _ (k6.trans r.closeOdd),
    L _ (k3.trans r.link),L _ ct,L _ sel,L _ sz,L _ pr,L _ (thr.trans r.threshold)⟩,rfl⟩

private theorem word_slt_threshold (a : Nat) (ha : a<2^29) :
    BitVec.slt (wordAddress a) (wordAddress (2^29)) = true := by
  unfold wordAddress
  rw [BitVec.slt_eq_decide]
  simp only [decide_eq_true_eq]
  rw [BitVec.toInt_ofNat', BitVec.toInt_ofNat']
  norm_num only [Nat.cast_mul,Nat.cast_ofNat]
  rw [Int.bmod_eq_emod,Int.bmod_eq_emod]
  norm_num at *
  have hmod : (8*(a:Int)) % (18446744073709551616:Int) = 8*(a:Int) := by
    rw [Int.emod_eq_of_lt]
    · norm_num
    · omega
  rw [hmod]
  have hsmall : ¬ (9223372036854775808:Int) ≤ 8*(a:Int) := by omega
  simp [hsmall]
  omega

theorem edge_run (s : MachineState) (i fuel : Nat) (hi : i<N)
    (start : s.pc=wordPC (firstWord4 (i%16384)+(plan i).length))
    (hp : s.getReg .x10=wordAddress (entryWord (i+1)))
    (h14 : s.getReg .x14=wordAddress (2^29)) :
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
    have fetchB : fetch image s=some (.base (.BGE .x10 .x14 12)) :=
      fetch_decoded s 181038 (by decide) pc _ (by decide +kernel)
    have head : entryWord (i+1)=msgWord (i+1)+7 := by
      have r0 : rank (i+1)=0 := by unfold rank;rw [show (i+1)%4096=0 by omega]
      unfold entryWord;rw [if_pos (by omega : rank (i+1)≤1)]
    by_cases last : i+1=N
    · have slt : BitVec.slt (s.getReg .x10) (s.getReg .x14)=false := by
        rw [hp,h14,head,last]
        unfold wordAddress msgWord N
        decide
      have op : ordinaryStep s (.base (.BGE .x10 .x14 12))=
          some ((latchReg s i).setPC (wordPC 181041)) := by
        have tgt : s.pc+signExtend13 (12#13)=wordPC 181041 := by rw [pc];decide
        simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,slt,tgt,latchReg]
      rw [edgeCost,if_pos edge,if_pos last,startPC,if_pos last,
        show 1+fuel=fuel+1 by omega,execute_ordinary_step _ _ _ _ _ _ fetchB op]
      simp [Execution.charge,instructionCycles]
    · have a_lt : msgWord (i+1)+7<2^29 := by
        have align : (i+1)%16384=0 := by omega
        have dm := Nat.div_add_mod (i+1) 16384
        unfold msgWord
        dsimp [N] at hi last
        omega
      have slt : BitVec.slt (s.getReg .x10) (s.getReg .x14)=true := by
        rw [hp,h14,head]
        exact word_slt_threshold (msgWord (i+1)+7) a_lt
      let mid := s.setPC (wordPC 181039)
      have op : ordinaryStep s (.base (.BGE .x10 .x14 12))=some mid := by
        have npc : s.pc+(4#64)=wordPC 181039 := by rw [pc];decide
        simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,slt,mid,npc]
      have fj : fetch image mid=some (.base (.JAL .x0 (-724004))) :=
        fetch_decoded mid 181039 (by decide) (by change wordPC 181039 = 728252#64; decide) _ (by decide +kernel)
      have jump : ordinaryStep mid (.base (.JAL .x0 (-724004)))=some ((latchReg s i).setPC (wordPC 38)) := by
        have tgt : wordPC 181039+signExtend21 (1373148#21)=wordPC 38 := by
          decide +kernel
        simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,tgt,mid,MachineState.setReg,MachineState.setPC,latchReg]
      have next : (i+1)%16384=0 := by omega
      rw [edgeCost,if_pos edge,if_neg last,startPC,if_neg last,next,show firstWord4 0=38 by decide,
        show 2+fuel=(fuel+1)+1 by omega,execute_ordinary_step _ _ _ _ _ _ fetchB op,
        execute_ordinary_step _ _ _ _ _ _ fj jump]
      simp [Execution.charge,instructionCycles,←Nat.add_assoc]
  · have more : i+1≠N := by dsimp [N] at *;omega
    have lr : latchReg s i=s := rfl
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
  obtain ⟨p10,p20,p23,pct,p5,p11,p13,p14,pr8,pr9,pr19,pr21,pr25,pr26,pr27,pr28,pr29,pr30,p6,p1,p2,p3,p18,p22,p4,p7,p31⟩ := walkOK.2 t hit
  have hpct : t.pc=wordPC (firstWord4 (i%16384)+(plan i).length) := by
    rw [ops_pc _ s t hit,pc];unfold wordPC;rw [←BitVec.ofNat_add];congr 1; omega
  rw [edge_run t i fuel hi hpct p10 (p14.trans r.threshold)]
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
