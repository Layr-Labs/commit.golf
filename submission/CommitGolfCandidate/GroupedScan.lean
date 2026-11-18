import CommitGolfCandidate.GroupedPacketRun
import CommitGolfCandidate.TwoPermutationCounted

namespace TwoPermutationPrototype.Grouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open TwoPermutationPrototype.QuartetCommit (qSource qSalt)
set_option maxRecDepth 18000
set_option maxHeartbeats 2000000

abbrev N : Nat := 16777216
def startPC (i : Nat) := if i=N then wordPC 46158 else wordPC (firstWord (i%4096))
/-- The latch after slot 4095: `beq x10,x6,+8` and one of the two jumps. -/
def edgeCost (i : Nat) := if i%4096=4095 then 2 else 0
/-- Instructions (steps) before slot `i`: 45,764 per tile. -/
def S (i : Nat) := 45764*(i/4096)+firstWord (i%4096)-21
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

theorem first_word_ge (n : Nat) : 21≤firstWord n := by unfold firstWord chainedBefore;omega

theorem cumul (i : Nat) (hi : i<N) :
    S (i+1)=S i+(plan i).length+edgeCost i ∧ Q (i+1)=Q i+opCalls (plan i) := by
  constructor
  · have len : (plan i).length=(packet (i%4096)).length := by
      have h:=congrArg List.length (plan_words i);simpa using h
    rw [len];unfold S edgeCost
    have g0 := first_word_ge (i%4096)
    by_cases edge : i%4096=4095
    · rw [if_pos edge,show (i+1)/4096=i/4096+1 by omega,show (i+1)%4096=0 by omega,edge]
      have step := packet_next 4095 (by decide)
      have top : firstWord (4095+1)=45783 := by decide
      have zero : firstWord 0=21 := by decide
      rw [edge] at g0;omega
    · rw [if_neg edge,show (i+1)/4096=i/4096 by omega,show (i+1)%4096=i%4096+1 by omega]
      have step := packet_next (i%4096) (by omega)
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

def stepTrace (s : MachineState) (i : Nat) : OracleComp World MachineState := do
  let t ← runOps (plan i) s
  return t.setPC (startPC (i+1))

structure Live (s : MachineState) (i : Nat) extends PacketRegs s i where
  pc : s.pc=startPC i
  stop : s.getReg .x6=4294971448
  out : s.getReg .x8=4294971392
  heapBase : s.getReg .x9=4294971424
  strideBase : s.getReg .x19=536870912
  quartet : s.getReg .x21=wordAddress (qSource 0)

theorem step_live (s : MachineState) (i : Nat) (hi : i<N) (r : Live s i)
    (u : MachineState) (reach : u∈support (stepTrace s i)) : Live u (i+1) := by
  simp only [stepTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reach
  obtain ⟨t,hit,rfl⟩ := reach
  have post := (walk_post _ _ _ (packet_walk s i hi r.toPacketRegs)).2 t hit
  obtain ⟨src,k20,k23,ct,sel,sz,pr,out,hbase,st,q,k25,k26,k27,k28,k29,k30,stop,k1,k2,k3⟩ := post
  exact ⟨⟨src,k20.trans r.s0,k23.trans r.s1,k25.trans r.s2,k26.trans r.s3,k27.trans r.a0,k28.trans r.a1,
    k29.trans r.a2,k30.trans r.a3,k1.trans r.far,k2.trans r.close,k3.trans r.link,ct,sel,sz,pr⟩,rfl,stop.trans r.stop,
    out.trans r.out,
    hbase.trans r.heapBase,st.trans r.strideBase,q.trans r.quartet⟩

theorem edge_run (s : MachineState) (i fuel : Nat) (hi : i<N)
    (start : s.pc=wordPC (firstWord (i%4096)+(plan i).length))
    (hp : s.getReg .x10=wordAddress (entryWord (i+1)))
    (stop : s.getReg .x6=4294971448) :
    execute image (edgeCost i+fuel) s true = (do
      let z ← execute image fuel (s.setPC (startPC (i+1))) true
      return z.charge (edgeCost i) 0) := by
  have len : (plan i).length=(packet (i%4096)).length := by
    have h:=congrArg List.length (plan_words i); simpa using h
  rw [len,←packet_next _ (by omega)] at start
  by_cases edge : i%4096=4095
  · have pc : s.pc=wordPC 45783 := by rw [start,edge];rfl
    have fetchB : fetch image s=some (.base (.BEQ .x10 .x6 8)) := fetch_decoded s 45783 (by decide) pc _ (by decide +kernel)
    have head : entryWord (i+1)=msgWord (i+1)+7 := by
      have r0 : rank (i+1)=0 := by unfold rank;rw [show (i+1)%4096=0 by omega]
      unfold entryWord;rw [if_pos (by omega : rank (i+1)≤1)]
    have same : s.getReg .x10=s.getReg .x6 ↔ i+1=N := by
      rw [hp,stop,head,show (4294971448:Word)=wordAddress 536871431 from rfl]
      constructor
      · intro h
        have w:=wordAddress_injective_of_bound (by unfold msgWord;dsimp [N] at hi;omega) (by decide) h
        unfold msgWord at w;dsimp [N];omega
      · intro h;rw [h];rfl
    by_cases last : i+1=N
    · let mid := s.setPC (wordPC 45785)
      have op : ordinaryStep s (.base (.BEQ .x10 .x6 8))=some mid := by
        simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,pc,same.mpr last,wordPC,signExtend13,mid]
      have fj : fetch image mid=some (.base (.JAL .x0 1492)) := fetch_decoded mid 45785 (by decide) rfl _ (by decide +kernel)
      have jump : ordinaryStep mid (.base (.JAL .x0 1492))=some (s.setPC (wordPC 46158)) := by
        simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,mid,MachineState.setPC,MachineState.setReg];rfl
      rw [edgeCost,if_pos edge,startPC,if_pos last,
        show 2+fuel=(fuel+1)+1 by omega,execute_ordinary_step _ _ _ _ _ _ fetchB op,
        execute_ordinary_step _ _ _ _ _ _ fj jump]
      simp [Execution.charge,instructionCycles,←Nat.add_assoc]
    · let mid := s.setPC (wordPC 45784)
      have next : (i+1)%4096=0 := by omega
      have op : ordinaryStep s (.base (.BEQ .x10 .x6 8))=some mid := by
        simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,pc,mid,mt same.mp last];rfl
      have fj : fetch image mid=some (.base (.JAL .x0 1914100)) := fetch_decoded mid 45784 (by decide) rfl _ (by decide +kernel)
      have jump : ordinaryStep mid (.base (.JAL .x0 1914100))=some (s.setPC (wordPC 21)) := by
        simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,mid,MachineState.setPC,MachineState.setReg];rfl
      rw [edgeCost,if_pos edge,startPC,if_neg last,next,show firstWord 0=21 by decide,
        show 2+fuel=(fuel+1)+1 by omega,execute_ordinary_step _ _ _ _ _ _ fetchB op,
        execute_ordinary_step _ _ _ _ _ _ fj jump]
      simp [Execution.charge,instructionCycles,←Nat.add_assoc]
  · have more : i+1≠N := by dsimp [N] at *;omega
    have next : (i+1)%4096=i%4096+1 := by omega
    rw [edgeCost,if_neg edge,Nat.zero_add,startPC,if_neg more,next,←start]
    cases s;simp [MachineState.setPC,Execution.charge]

theorem packet_execute (s : MachineState) (i fuel : Nat) (hi : i<N) (r : Live s i) :
    execute image ((plan i).length+edgeCost i+fuel) s true =
      (do let t ← stepTrace s i; let z ← execute image fuel t true
          return z.charge ((plan i).length+edgeCost i+7*opCalls (plan i)) (opCalls (plan i))) := by
  have walkOK := walk_post _ _ _ (packet_walk s i hi r.toPacketRegs)
  have pc : s.pc=wordPC (firstWord (i%4096)) := by simpa [startPC,Nat.ne_of_lt hi] using r.pc
  rw [Nat.add_assoc,run_ops (plan i) _ _ s true pc (plan_fetch i) walkOK.1]
  simp only [stepTrace,bind_assoc,pure_bind]
  apply bind_congr_of_forall_mem_support; intro t hit
  have p := walkOK.2 t hit
  have pct : t.pc=wordPC (firstWord (i%4096)+(plan i).length) := by
    rw [ops_pc _ s t hit,pc];unfold wordPC;rw [←BitVec.ofNat_add];congr 1 <;> omega
  rw [edge_run t i fuel hi pct p.1 (p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.trans r.stop)]
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
