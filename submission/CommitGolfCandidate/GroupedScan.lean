import CommitGolfCandidate.GroupedPacketRun
import CommitGolfCandidate.TwoPermutationCounted

namespace TwoPermutationPrototype.Grouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open TwoPermutationPrototype.QuartetCommit (qSource qSalt)
set_option maxRecDepth 18000
set_option maxHeartbeats 2000000

abbrev N : Nat := 16777216
def startPC (i : Nat) := if i=N then wordPC 45591 else wordPC (firstWord (i%4096))
def edgeCost (i : Nat) := if i%4096=4095 then if i+1=N then 1 else 2 else 0
def S (i : Nat) := 11*i+pairHeads i+(92*(i/4096)+rb (i%4096))+2*(i/4096)-(if i=N then 1 else 0)
def Q (i : Nat) := 2*i+heads i
def C (i : Nat) := S i+7*Q i

theorem calls_plan (i : Nat) : opCalls (plan i)=2+(if rank i=0 then 1 else 0) := by
  by_cases h : rank i=0 <;> by_cases p : pairPos i=0 <;> by_cases b : rebase (i%4096) <;>
    simp [plan,opCalls,Action.calls,within_rank,within_pair,h,p,b]

theorem length_plan (i : Nat) : (plan i).length=11+(if pairPos i=0 then 1 else 0)+(if rebase (i%4096) then 1 else 0) := by
  by_cases h : rank i=0 <;> by_cases p : pairPos i=0 <;> by_cases b : rebase (i%4096)
  all_goals simp [plan,within_rank,within_pair,h,p,b] <;> exact False.elim (h (pair_head i p))

theorem cumul (i : Nat) (hi : i<N) :
    S (i+1)=S i+(plan i).length+edgeCost i ∧ Q (i+1)=Q i+opCalls (plan i) := by
  have rs := rebases_succ i
  rw [calls_plan,length_plan];unfold S Q edgeCost
  rw [heads_succ,pair_succ,if_neg (Nat.ne_of_lt hi)]
  change i<16777216 at hi
  dsimp only [N]
  split_ifs at rs ⊢ <;> constructor <;> omega

def stepTrace (s : MachineState) (i : Nat) : OracleComp World MachineState := do
  let t ← runOps (plan i) s
  return t.setPC (startPC (i+1))

structure Live (s : MachineState) (i : Nat) extends PacketRegs s i where
  pc : s.pc=startPC i
  stop : s.getReg .x25=wordAddress (qSource 4194304)+2048
  out : s.getReg .x8=4294971392
  heapBase : s.getReg .x9=4294971424
  strideBase : s.getReg .x19=536870912
  quartet : s.getReg .x21=wordAddress (qSource 0)

theorem step_live (s : MachineState) (i : Nat) (hi : i<N) (r : Live s i)
    (u : MachineState) (reach : u∈support (stepTrace s i)) : Live u (i+1) := by
  simp only [stepTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reach
  obtain ⟨t,hit,rfl⟩ := reach
  have post := (walk_post _ _ _ (packet_walk s i hi r.toPacketRegs)).2 t hit
  obtain ⟨src,hp,stride,ct,buf,sel,sz,pr,out,hbase,st,q,stop⟩ := post
  exact ⟨⟨src,hp,stride,ct,buf,sel,sz,pr⟩,rfl,stop.trans r.stop,out.trans r.out,
    hbase.trans r.heapBase,st.trans r.strideBase,q.trans r.quartet⟩

theorem edge_run (s : MachineState) (i fuel : Nat) (hi : i<N)
    (start : s.pc=wordPC (firstWord (i%4096)+(plan i).length))
    (hp : s.getReg .x20=wordAddress (cursor (i+1)))
    (stop : s.getReg .x25=wordAddress (qSource 4194304)+2048) :
    execute image (edgeCost i+fuel) s true = (do
      let z ← execute image fuel (s.setPC (startPC (i+1))) true
      return z.charge (edgeCost i) 0) := by
  have len : (plan i).length=(packet (i%4096)).length := by
    have h:=congrArg List.length (plan_words i); simpa using h
  rw [len,←packet_next] at start
  by_cases edge : i%4096=4095
  · have pc : s.pc=wordPC 45356 := by rw [start,edge];rfl
    have fetchB : fetch image s=some (.base (.BEQ .x20 .x25 940)) := fetch_decoded s 45356 (by decide) pc _ (by decide +kernel)
    have cur : wordAddress (cursor (i+1))=wordAddress (qSource (1024*((i+1)/4096)))+2048 := by
      unfold cursor
      rw [show (i+1)%4096=0 by omega,rb_zero,Nat.mul_zero,Nat.add_zero]
      exact wordAddress_add ..
    have same : s.getReg .x20=s.getReg .x25 ↔ i+1=N := by
      rw [hp,stop,cur,BitVec.add_left_inj]
      constructor
      · intro h
        have w:=wordAddress_injective_of_bound (by unfold qSource;dsimp [N] at hi;omega) (by decide) h
        unfold qSource at w;dsimp [N];omega
      · intro h;rw [h];rfl
    by_cases last : i+1=N
    · have op : ordinaryStep s (.base (.BEQ .x20 .x25 940))=some (s.setPC (wordPC 45591)) := by
        simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,pc,same.mpr last,wordPC,signExtend13]
      rw [edgeCost,if_pos edge,if_pos last,startPC,if_pos last,Nat.add_comm 1 fuel,execute_ordinary_step _ _ _ _ _ _ fetchB op];rfl
    · let mid := s.setPC (wordPC 45357)
      have next : (i+1)%4096=0 := by omega
      have op : ordinaryStep s (.base (.BEQ .x20 .x25 940))=some mid := by
        simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,pc,mid,mt same.mp last];rfl
      have fj : fetch image mid=some (.base (.JAL .x0 1915808)) := fetch_decoded mid 45357 (by decide) rfl _ (by decide +kernel)
      have jump : ordinaryStep mid (.base (.JAL .x0 1915808))=some (s.setPC (wordPC 21)) := by
        simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,mid,MachineState.setPC,MachineState.setReg];rfl
      rw [edgeCost,if_pos edge,if_neg last,startPC,if_neg last,next,show firstWord 0=21 by decide,
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
  rw [edge_run t i fuel hi pct p.2.1 (p.2.2.2.2.2.2.2.2.2.2.2.2.trans r.stop)]
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
