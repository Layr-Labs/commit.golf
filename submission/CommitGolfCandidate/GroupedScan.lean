import CommitGolfCandidate.GroupedPacketRun
import CommitGolfCandidate.TwoPermutationCounted

/-! Pair-heads leaf body: the scan over all 2^23 pair packets, with exact step, call and cycle counts. -/

namespace TwoPermutationPrototype.Grouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open TwoPermutationPrototype.QuartetCommit (qSource qSalt)
set_option maxRecDepth 18000
set_option maxHeartbeats 2000000

/-- Number of pair packets. -/
abbrev NP : Nat := 8388608
def startPC (P : Nat) := if P=NP then wordPC 45591 else wordPC (pairWord (P%2048))
/-- The latch after the last pair of a body: `beq s4,s9` then one `jal` (back to word 21, or on to word 45,591). -/
def edgeCost (P : Nat) := if P%2048=2047 then 2 else 0
/-- Head pairs among the first `P` pairs (373 per body). -/
def headCount (P : Nat) := 373*(P/2048)+headsBefore (P%2048)
def S (P : Nat) := 22*P-3*headCount P+P/16+2*(P/2048)
def Q (P : Nat) := 4*P+headCount P
def C (P : Nat) := S P+7*Q P

theorem head_count_succ (P : Nat) : headCount (P+1)=headCount P+(if pairHead (P%2048) then 1 else 0) := by
  unfold headCount
  by_cases e : P%2048=2047
  · have h1 : (P+1)/2048=P/2048+1 := by omega
    have h2 : (P+1)%2048=0 := by omega
    rw [h1,h2,e,if_neg (by decide : ¬pairHead 2047),show headsBefore 0=0 by decide,show headsBefore 2047=373 by decide]
    omega
  · have h1 : (P+1)/2048=P/2048 := by omega
    have h2 : (P+1)%2048=P%2048+1 := by omega
    rw [h1,h2,heads_before_succ]; omega

theorem head_count_le (P : Nat) : headCount P ≤ P := by
  have := heads_before_le (P%2048)
  have b : headsBefore (P%2048) ≤ 373 := by
    have := heads_before_le (P%2048); unfold headsBefore; split_ifs <;> omega
  unfold headCount; omega

theorem calls_plan (P : Nat) : opCalls (pairPlan P)=4+(if pairHead (P%2048) then 1 else 0) := by
  by_cases h : pairHead (P%2048) <;> by_cases k : P%16=15 <;>
    simp [pairPlan,opCalls,Action.calls,h,k]

theorem length_plan (P : Nat) :
    (pairPlan P).length=22-(if pairHead (P%2048) then 3 else 0)+(if P%16=15 then 1 else 0) := by
  have len := congrArg List.length (pair_plan_words P)
  simp only [List.length_map] at len
  rw [len,pair_packet_length,show P%2048%16=P%16 by omega]

theorem cumul (P : Nat) (hP : P<NP) :
    S (P+1)=S P+(pairPlan P).length+edgeCost P ∧ Q (P+1)=Q P+opCalls (pairPlan P) := by
  rw [calls_plan,length_plan]; unfold S Q edgeCost
  have hc := head_count_le P
  rw [head_count_succ]
  split_ifs <;> constructor <;> omega

def stepTrace (s : MachineState) (P : Nat) : OracleComp World MachineState := do
  let t ← runOps (pairPlan P) s
  return t.setPC (startPC (P+1))

structure Live (s : MachineState) (P : Nat) extends PairRegs s P where
  pc : s.pc=startPC P
  stop : s.getReg .x25=wordAddress (qSource 4194304)+2048
  out : s.getReg .x8=4294971392
  heapBase : s.getReg .x9=4294971424
  strideBase : s.getReg .x19=536870912
  quartet : s.getReg .x21=wordAddress (qSource 0)

theorem anchor_next (P : Nat) (h : ¬pairHead ((P+1)%2048)) : anchorWord (P+1)=anchorWord P := by
  unfold anchorWord replyWord headPair groupK pairRank msgWord
  unfold pairHead at h
  have e : (P+1)%2048=P%2048+1 := by omega
  rw [e] at h ⊢
  split_ifs <;> omega

theorem step_live (s : MachineState) (P : Nat) (hP : P<NP) (r : Live s P)
    (u : MachineState) (reach : u∈support (stepTrace s P)) : Live u (P+1) := by
  simp only [stepTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reach
  obtain ⟨t,hit,rfl⟩ := reach
  have post := (walk_post _ _ _ (pair_walk s P hP r.toPairRegs)).2 t hit
  obtain ⟨msg,hp,stride,ct,anc,sel,sz,pr,out,hbase,st,q,stop⟩ := post
  refine ⟨⟨?_,?_,stride,ct,?_,sel,sz,pr⟩,rfl,stop.trans r.stop,out.trans r.out,
    hbase.trans r.heapBase,st.trans r.strideBase,q.trans r.quartet⟩
  · simpa only [MachineState.getReg_setPC,show 2*(P+1)=2*P+2 by omega] using msg
  · simpa only [MachineState.getReg_setPC,show 2*(P+1)=2*P+2 by omega] using hp
  · intro nh; simpa only [MachineState.getReg_setPC,anchor_next P nh] using anc

theorem edge_run (s : MachineState) (P fuel : Nat) (hP : P<NP)
    (start : s.pc=wordPC (pairWord (P%2048)+(pairPlan P).length))
    (hp : s.getReg .x20=wordAddress (cursor (2*P+2)))
    (stop : s.getReg .x25=wordAddress (qSource 4194304)+2048) :
    execute image (edgeCost P+fuel) s true = (do
      let z ← execute image fuel (s.setPC (startPC (P+1))) true
      return z.charge (edgeCost P) 0) := by
  have len : (pairPlan P).length=(pairPacket (P%2048)).length := by
    have h := congrArg List.length (pair_plan_words P); simpa using h
  rw [len,←pair_word_next] at start
  by_cases edge : P%2048=2047
  · have pc : s.pc=wordPC 44086 := by rw [start,edge,pair_word_latch]
    have fetchB : fetch image s=some (.base (.BEQ .x20 .x25 8)) :=
      fetch_decoded s 44086 (by decide) pc _ (by decide +kernel)
    have same : s.getReg .x20=s.getReg .x25 ↔ P+1=NP := by
      rw [hp,stop,show wordAddress (cursor (2*P+2))=wordAddress (qSource (8*((2*P+2)/32)))+2048 from wordAddress_add ..,
        BitVec.add_left_inj]
      constructor
      · intro h
        have w := wordAddress_injective_of_bound (by unfold qSource; dsimp [NP] at hP; omega) (by decide) h
        unfold qSource at w; dsimp [NP]; omega
      · intro h
        have : (2*P+2)/32=524288 := by dsimp [NP] at h; omega
        rw [this]
    by_cases last : P+1=NP
    · let mid := s.setPC (wordPC 44088)
      have op : ordinaryStep s (.base (.BEQ .x20 .x25 8))=some mid := by
        simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,pc,same.mpr last,mid,wordPC,signExtend13]
      have fj : fetch image mid=some (.base (.JAL .x0 6012)) := fetch_decoded mid 44088 (by decide) rfl _ (by decide +kernel)
      have jump : ordinaryStep mid (.base (.JAL .x0 6012))=some (s.setPC (wordPC 45591)) := by
        simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,mid,MachineState.setPC,MachineState.setReg]; rfl
      rw [edgeCost,if_pos edge,startPC,if_pos last,show 2+fuel=(fuel+1)+1 by omega,
        execute_ordinary_step _ _ _ _ _ _ fetchB op,execute_ordinary_step _ _ _ _ _ _ fj jump]
      simp [Execution.charge,instructionCycles,←Nat.add_assoc]
    · let mid := s.setPC (wordPC 44087)
      have next : (P+1)%2048=0 := by omega
      have op : ordinaryStep s (.base (.BEQ .x20 .x25 8))=some mid := by
        simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,pc,mid,mt same.mp last]; rfl
      have fj : fetch image mid=some (.base (.JAL .x0 1920888)) := fetch_decoded mid 44087 (by decide) rfl _ (by decide +kernel)
      have jump : ordinaryStep mid (.base (.JAL .x0 1920888))=some (s.setPC (wordPC 21)) := by
        simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,mid,MachineState.setPC,MachineState.setReg]; rfl
      rw [edgeCost,if_pos edge,startPC,if_neg last,next,show pairWord 0=21 by decide,
        show 2+fuel=(fuel+1)+1 by omega,execute_ordinary_step _ _ _ _ _ _ fetchB op,
        execute_ordinary_step _ _ _ _ _ _ fj jump]
      simp [Execution.charge,instructionCycles,←Nat.add_assoc]
  · have more : P+1≠NP := by dsimp [NP] at *; omega
    have next : (P+1)%2048=P%2048+1 := by omega
    rw [edgeCost,if_neg edge,Nat.zero_add,startPC,if_neg more,next,←start]
    cases s; simp [MachineState.setPC,Execution.charge]

theorem packet_execute (s : MachineState) (P fuel : Nat) (hP : P<NP) (r : Live s P) :
    execute image ((pairPlan P).length+edgeCost P+fuel) s true =
      (do let t ← stepTrace s P; let z ← execute image fuel t true
          return z.charge ((pairPlan P).length+edgeCost P+7*opCalls (pairPlan P)) (opCalls (pairPlan P))) := by
  have walkOK := walk_post _ _ _ (pair_walk s P hP r.toPairRegs)
  have pc : s.pc=wordPC (pairWord (P%2048)) := by simpa [startPC,Nat.ne_of_lt hP] using r.pc
  rw [Nat.add_assoc,run_ops (pairPlan P) _ _ s true pc (pair_plan_fetch P) walkOK.1]
  simp only [stepTrace,bind_assoc,pure_bind]
  apply bind_congr_of_forall_mem_support; intro t hit
  have p := walkOK.2 t hit
  have pct : t.pc=wordPC (pairWord (P%2048)+(pairPlan P).length) := by
    have wb := pair_word_bound (P%2048) (by omega)
    have lb : (pairPlan P).length ≤ 23 := by rw [length_plan]; split_ifs <;> omega
    rw [ops_pc _ s t hit,pc]; unfold wordPC; rw [←BitVec.ofNat_add]; congr 1 <;> omega
  rw [edge_run t P fuel hP pct p.2.1 (p.2.2.2.2.2.2.2.2.2.2.2.2.trans r.stop)]
  simp only [bind_assoc,pure_bind]
  apply bind_congr; intro z; apply congrArg pure
  cases z; simp [Execution.charge,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

def scan : Nat → Nat → MachineState → OracleComp World MachineState
  | 0,_,s => pure s
  | n+1,P,s => do let t ← stepTrace s P; scan n (P+1) t

theorem scan_post (n P : Nat) (s t : MachineState) (bound : P+n≤NP) (r : Live s P)
    (reach : t∈support (scan n P s)) : Live t (P+n) := by
  induction n generalizing P s with
  | zero => simp only [scan,support_pure,Set.mem_singleton_iff] at reach; subst t; exact r
  | succ n ih =>
    rw [scan,mem_support_bind_iff] at reach
    obtain ⟨u,h,rest⟩ := reach
    simpa only [show P+(n+1)=(P+1)+n by omega] using ih (P+1) u (by omega) (step_live s P (by omega) r u h) rest

theorem monotone_counts (P n : Nat) (bound : P+n≤NP) :
    S P≤S (P+n) ∧ Q P≤Q (P+n) ∧ C P≤C (P+n) := by
  induction n with
  | zero => simp
  | succ k ih =>
    have h := ih (by omega)
    have g := cumul (P+k) (by omega)
    rw [show P+(k+1)=P+k+1 by omega]
    unfold C at *; omega

attribute [local irreducible] stepTrace S Q C edgeCost opCalls pairPlan

theorem run_scan (n P : Nat) (s : MachineState) (bound : P+n≤NP) (r : Live s P) (fuel : Nat) :
    execute image (S (P+n)-S P+fuel) s true = (do
      let t ← scan n P s; let z ← execute image fuel t true
      return z.charge (C (P+n)-C P) (Q (P+n)-Q P)) := by
  induction n generalizing P s with
  | zero => simp [scan,Execution.charge]
  | succ n ih =>
    have h := cumul P (by omega)
    have m := monotone_counts (P+1) n (by omega)
    have next : P+(n+1)=(P+1)+n := by omega
    have price : C (P+1)=C P+((pairPlan P).length+edgeCost P+7*opCalls (pairPlan P)) := by
      unfold C; rw [h.1,h.2]; omega
    rw [next,show S ((P+1)+n)-S P+fuel=(pairPlan P).length+edgeCost P+(S ((P+1)+n)-S (P+1)+fuel) by omega,
      packet_execute s P _ (by omega) r]
    simp only [scan,bind_assoc]
    apply bind_congr_of_forall_mem_support; intro u reach
    rw [ih (P+1) u (by omega) (step_live s P (by omega) r u reach)]
    simp only [bind_assoc,pure_bind]
    apply bind_congr; intro last; apply bind_congr; intro out; apply congrArg pure
    cases out; simp only [Execution.charge,Execution.mk.injEq,true_and]; constructor <;> omega

theorem totals : S NP=180498432 ∧ Q NP=35082240 ∧ C NP=426074112 := by
  unfold C S Q headCount headsBefore; decide

end TwoPermutationPrototype.Grouped
