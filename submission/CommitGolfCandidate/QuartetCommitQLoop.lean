import CommitGolfCandidate.QuartetCommitQStep
import CommitGolfCandidate.TwoPermutationCounted

namespace TwoPermutationPrototype.QuartetCommit
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.RV64
set_option maxRecDepth 8192
set_option maxHeartbeats 950000
attribute [local irreducible] image execute qAfter

def qUnits : Nat → Nat → MachineState → OracleComp World MachineState
  | 0,_,s => pure s
  | count+1,g,s => do
    let reply ← World.query (.inr (.inr (.inl (quadArgument s g))))
    qUnits count (g+1) (qAfter s g reply)

theorem q_segment (s : MachineState) (g slot count fuel : Nat)
    (limit : g+count≤4194304) (inside : slot+count≤341) (r : QRegs s g) (pc : s.pc=quadPC slot) :
    execute image (3*count+fuel) s true = (do
      let mid ← qUnits count g s
      let e ← execute image fuel mid true
      return e.charge (10*count) count) := by
  induction count generalizing s g slot with
  | zero => simp [qUnits,Execution.charge]
  | succ n ih =>
    let pos : Fin 341 := ⟨slot, by omega⟩
    rw [show 3*(n+1)+fuel=3+(3*n+fuel) by omega,q_unit_run s g pos _ (by omega) r pc]
    simp only [qUnits,bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro answer _
    have afterPC := (q_post_pc s g answer).trans ((congrArg (·+12) pc).trans (q_next_pc slot))
    rw [ih _ (g+1) (slot+1) (by omega) (by omega) (q_next_regs s g answer r) afterPC]
    simp [Execution.charge,Nat.mul_succ,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

theorem q_segment_post (s : MachineState) (g slot count : Nat)
    (r : QRegs s g) (pc : s.pc=quadPC slot)
    {out : MachineState} (hit : out ∈ support (qUnits count g s)) :
    QRegs out (g+count) ∧ out.pc=quadPC (slot+count) := by
  induction count generalizing s g slot with
  | zero => simp only [qUnits,support_pure,Set.mem_singleton_iff] at hit;subst out;exact ⟨r,pc⟩
  | succ n ih =>
    simp only [qUnits,mem_support_bind_iff] at hit
    obtain ⟨answer,_,rest⟩ := hit
    have afterPC := (q_post_pc s g answer).trans ((congrArg (·+12) pc).trans (q_next_pc slot))
    simpa only [Nat.add_assoc,Nat.add_comm 1 n] using ih _ (g+1) (slot+1) (q_next_regs s g answer r) afterPC rest

def qLatchPC (k : Nat) : Word := if k+1=12300 then wordPC 46765 else quadPC 0

theorem q_branch (s : MachineState) (g fuel : Nat) (bound : g≤4194304)
    (r : QRegs s g) (pc : s.pc=quadPC 341) :
    execute image ((if g=4194304 then 2 else 1)+fuel) s true = (do
      let e ← execute image fuel (s.setPC (if g=4194304 then wordPC 46765 else quadPC 0)) true
      return e.charge (if g=4194304 then 2 else 1) 0) := by
  have addr : s.pc=wordPC 46263 := pc
  have eq : s.getReg .x10 = s.getReg .x24 ↔ g=4194304 := by
    rw [r.source,r.stop];constructor
    · intro h
      have j := wordAddress_injective_of_bound (a:=qSource g) (b:=qSource 4194304)
        (by unfold qSource;omega) (by decide) h
      unfold qSource at j;omega
    · intro h;rw [h]
  by_cases last : g=4194304
  · let mid := s.setPC (wordPC 46264)
    have step : ordinaryStep s (.base (.BNE .x10 .x24 4100))=some mid := by
      simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,addr,eq.mpr last,mid,wordPC]
    have jump : ordinaryStep mid (.base (.JAL .x0 2004))=some (s.setPC (wordPC 46765)) := by
      simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,mid,MachineState.setReg,MachineState.setPC];rfl
    rw [if_pos last,show 2+fuel=(fuel+1)+1 by omega,
      CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (fetch_quad_branch s addr) step,
      CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (fetch_quad_jump mid rfl) jump]
    simp [last,instructionCycles,Execution.charge,←Nat.add_assoc]
  · have neq : s.getReg .x10≠s.getReg .x24 := fun same => last (eq.mp same)
    have step : ordinaryStep s (.base (.BNE .x10 .x24 4100))=some (s.setPC (quadPC 0)) := by
      simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,addr,neq,signExtend13,wordPC,quadPC]
    rw [if_neg last,Nat.add_comm 1 fuel,
      CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (fetch_quad_branch s addr) step]
    simp [last,instructionCycles]

def qGroups : Nat → Nat → MachineState → OracleComp World MachineState
  | 0,_,s => pure s
  | count+1,k,s => do
    let mid ← qUnits 341 (4+341*k) s
    qGroups count (k+1) (mid.setPC (qLatchPC k))

def qPhase (s : MachineState) : OracleComp World MachineState := do
  let mid ← qUnits 4 0 (s.setPC (quadPC 337))
  qGroups 12300 0 (mid.setPC (quadPC 0))

theorem q_group_run (s : MachineState) (remaining k fuel : Nat) (finish : k+remaining=12300)
    (r : QRegs s (4+341*k)) (pc : 0<remaining → s.pc=quadPC 0) :
    execute image ((1024*remaining+(if remaining=0 then 0 else 1))+fuel) s true = (do
      let out ← qGroups remaining k s
      let e ← execute image fuel out true
      return e.charge (3411*remaining+(if remaining=0 then 0 else 1)) (341*remaining)) := by
  induction remaining generalizing s k with
  | zero => simp [qGroups,Execution.charge]
  | succ n ih =>
    have arithmetic : 1024*(n+1)+1=1023+(if 4+341*(k+1)=4194304 then 2 else 1)+(1024*n+(if n=0 then 0 else 1)) ∧
        3411*(n+1)+1=3410+(if 4+341*(k+1)=4194304 then 2 else 1)+(3411*n+(if n=0 then 0 else 1)) := by
      split <;> split <;> constructor <;> omega
    have atStart := pc (by omega)
    rw [if_neg (by omega : n+1≠0),show (1024*(n+1)+1)+fuel=3*341+((if 4+341*(k+1)=4194304 then 2 else 1)+((1024*n+(if n=0 then 0 else 1))+fuel)) by omega,
      q_segment s (4+341*k) 0 341 _ (by omega) (by decide) r atStart]
    simp only [qGroups,bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro mid hit
    obtain ⟨next,atLatch⟩ := q_segment_post s (4+341*k) 0 341 r atStart hit
    have nextRegs : QRegs mid (4+341*(k+1)) := by simpa only [Nat.mul_succ,Nat.add_assoc] using next
    rw [q_branch mid (4+341*(k+1)) _ (by omega) nextRegs atLatch]
    have test : (4+341*(k+1)=4194304) ↔ k+1=12300 := by omega
    simp only [test]
    let after := mid.setPC (qLatchPC k)
    have regs : QRegs after (4+341*(k+1)) := ⟨nextRegs.source,nextRegs.dest,nextRegs.selector,
      nextRegs.size,nextRegs.primitive,nextRegs.stop⟩
    have again (more : 0<n) : after.pc=quadPC 0 := by change qLatchPC k=_;rw [qLatchPC,if_neg (by omega)]
    simp only [bind_assoc,pure_bind]
    change (do let e ← execute image ((1024*n+(if n=0 then 0 else 1))+fuel) after true
               return e.charge (if k+1=12300 then 2 else 1) 0 |>.charge 3410 341) = _
    rw [ih after (k+1) (by omega) regs again]
    simp only [bind_assoc,pure_bind]
    apply bind_congr
    intro out
    apply bind_congr
    intro e
    simp only [Execution.charge]
    simp only [test] at arithmetic
    have hc : 3410 + ((if k+1=12300 then 2 else 1) + ((3411*n+(if n=0 then 0 else 1))+e.cycles)) = 3411*(n+1)+1+e.cycles := by omega
    have ho : 341+(0+(341*n+e.oracleCalls))=341*(n+1)+e.oracleCalls := by omega
    rw [hc,ho]

theorem entire_quartet_phase (s : MachineState) (fuel : Nat) (r : QRegs s 0) (pc : s.pc=wordPC 45227) :
    execute image (12595215+fuel) s true = (do
      let out ← qPhase s
      let e ← execute image fuel out true
      return e.charge 41955343 4194304) := by
  let entry := s.setPC (quadPC 337)
  have step : ordinaryStep s (.base (.JAL .x0 4096))=some entry := by
    simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,pc,entry,MachineState.setReg,MachineState.setPC];rfl
  have regs : QRegs entry 0 := ⟨r.source,r.dest,r.selector,r.size,r.primitive,r.stop⟩
  rw [show 12595215+fuel=(12+(1+(12595201+fuel)))+1 by omega,
    CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (fetch_quad_entry s pc) step,
    q_segment entry 0 337 4 _ (by decide) (by decide) regs rfl]
  simp only [qPhase,bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro mid hit
  obtain ⟨next,atLatch⟩ := q_segment_post entry 0 337 4 regs rfl hit
  have branch := q_branch mid 4 (12595201+fuel) (by decide) next atLatch
  norm_num at branch
  rw [branch]
  let after := mid.setPC (quadPC 0)
  have nextRegs : QRegs after (4+341*0) := ⟨next.source,next.dest,next.selector,next.size,next.primitive,next.stop⟩
  have groups := q_group_run after 12300 0 fuel (by decide) nextRegs (fun _ => rfl)
  norm_num at groups
  rw [groups]
  simp [Execution.charge,instructionCycles,after,←Nat.add_assoc]

end TwoPermutationPrototype.QuartetCommit
