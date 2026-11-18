import CommitGolfCandidate.GroupedQStep
import CommitGolfCandidate.TwoPermutationCounted

namespace TwoPermutationPrototype.Grouped
open TwoPermutationPrototype.QuartetCommit (qSource qUpper qLeaf PaddedLeaves quad_input_words quadWords)
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
    (limit : g+count≤4194304) (inside : slot+count≤8192) (r : QRegs s g) (pc : s.pc=quadPC slot) :
    execute image (3*count+fuel) s true = (do
      let mid ← qUnits count g s
      let e ← execute image fuel mid true
      return e.charge (10*count) count) := by
  induction count generalizing s g slot with
  | zero => simp [qUnits,Execution.charge]
  | succ n ih =>
    let pos : Fin 8192 := ⟨slot, by omega⟩
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

def qLatchCost (k : Nat) := if k+1=512 then 1 else 2
def qLatchPC (k : Nat) : Word := if k+1=512 then wordPC 70172 else quadPC 0

theorem q_latch (s : MachineState) (k fuel : Nat) (bound : k<512)
    (r : QRegs s (8192*(k+1))) (pc : s.pc=quadPC 8192) :
    execute image (qLatchCost k+fuel) s true = (do
      let e ← execute image fuel (s.setPC (qLatchPC k)) true; return e.charge (qLatchCost k) 0) := by
  have addr : s.pc=wordPC 70170 := pc
  have eq : s.getReg .x10 = s.getReg .x24 ↔ k+1=512 := by
    rw [r.source,r.stop];constructor
    · intro h
      have j := wordAddress_injective_of_bound (a:=qSource (8192*(k+1))) (b:=qSource 4194304)
        (by unfold qSource;omega) (by decide) h
      unfold qSource at j;omega
    · intro h;rw [h]
  by_cases last : k+1=512
  · have step : ordinaryStep s (.base (.BEQ .x10 .x24 8))=some (s.setPC (wordPC 70172)) := by
      simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,addr,eq.mpr last,signExtend13,wordPC]
    rw [qLatchCost,if_pos last,qLatchPC,if_pos last,Nat.add_comm 1 fuel,
      CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (fetch_quad_branch s addr) step];rfl
  · let mid := s.setPC (wordPC 70171)
    have neq : s.getReg .x10≠s.getReg .x24 := fun same => last (eq.mp same)
    have step : ordinaryStep s (.base (.BEQ .x10 .x24 8))=some mid := by
      simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,addr,neq,mid,wordPC]
    have jump : ordinaryStep mid (.base (.JAL .x0 1998844))=some (s.setPC (quadPC 0)) := by
      simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,mid,MachineState.setReg,MachineState.setPC];rfl
    rw [qLatchCost,if_neg last,qLatchPC,if_neg last,show 2+fuel=(fuel+1)+1 by omega,
      CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (fetch_quad_branch s addr) step,
      CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (fetch_quad_jump mid rfl) jump]
    simp [instructionCycles,Execution.charge,←Nat.add_assoc]

def qGroups : Nat → Nat → MachineState → OracleComp World MachineState
  | 0,_,s => pure s
  | count+1,k,s => do
    let mid ← qUnits 8192 (8192*k) s
    qGroups count (k+1) (mid.setPC (qLatchPC k))

attribute [local irreducible] qUnits

theorem q_group_run (s : MachineState) (remaining k fuel : Nat) (finish : k+remaining=512)
    (r : QRegs s (8192*k)) (pc : 0<remaining → s.pc=quadPC 0) :
    execute image ((24578*remaining-1)+fuel) s true = (do
      let out ← qGroups remaining k s
      let e ← execute image fuel out true
      return e.charge (81922*remaining-1) (8192*remaining)) := by
  induction remaining generalizing s k with
  | zero => simp [qGroups,Execution.charge]
  | succ n ih =>
    have arithmetic : 24578*(n+1)-1=24576+qLatchCost k+(24578*n-1) ∧
        81922*(n+1)-1=81920+qLatchCost k+(81922*n-1) := by
      unfold qLatchCost;split <;> constructor <;> omega
    have atStart := pc (by omega)
    rw [show (24578*(n+1)-1)+fuel=3*8192+(qLatchCost k+((24578*n-1)+fuel)) by omega,
      q_segment s (8192*k) 0 8192 _ (by omega) (by decide) r atStart]
    simp only [qGroups,bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro mid hit
    obtain ⟨next,atLatch⟩ := q_segment_post s (8192*k) 0 8192 r atStart hit
    have nextRegs : QRegs mid (8192*(k+1)) := by simpa only [Nat.mul_succ] using next
    rw [q_latch mid k _ (by omega) nextRegs atLatch]
    let after := mid.setPC (qLatchPC k)
    have regs : QRegs after (8192*(k+1)) := ⟨nextRegs.source,nextRegs.dest,nextRegs.selector,
      nextRegs.size,nextRegs.primitive,nextRegs.stop⟩
    have again (more : 0<n) : after.pc=quadPC 0 := by change qLatchPC k=_;rw [qLatchPC,if_neg (by omega)]
    rw [ih after (k+1) (by omega) regs again,arithmetic.2]
    simp only [bind_assoc,pure_bind]
    apply bind_congr;intro last
    apply bind_congr;intro result
    apply congrArg pure
    cases result
    simp only [Execution.charge,Execution.mk.injEq,true_and]
    constructor <;> omega

theorem entire_quartet_phase (s : MachineState) (fuel : Nat) (r : QRegs s 0) (pc : s.pc=quadPC 0) :
    execute image (12583935+fuel) s true = (do
      let out ← qGroups 512 0 s
      let e ← execute image fuel out true
      return e.charge 41944063 4194304) :=
  q_group_run s 512 0 fuel (by decide) r (fun _ => pc)

end TwoPermutationPrototype.Grouped
