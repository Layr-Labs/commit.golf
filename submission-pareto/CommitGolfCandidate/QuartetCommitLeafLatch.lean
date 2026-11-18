import CommitGolfCandidate.QuartetCommitLeafGroups
import CommitGolfCandidate.QuartetCommitSetup

namespace TwoPermutationPrototype.RV64.QuartetLeaves
open TwoPermutationPrototype.QuartetCommit
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
attribute [local irreducible] execute QuartetCommit.image

def latchPC (g : Nat) : Word := if g+1=2^12 then 184992 else 4184
def latchCost (g : Nat) := if g+1=2^12 then 1 else 2

theorem latch_run (s : MachineState) (g fuel : Nat) (bound : g<2^12) (r : Regs s g 4096)
    (stop : s.getReg .x25=wordAddress (qSource 4194304)+2048) :
    execute QuartetCommit.image (latchCost g+fuel) s true =
      (do let y ← execute QuartetCommit.image fuel (s.setPC (latchPC g)) true
          return y.charge (latchCost g) 0) := by
  have here : s.pc=184984 := r.pc
  have eq : s.getReg .x20=s.getReg .x25 ↔ g+1=2^12 := by
    rw [r.heap,stop,BitVec.add_left_inj]
    constructor
    · intro h
      have j := wordAddress_injective_of_bound (a := heapBase g 4096) (b := qSource 4194304)
        (by unfold heapBase qSource;omega) (by decide) h
      unfold heapBase qSource at j;omega
    · intro h
      apply congrArg wordAddress
      unfold heapBase qSource
      omega
  by_cases last : g+1=2^12
  · have step : ordinaryStep s (.base (.BEQ .x20 .x25 8))=some (s.setPC 184992) := by
      simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,here,eq.mpr last,signExtend13]
    rw [latchCost,if_pos last,latchPC,if_pos last,Nat.add_comm 1 fuel,
      CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (fetch_leaf_branch s here) step];rfl
  · let middle := s.setPC 184988
    have diff : s.getReg .x20≠s.getReg .x25 := fun h => last (eq.mp h)
    have step : ordinaryStep s (.base (.BEQ .x20 .x25 8))=some middle := by
      simp [middle,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,here,diff]
    have jump : ordinaryStep middle (.base (.JAL .x0 1916348))=some (s.setPC 4184) := by
      simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,middle,MachineState.setReg,MachineState.setPC]
      rfl
    rw [latchCost,if_neg last,latchPC,if_neg last,show 2+fuel=(fuel+1)+1 by omega,
      CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (fetch_leaf_branch s here) step,
      CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (fetch_leaf_jump middle rfl) jump]
    simp [instructionCycles,Execution.charge,←Nat.add_assoc]

theorem latch_next (s : MachineState) (g : Nat) (more : g+1<2^12) (r : Regs s g 4096) :
    Regs (s.setPC (latchPC g)) (g+1) 0 := by
  have source : 4096*(g+1)+0=4096*g+4096 := by omega
  refine ⟨?_,?_,?_,r.stride,r.selector,r.size,r.primitive,?_⟩
  · change s.getReg .x10=wordAddress (leafStart _+5);rw [source];exact r.source
  · change s.getReg .x20=wordAddress (heapBase _ _)+2048;rw [r.heap];unfold heapBase;rw [show 1024*g+8*(4096/32)=1024*(g+1)+8*(0/32) by omega]
  · change s.getReg .x22=wordAddress (nonceBase _ _)+2048;rw [r.salts];unfold nonceBase;rw [show 4096*g+256*(4096/256)=4096*(g+1)+256*(0/256) by omega]
  · change latchPC g=_;rw [latchPC,if_neg (by omega)];rfl

def batch (g : Nat) (s : MachineState) : OracleComp World MachineState := do
  let body ← group g 4096 0 s
  return body.setPC (latchPC g)

theorem batch_run (s : MachineState) (g fuel : Nat) (bound : g<2^12) (r : Regs s g 0)
    (stop : s.getReg .x25=wordAddress (qSource 4194304)+2048) :
    execute QuartetCommit.image (45200+latchCost g+fuel) s true =
      (do let next ← batch g s
          let result ← execute QuartetCommit.image fuel next true
          return result.charge (102544+latchCost g) 8192) := by
  rw [show 45200+latchCost g+fuel=span 11 0 4096+(latchCost g+fuel) by change 45200+_+_=45200+(_+_);omega,
    group_run s g 4096 0 _ bound (by decide) r]
  simp only [batch,bind_assoc,pure_bind]
  apply bind_congr_of_forall_mem_support
  intro body reached
  have regs := group_post s g 4096 0 bound (by decide) r reached
  have endReg := (group_saved s g 4096 0 .x25 (by simp [SavedReg]) reached).trans stop
  rw [latch_run body g fuel bound regs endReg]
  simp [span,progress,Execution.charge,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem batch_post (s : MachineState) (g : Nat) (bound : g<2^12) (r : Regs s g 0)
    {next : MachineState} (hit : next ∈ support (batch g s)) :
    (g+1<2^12 → Regs next (g+1) 0) ∧ next.pc=latchPC g ∧
    ∀ reg, SavedReg reg → next.getReg reg=s.getReg reg := by
  simp only [batch,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at hit
  obtain ⟨body,reach,rfl⟩ := hit
  refine ⟨fun more => latch_next body g more (group_post s g 4096 0 bound (by decide) r reach),rfl,?_⟩
  intro reg safe
  exact group_saved s g 4096 0 reg safe (next := body) reach

def groups : Nat → Nat → MachineState → OracleComp World MachineState
  | 0,_,s => pure s
  | k+1,g,s => do
    let mid ← batch g s
    groups k (g+1) mid

theorem groups_run (s : MachineState) (cnt g fuel : Nat) (limit : g+cnt=2^12)
    (r : 0<cnt → Regs s g 0) (stop : s.getReg .x25=wordAddress (qSource 4194304)+2048) :
    execute QuartetCommit.image ((45202*cnt-1)+fuel) s true =
      (do let next ← groups cnt g s
          let result ← execute QuartetCommit.image fuel next true
          return result.charge (102546*cnt-1) (8192*cnt)) := by
  induction cnt generalizing g s with
  | zero => simp [groups,Execution.charge]
  | succ k ih =>
    have last : (45202*(k+1)-1)=45200+latchCost g+(45202*k-1) ∧
        (102546*(k+1)-1)=102544+latchCost g+(102546*k-1) := by
      unfold latchCost;split <;> constructor <;> omega
    have valid := r (by omega)
    rw [last.1,Nat.add_assoc (45200+latchCost g),batch_run s g _ (by omega) valid stop]
    simp only [groups,bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro next reached
    obtain ⟨regs,_,keep⟩ := batch_post s g (by omega) valid reached
    rw [ih next (g+1) (by omega) (fun more => regs (by omega)) ((keep .x25 (by simp [SavedReg])).trans stop), last.2]
    simp [Execution.charge,Nat.mul_succ,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

theorem groups_post (s : MachineState) (cnt g : Nat) (limit : g+cnt=2^12)
    (r : Regs s g 0) (positive : 0<cnt) {out : MachineState} (hit : out ∈ support (groups cnt g s)) :
    out.pc=184992 ∧ ∀ reg, SavedReg reg → out.getReg reg=s.getReg reg := by
  induction cnt generalizing g s with
  | zero => omega
  | succ k ih =>
    simp only [groups,mem_support_bind_iff] at hit
    obtain ⟨mid,step,reach⟩ := hit
    obtain ⟨regs,pc,keep⟩ := batch_post s g (by omega) r step
    cases k with
    | zero =>
      simp only [groups,support_pure,Set.mem_singleton_iff] at reach;subst out
      exact ⟨by rw [pc,latchPC,if_pos (by omega)],keep⟩
    | succ k =>
      obtain ⟨finish,rest⟩ := ih mid (g+1) (by omega) (regs (by omega)) (by omega) reach
      exact ⟨finish,fun reg h => (rest reg h).trans (keep reg h)⟩


theorem entry_regs (s : MachineState) (entry : StartLeafRegs s) : Regs s 0 0 :=
  ⟨entry.source,entry.cursor,entry.salt,entry.bigStride,entry.selector,entry.size,entry.primitive,entry.pc⟩

theorem entire_leaf_phase (s : MachineState) (entry : StartLeafRegs s) (fuel : Nat) :
    execute QuartetCommit.image (185147391+fuel) s true = (do
      let next ← groups 4096 0 s
      let e ← execute QuartetCommit.image fuel next true
      return e.charge 420028415 33554432) :=
  groups_run s 4096 0 fuel (by decide) (fun _ => entry_regs s entry) entry.sentinel

end TwoPermutationPrototype.RV64.QuartetLeaves
