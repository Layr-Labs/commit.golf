import CommitGolfCandidate.R1bParentCost
import CommitGolfCandidate.R1bParentSites
import CommitGolfCandidate.R1bNarrowState

namespace TwoPermutationPrototype.RV64.R1bParents
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
attribute [local irreducible] execute writeBits

def ip (i : Nat) : Word := BitVec.ofNat 64 (4096+4*i)
def nodeIP (n : Nat) := ip (if n=0 then 262060 else site n)
def retained (n : Nat) (v : BitVec 256) := if n<524288 then RV64.pad238 v else projectReply v

def laneState (s : MachineState) (n : Nat) (v : BitVec 256) : MachineState :=
  if n<524288 then suffixState (parentWritten s n v) 5 else packedParentAfter s n v

def nextState (s : MachineState) (n : Nat) (v : BitVec 256) : MachineState :=
  (laneState s n v).setPC (nodeIP (n-1))

structure Ready (s : MachineState) (n : Nat) extends ParentRegs s n : Prop where
  pc : s.pc=nodeIP n
  stop : s.getReg .x18=wordAddress (treeWord 524287)
  mask : s.getReg .x6=16383

theorem laneKeeps (s : MachineState) (n : Nat) (v : BitVec 256) (r : Reg)
    (a : Reg.x10≠r) (b : Reg.x12≠r) (c : Reg.x7≠r) : (laneState s n v).getReg r=s.getReg r := by
  unfold laneState
  split
  · exact (suffixKeeps (parentWritten s n v) r a b c).trans (writeBits_register s (wordAddress (treeWord n)) v r)
  · exact packed_parent_keeps_register s n v r a b

theorem next_regs {s : MachineState} {n : Nat} (v : BitVec 256) (r : Ready s (n+1)) :
    Ready (nextState s (n+1) v) n := by
  have t : ParentRegs (laneState s (n+1) v) n := by
    unfold laneState;split
    · exact narrowRegs s n v r.toParentRegs
    · exact packed_next_parent_regs s n v r.toParentRegs
  refine ⟨⟨t.source,t.target,t.selector,t.size,t.primitive,t.heap⟩,rfl,?_,?_⟩
  · exact (laneKeeps s (n+1) v .x18 (by decide) (by decide) (by decide)).trans r.stop
  · exact (laneKeeps s (n+1) v .x6 (by decide) (by decide) (by decide)).trans r.mask

def trace : Nat → MachineState → OracleComp World MachineState
  | 0,s => pure s
  | n+1,s => do
    let v ← (liftM (World.query (.inr (.inl (parentInput s (n+1))))) : OracleComp World (BitVec 256))
    trace n (nextState s (n+1) v)

theorem trace_post (n : Nat) (s : MachineState) (r : Ready s n) {out : MachineState}
    (hit : out ∈ support (trace n s)) : Ready out 0 ∧ out.getReg .x8=s.getReg .x8 := by
  induction n generalizing s with
  | zero =>
    simp only [trace,support_pure,Set.mem_singleton_iff] at hit
    subst out;exact ⟨r,rfl⟩
  | succ n ih =>
    simp only [trace,mem_support_bind_iff] at hit
    obtain ⟨v,_,reached⟩ := hit
    have ⟨post,saved⟩:=ih _ (next_regs v r) reached
    refine ⟨post,saved.trans ?_⟩
    exact laneKeeps s (n+1) v .x8 (by decide) (by decide) (by decide)

def NodeExecution : Prop := ∀ (s : MachineState) (n fuel : Nat), n < 8388607 → Ready s (n+1) →
  execute packedWideCommitImage (width (n+1)+controlSteps (n+1)+fuel) s true =
    (do let v ← (liftM (World.query (.inr (.inl (parentInput s (n+1))))) : OracleComp World (BitVec 256))
        let out ← execute packedWideCommitImage fuel (nextState s (n+1) v) true
        return out.charge (width (n+1)+controlSteps (n+1)+7) 1)

theorem trace_run (lane : NodeExecution) (n fuel : Nat) (s : MachineState) (bound : n≤8388607) (r : Ready s n) :
    execute packedWideCommitImage (remainingSteps n+fuel) s true =
      (do let t ← trace n s
          let out ← execute packedWideCommitImage fuel t true
          return out.charge (remainingSteps n+7*n) n) := by
  induction n generalizing s with
  | zero => simp [remainingSteps,trace,Execution.charge]
  | succ n ih =>
    have cost := stepCount (n:=n+1) (by omega)
    simp only [Nat.add_sub_cancel] at cost
    rw [cost,Nat.add_assoc _ (remainingSteps n) fuel,lane _ _ _ (by omega) r]
    simp only [trace,bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro v _
    rw [ih _ (by omega) (next_regs v r)]
    simp [Execution.charge,Nat.mul_succ,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

end TwoPermutationPrototype.RV64.R1bParents
