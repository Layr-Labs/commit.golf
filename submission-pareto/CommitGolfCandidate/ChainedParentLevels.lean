import CommitGolfCandidate.ChainedParentInit

/-! Native execution of the complete sequence of 24 parent levels. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
attribute [local irreducible] execute

def heightAt (remaining : Nat) : Height := ⟨(24-remaining)%24,Nat.mod_lt _ (by decide)⟩
def stageSteps (h : Height) := 6+parentNodeSteps h*heightCount h
def stageCycles (h : Height) := 6+parentNodeCycles h*heightCount h
def stageQueries (h : Height) := calls h*heightCount h

def stageTrace (h : Height) (s : MachineState) : OracleComp World MachineState := do
  let out ← heapLevelTrace h (heightCount h) s
  return shiftState out

theorem stage_execution (s : MachineState) (h : Height)
    (ready : HeapLevelReady s h (heightCount h)) (fuel : Nat) (coins : Bool) :
    execute chainedCommitImage (stageSteps h+fuel) s coins =
      (do let out ← stageTrace h s
          let result ← execute chainedCommitImage fuel out coins
          return result.charge (stageCycles h) (stageQueries h)) := by
  rw [show stageSteps h+fuel = 5+parentNodeSteps h*heightCount h+(fuel+1) by unfold stageSteps; omega,
    heap_level_execution s h _ ready]
  simp only [stageTrace,bind_assoc,pure_bind]
  apply bind_congr_of_forall_mem_support
  intro out reached
  rw [shift_execution out h (heap_level_pc s out h _ ready reached)]
  simp [stageCycles,stageQueries,Execution.charge,←Nat.add_assoc,
    show 5+parentNodeCycles h*heightCount h+1 = 6+parentNodeCycles h*heightCount h by omega]

theorem stage_next (remaining : Nat) (positive : 0 < remaining) (small : remaining < 24)
    (s out : MachineState) (ready : HeapLevelReady s (heightAt (remaining+1)) (heightCount (heightAt (remaining+1))))
    (reached : out ∈ support (stageTrace (heightAt (remaining+1)) s)) :
    HeapLevelReady out (heightAt remaining) (heightCount (heightAt remaining)) := by
  let i : Fin 23 := ⟨23-remaining,by omega⟩
  have current : heightAt (remaining+1) = lowerHeight i := by
    apply Fin.ext
    dsimp [heightAt,lowerHeight,i]
    omega
  have next : heightAt remaining = nextHeight i := by
    apply Fin.ext
    dsimp [heightAt,nextHeight,i]
    omega
  rw [current] at ready reached
  rw [next]
  simp only [stageTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
  obtain ⟨before,last,rfl⟩ := reached
  exact heap_level_next i s before ready last

def parentLevels : Nat → MachineState → OracleComp World MachineState
  | 0,s => pure s
  | remaining+1,s => do
    let out ← stageTrace (heightAt (remaining+1)) s
    parentLevels remaining out

def levelsSteps : Nat → Nat
  | 0 => 0
  | remaining+1 => stageSteps (heightAt (remaining+1))+levelsSteps remaining
def levelsCycles : Nat → Nat
  | 0 => 0
  | remaining+1 => stageCycles (heightAt (remaining+1))+levelsCycles remaining
def levelsQueries : Nat → Nat
  | 0 => 0
  | remaining+1 => stageQueries (heightAt (remaining+1))+levelsQueries remaining

theorem parent_levels_execution (remaining : Nat) (small : remaining ≤ 24) (s : MachineState)
    (ready : 0 < remaining → HeapLevelReady s (heightAt remaining) (heightCount (heightAt remaining)))
    (fuel : Nat) (coins : Bool) :
    execute chainedCommitImage (levelsSteps remaining+fuel) s coins =
      (do let out ← parentLevels remaining s
          let result ← execute chainedCommitImage fuel out coins
          return result.charge (levelsCycles remaining) (levelsQueries remaining)) := by
  induction remaining generalizing s with
  | zero => simp [parentLevels,levelsSteps,levelsCycles,levelsQueries,Execution.charge]
  | succ remaining ih =>
    have entry := ready (by omega)
    rw [levelsSteps,Nat.add_assoc,stage_execution s _ entry]
    simp only [parentLevels,bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro out reached
    rw [ih (by omega) out (fun positive => stage_next remaining positive (by omega) s out entry reached)]
    simp [levelsCycles,levelsQueries,Execution.charge,←Nat.add_assoc]

theorem parent_levels_totals : levelsSteps 24 = 1343338074 ∧
    levelsCycles 24 = 1814456659 ∧ levelsQueries 24 = 67302655 := by decide +kernel

end CommitGolfCandidate.Chained.Native
