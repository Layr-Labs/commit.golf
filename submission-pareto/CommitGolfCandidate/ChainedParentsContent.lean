import CommitGolfCandidate.ChainedLevelContent

/-! Composition of canonical heap contents through all 24 delivered parent levels. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
attribute [local irreducible] parentLevels checkEvaluation readBuffer

def ChainedTree (oracle : Oracle) (heap : Nat → BitVec 238) : Prop :=
  ∀ h node, heightCount h ≤ node → node < 2*heightCount h →
    (heap node).setWidth 256 = parentValue oracle h (heap (2*node)) (heap (2*node+1))

theorem stage_count_next (remaining : Nat) (positive : 0 < remaining) (small : remaining < 24) :
    2*heightCount (heightAt remaining) = heightCount (heightAt (remaining+1)) := by
  let i : Fin 23 := ⟨23-remaining,by omega⟩
  have current : heightAt (remaining+1) = lowerHeight i := by
    apply Fin.ext
    dsimp [heightAt,lowerHeight,i]
    omega
  have next : heightAt remaining = nextHeight i := by
    apply Fin.ext
    dsimp [heightAt,nextHeight,i]
    omega
  rw [current,next,height_count_next]

theorem parent_levels_content (oracle : Oracle) (heap : Nat → BitVec 238) (tree : ChainedTree oracle heap)
    (remaining : Nat) (small : remaining ≤ 24) (positive : 0 < remaining) (s : MachineState)
    (ready : HeapLevelReady s (heightAt remaining) (heightCount (heightAt remaining)))
    (prior : HeapContent s heap (2*heightCount (heightAt remaining)-1)) :
    HeapContent (checkEvaluation oracle (parentLevels remaining s)).1 heap 0 := by
  induction remaining generalizing s with
  | zero => omega
  | succ remaining ih =>
    let mid := (checkEvaluation oracle (stageTrace (heightAt (remaining+1)) s)).1
    have reached := check_evaluation_support oracle (stageTrace (heightAt (remaining+1)) s)
    have content := stage_content oracle heap _ s ready (tree _) prior
    cases remaining with
    | zero =>
      have one : heightCount (heightAt 1) = 1 := by decide +kernel
      simpa only [parentLevels,check_evaluation_bind,check_evaluation_pure,one,Nat.sub_self] using content
    | succ n =>
      have next := stage_next (n+1) (by omega) (by omega) s mid ready reached
      have initial : HeapContent mid heap (2*heightCount (heightAt (n+1))-1) := by
        rw [stage_count_next (n+1) (by omega) (by omega)]
        exact content
      rw [parentLevels,check_evaluation_bind]
      exact ih (by omega) (by omega) mid next initial

end CommitGolfCandidate.Chained.Native
