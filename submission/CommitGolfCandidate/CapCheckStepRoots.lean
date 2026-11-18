import CommitGolfCandidate.CapCheckDfsEvaluation
import CommitGolfCandidate.CapCheckBoundaryRoots
import CommitGolfCandidate.CapMultiproof

/-! Root-heap projection of the same fixed-oracle DFS transition. Unknown
visits install their proof digest, and an odd-child return compresses the
already populated adjacent child slots. Every other bounded slot is framed.
This is a step refinement, not yet the whole codec acceptance theorem. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false
attribute [local irreducible] readBuffer

def capCheckRootStep (compress : Compression) (marked : Nat → Bool)
    (control : CapDfsControl) (roots : Nat → Digest) (boundary : Digest) :
    Nat → Digest :=
  match control with
  | .visit node =>
      if marked node then roots else fun other => if other=node then boundary else roots other
  | .advance node =>
      if node=1 ∨ node%2=0 then roots
      else fun other => if other=node/2 then
        combine compress (roots (2*(node/2))) (roots (2*(node/2)+1)) else roots other
  | .done => roots

theorem cap_check_ascent_query_roots (state : MachineState) (node : Nat) :
    capCheckAscentQuery state node =
      capReadRoot state (2*(node/2)+1) ++ capReadRoot state (2*(node/2)) := by
  unfold capCheckAscentQuery capReadRoot
  rw [show 12288+32*(2*(node/2)+1)=12288+64*(node/2)+32 by omega,
    show 12288+32*(2*(node/2))=12288+64*(node/2) by omega]

theorem cap_check_dfs_next_roots (oracle : Oracle) (limit : Nat)
    (marked : Nat → Bool) (control : CapDfsControl) (state : MachineState)
    (ready : CapCheckDfsReady limit marked control state)
    (above : 32768 ≤ (state.getReg .x25).toNat)
    (other : Nat) (otherBound : other<512) :
    capReadRoot (capCheckDfsNext oracle marked control state) other =
      capCheckRootStep (s6Compress oracle.compression) marked control (capReadRoot state)
        (readBuffer state (state.getReg .x25).toNat 32) other := by
  have roots : state.getReg .x18=12288 := by
    have fixed : state.getReg .x18=BitVec.ofNat 64 12288 := by
      simpa only [capBoundaryRootRegister,↓reduceIte] using ready.stable.roots
    exact fixed.trans (by rfl)
  cases control with
  | visit node =>
    by_cases present : marked node=true
    · simp only [capCheckDfsNext,capCheckRootStep,if_pos present]
      exact read_buffer_memory_congr _ _
        (cap_marked_visit_memory true state node) _ _
    · simp only [capCheckDfsNext,capCheckRootStep,if_neg present]
      have cursorSmall : (state.getReg .x25).toNat+32≤2^64 := by
        have bound := ready.window.limitBound
        have before := ready.window.beforeEnd
        simp only [MEMORY_BYTES] at bound
        omega
      exact cap_unknown_check_root_map state node other (state.getReg .x25).toNat
        roots ready.physical.2
        (by simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq])
        ready.valid.2 otherBound above ready.window.aligned cursorSmall
  | advance node =>
    by_cases root : node=1
    · simp only [capCheckDfsNext,capCheckRootStep,if_pos root,
        root,true_or,↓reduceIte]
      exact read_buffer_memory_congr _ _ (cap_flow_memory _ _) _ _
    · by_cases even : node%2=0
      · simp only [capCheckDfsNext,capCheckRootStep,if_neg root,if_pos even,
          even,or_true,↓reduceIte]
        exact read_buffer_memory_congr _ _ (cap_advance_sibling_memory true state) _ _
      · have inactive : ¬ (node=1 ∨ node%2=0) := by
          simp only [root,even,false_or,not_false_eq_true]
        simp only [capCheckDfsNext,capCheckRootStep,if_neg root,if_neg even,
          if_neg inactive]
        rw [cap_check_ascent_answer_root_map state
          (oracle.compression (capCheckAscentQuery state node)) node other
          ready.physical.2 roots ready.valid.2 otherBound,
          cap_check_ascent_query_roots]
        rfl
  | done => rfl

end CommitGolfCandidate
