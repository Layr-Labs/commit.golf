import CommitGolfCandidate.R1bParentControl
import CommitGolfCandidate.R1bNarrowLane
namespace TwoPermutationPrototype.RV64.R1bParents
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
attribute [local irreducible] execute writeBits

private theorem wideFetch (slot : Nat) (hs : slot<1024) (k : Fin 4) (s : MachineState)
    (pc : s.pc=ip (26+4*slot+k.val)) :
    fetch packedWideCommitImage s=some (.base wideOps[k.val]) := by
  have dec:=decodedBlock (slot/64) (by omega) false ⟨slot%64,by omega⟩ k
  change Manifest.decodeBase (packed_wideCodeWord (26+4*(64*(slot/64)+slot%64)+k.val))=some wideOps[k.val] at dec
  rw [show 64*(slot/64)+slot%64=slot by omega] at dec
  exact packed_wide_fetch_decoded s (26+4*slot+k.val) (by omega) pc _ dec

private theorem wideWords (slot : Nat) (hs : slot<1024) :
    PackedParentWordsAt packedWideCommitImage (ip (26+4*slot)) := by
  have offset (k : Fin 4) : ip (26+4*slot+k.val)=ip (26+4*slot)+BitVec.ofNat 64 (4*k.val) := by
    unfold ip;rw [←BitVec.ofNat_add];congr 1;omega
  refine ⟨fun s pc=>?_,fun s pc=>?_,fun s pc=>?_,fun s pc=>?_⟩
  · exact wideFetch slot hs 0 s pc
  · exact wideFetch slot hs 1 s (pc.trans (offset 1).symm)
  · exact wideFetch slot hs 2 s (pc.trans (offset 2).symm)
  · exact wideFetch slot hs 3 s (pc.trans (offset 3).symm)

theorem laneRun (s : MachineState) (n fuel : Nat) (bound : n<8388607) (r : Ready s (n+1)) :
    execute packedWideCommitImage (width (n+1)+fuel) s true =
      (do let v ← (liftM (World.query (.inr (.inl (parentInput s (n+1))))) : OracleComp World (BitVec 256))
          let out ← execute packedWideCommitImage fuel (laneState s (n+1) v) true
          return out.charge (width (n+1)+7) 1) := by
  have here : s.pc=ip (site (n+1)) := r.pc
  have advance (w : Nat) : s.pc+BitVec.ofNat 64 (4*w)=ip (site (n+1)+w) := by
    rw [here];unfold ip;rw [←BitVec.ofNat_add];congr 1;omega
  by_cases low : n+1<524288
  · let slot := (1024-(n+1)%1024)%1024
    have hs : slot<1024 := Nat.mod_lt _ (by decide)
    have sitePC : s.pc=ip (4125+6*slot) := by simpa [site,low,slot] using here
    have call:=parent_call_at packedWideCommitImage s (n+1) (5+fuel) (by omega) r.toParentRegs (fetchLane _ 0 hs (by decide) s sitePC)
    rw [width,if_pos low,show 6+fuel=(5+fuel)+1 by omega,call]
    apply bind_congr_of_forall_mem_support
    intro v _
    rw [narrowSuffix v (by omega) hs r.toParentRegs sitePC fuel]
    simp [laneState,low,Execution.charge,bind_assoc,←Nat.add_assoc]
  · let slot := 1023-(n+1)%1024
    have hs : slot<1024 := by unfold slot;omega
    have sitePC : s.pc=ip (26+4*slot) := by simpa [site,low,slot] using here
    rw [width,if_neg low,packed_parent_step _ _ _ _ _ sitePC (by omega) r.toParentRegs (wideWords slot hs)]
    apply bind_congr_of_forall_mem_support
    intro v _
    simp only [laneState,if_neg low]

private theorem laneEnd (s : MachineState) (n : Nat) (v : BitVec 256) (pc : s.pc=ip (site n)) :
    (laneState s n v).pc=ip (site n+width n) := by
  have move (w : Nat) : s.pc+BitVec.ofNat 64 (4*w)=ip (site n+w) := by
    rw [pc];unfold ip;rw [←BitVec.ofNat_add];congr 1;omega
  unfold laneState width
  split
  · rw [suffixPC,show (parentWritten s n v).pc=s.pc+4 from written_pc s _ v,BitVec.add_assoc]
    exact move 6
  · rw [packed_parent_pc];exact move 4

theorem node_execution : NodeExecution := by
  intro s n fuel bound ready
  rw [Nat.add_assoc,laneRun s n (controlSteps (n+1)+fuel) bound ready]
  apply bind_congr_of_forall_mem_support
  intro v _
  have next:=next_regs v ready
  let z:=laneState s (n+1) v
  have regs : ParentRegs z n := ⟨next.source,next.target,next.selector,next.size,next.primitive,next.heap⟩
  have go:=dispatch z (n+1) fuel (by omega) (by omega) (laneEnd s (n+1) v ready.pc) regs next.stop
  have same : z.setPC (nodeIP (n+1-1))=nextState s (n+1) v := by rfl
  rw [same] at go
  rw [show execute packedWideCommitImage (controlSteps (n+1)+fuel) (laneState s (n+1) v) true=_ from go]
  simp [Execution.charge,bind_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

end TwoPermutationPrototype.RV64.R1bParents
