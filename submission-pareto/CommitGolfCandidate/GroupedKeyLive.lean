import CommitGolfCandidate.GroupedKeySetup

/-! The P4 prologue's final state is the grouped scan's `Live` state at leaf 0. -/
namespace TwoPermutationPrototype.Grouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
set_option maxRecDepth 60000
set_option maxHeartbeats 1000000

private theorem ready_reg (t : MachineState) :
    (readyOps.foldl execInstrBr t).getReg .x10=t.getReg .x18 ∧
    (readyOps.foldl execInstrBr t).getReg .x20=t.getReg .x20+2048 ∧
    (readyOps.foldl execInstrBr t).getReg .x7=4096 ∧
    (readyOps.foldl execInstrBr t).getReg .x28=t.getReg .x21+2048 ∧
    (readyOps.foldl execInstrBr t).getReg .x5=0 ∧
    (readyOps.foldl execInstrBr t).getReg .x11=200 ∧
    (readyOps.foldl execInstrBr t).getReg .x13=1 ∧
    (readyOps.foldl execInstrBr t).pc=t.pc+32 ∧
    ∀ reg ∈ [Reg.x8,.x9,.x19,.x21,.x24], (readyOps.foldl execInstrBr t).getReg reg=t.getReg reg := by
  refine ⟨?_,?_,?_,?_,rfl,rfl,rfl,?_,?_⟩
  · change t.getReg .x18+0=_;simp
  · rfl
  · rfl
  · rfl
  · change t.pc+4+4+4+4+4+4+4+4=_;bv_omega
  · intro reg member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl <;> rfl

theorem ready_live (s : MachineState) (e : CommitEntry s) (k : BitVec 192) : Live (keyReady s k) 0 := by
  have r := key_registers s e
  have w (reg : Reg) : (keyWritten s k).getReg reg = (keySetup s).getReg reg := writeBits_register ..
  have wpc : (keyWritten s k).pc=4148 := by rw [keyWritten,written_pc,key_pc s e.pc];rfl
  obtain ⟨x10,x20,x7,x28,x5,x11,x13,pc,keep⟩ := ready_reg (keyWritten s k)
  change (readyOps.foldl execInstrBr (keyWritten s k)).getReg _ = _ at x10
  refine ⟨⟨?_,?_,x7,?_,?_,x5,x11,x13⟩,?_,?_,?_,?_,?_,?_⟩
  · rw [show keyReady s k = readyOps.foldl execInstrBr (keyWritten s k) from rfl,x10,w,r.source];rfl
  · rw [show keyReady s k = readyOps.foldl execInstrBr (keyWritten s k) from rfl,x20,w,r.leaves];rfl
  · rw [show keyReady s k = readyOps.foldl execInstrBr (keyWritten s k) from rfl,keep .x24 (by simp),w,r.key]
  · trivial
  · rw [show keyReady s k = readyOps.foldl execInstrBr (keyWritten s k) from rfl,pc,wpc];rfl
  · rw [show keyReady s k = readyOps.foldl execInstrBr (keyWritten s k) from rfl,x28,w,r.stop]
  · rw [show keyReady s k = readyOps.foldl execInstrBr (keyWritten s k) from rfl,keep .x8 (by simp),w,r.out]
  · rw [show keyReady s k = readyOps.foldl execInstrBr (keyWritten s k) from rfl,keep .x9 (by simp),w,r.heap]
  · rw [show keyReady s k = readyOps.foldl execInstrBr (keyWritten s k) from rfl,keep .x19 (by simp),w,r.stride]
  · rw [show keyReady s k = readyOps.foldl execInstrBr (keyWritten s k) from rfl,keep .x21 (by simp),w,r.stop]

end TwoPermutationPrototype.Grouped
