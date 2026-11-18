import CommitGolfCandidate.QuadCommitRoot
import CommitGolfCandidate.QuadCommitQuadControl

/-! The tree phase of the commit image from any leaf-entry state with the right registers. -/
namespace TwoPermutationPrototype.Quad.Commit
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64
set_option maxRecDepth 8192
set_option maxHeartbeats 200000
attribute [local irreducible] image execute rootPrefix

/-- Registers of the leaf-entry state (PC 4172) needed by the whole tree phase. -/
structure ReadyRegs (s : MachineState) : Prop where
  regs : Leaves.Regs s 0 0
  out : s.getReg .x8=4294971392
  heap : s.getReg .x9=4294971424

def body (ready : MachineState) : OracleComp World MachineState := do
  let leaves ← Leaves.groups 4096 0 ready
  let quads ← Quads.groups 256 0 (quadSetup leaves 9)
  let parents ← packedParentGroups 381596 15709 267 (parentSetup quads 9)
  return rootPrefix parents 10

attribute [local irreducible] body Leaves.groups Quads.groups packedParentGroups

/-- From the leaf-entry state: 4096 leaf bodies, 256 quad bodies, 267 parent bodies, root, HALT. -/
theorem execute_after_ready (ready : MachineState) (r : ReadyRegs ready) (fuel : Nat) :
    execute image (214434860+fuel) ready true =
      (do let result ← body ready
          return ⟨.success,result,508036133,41943039⟩) := by
  have rs := r.regs
  rw [show 214434860+fuel=185073663+(9+(12583423+(9+(16777745+(11+fuel))))) by omega,
    Leaves.groups_run _ 4096 0 _ (by decide) (fun _ => rs) r.out]
  simp only [body,bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro leaves reached
  obtain ⟨leafPC,keep⟩ := Leaves.groups_post _ 4096 0 (by decide) rs (by decide) reached
  have selector : leaves.getReg .x5=0 := (keep .x5 (by simp [Leaves.SavedReg])).trans rs.selector
  have size : leaves.getReg .x11=200 := (keep .x11 (by simp [Leaves.SavedReg])).trans rs.size
  have primitive : leaves.getReg .x13=1 := (keep .x13 (by simp [Leaves.SavedReg])).trans rs.primitive
  have heap : leaves.getReg .x9=4294971424 := (keep .x9 (by simp [Leaves.SavedReg])).trans r.heap
  have output : leaves.getReg .x8=4294971392 := (keep .x8 (by simp [Leaves.SavedReg])).trans r.out
  have quadRegs := quad_setup_regs leaves heap selector size primitive
  rw [execute_quad_setup leaves leafPC,
    Quads.groups_run _ 256 0 _ (by decide) quadRegs.1
      (fun _ => quad_setup_pc leaves leafPC) quadRegs.2]
  simp only [bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro quads reached
  obtain ⟨qr,quadPC,qkeep⟩ := Quads.groups_post _ 256 0 (by decide) quadRegs.1
    (fun _ => quad_setup_pc leaves leafPC) reached
  have qheap : quads.getReg .x9=4294971424 := (qkeep .x9 (by decide) (by decide)).trans heap
  have qout : quads.getReg .x8=4294971392 := (qkeep .x8 (by decide) (by decide)).trans output
  have pr := parent_setup_regs quads qheap qr.selector
  have pRun := Parents.groups_run image 381596 15709 parent_words parent_control (by decide) 267 (11+fuel)
    (parentSetup quads 9) (by decide) pr.1
    (fun _ => parent_setup_pc quads (quadPC (by decide))) pr.2
  change execute image (16777745+(11+fuel)) (parentSetup quads 9) true =
    (do let parents ← packedParentGroups 381596 15709 267 (parentSetup quads 9)
        let out ← execute image (11+fuel) parents true
        return out.charge 46137866 4194303) at pRun
  rw [execute_parent_setup quads (quadPC (by decide)),pRun]
  simp only [bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro parents reached
  obtain ⟨terms,here⟩ := packed_groups_post 381596 15709 267 _ (by decide)
    (fun _ => parent_setup_pc quads (quadPC (by decide))) pr.1 reached
  have parentPC : parents.pc=632948 := here (by decide)
  have pout : parents.getReg .x8=4294971392 :=
    (Parents.groups_keeps _ 381596 15709 267 .x8 (by decide) (by decide) reached).trans qout
  rw [execute_root parents parentPC terms.heap pout]
  simp only [bind_assoc,pure_bind,Execution.charge]

end TwoPermutationPrototype.Quad.Commit
