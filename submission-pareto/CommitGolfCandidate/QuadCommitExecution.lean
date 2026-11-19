import CommitGolfCandidate.QuadCommitRoot
import CommitGolfCandidate.QuadCommitQuad3Control

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
  let quad2s ← Quad2s.groups 64 0 (quad2Setup quads 9)
  let quad3s ← Quad3s.groups 16 0 (quad3Setup quad2s 9)
  let parents ← packedParentGroups 774900 13797 19 (parentSetup quad3s 9)
  return rootPrefix parents 10

attribute [local irreducible] body Leaves.groups Quads.groups Quad2s.groups Quad3s.groups packedParentGroups

/-- From the leaf-entry state: 4096 leaf bodies, 256 level-1 bodies, 64 level-2 bodies,
16 level-3 bodies, 19 parent bodies, root, HALT. -/
theorem execute_after_ready (ready : MachineState) (r : ReadyRegs ready) (fuel : Nat) :
    execute image (202638060+fuel) ready true =
      (do let result ← body ready
          return ⟨.success,result,477889253,39321599⟩) := by
  have rs := r.regs
  rw [show 202638060+fuel=185073663+(9+(12583423+(9+(3145855+(9+(786463+(9+(1048609+(11+fuel))))))))) by omega,
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
  have quad2Regs := quad2_setup_regs quads qheap qr.selector qr.size qr.primitive
  rw [execute_quad2_setup quads (quadPC (by decide)),
    Quad2s.groups_run _ 64 0 _ (by decide) quad2Regs.1
      (fun _ => quad2_setup_pc quads (quadPC (by decide))) quad2Regs.2]
  simp only [bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro quad2s reached
  obtain ⟨q2r,quad2PC,q2keep⟩ := Quad2s.groups_post _ 64 0 (by decide) quad2Regs.1
    (fun _ => quad2_setup_pc quads (quadPC (by decide))) reached
  have q2heap : quad2s.getReg .x9=4294971424 := (q2keep .x9 (by decide) (by decide)).trans qheap
  have q2out : quad2s.getReg .x8=4294971392 := (q2keep .x8 (by decide) (by decide)).trans qout
  have quad3Regs := quad3_setup_regs quad2s q2heap q2r.selector q2r.size q2r.primitive
  rw [execute_quad3_setup quad2s (quad2PC (by decide)),
    Quad3s.groups_run _ 16 0 _ (by decide) quad3Regs.1
      (fun _ => quad3_setup_pc quad2s (quad2PC (by decide))) quad3Regs.2]
  simp only [bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro quad3s reached
  obtain ⟨q3r,quad3PC,q3keep⟩ := Quad3s.groups_post _ 16 0 (by decide) quad3Regs.1
    (fun _ => quad3_setup_pc quad2s (quad2PC (by decide))) reached
  have q3heap : quad3s.getReg .x9=4294971424 := (q3keep .x9 (by decide) (by decide)).trans q2heap
  have q3out : quad3s.getReg .x8=4294971392 := (q3keep .x8 (by decide) (by decide)).trans q2out
  have pr := parent_setup_regs quad3s q3heap q3r.selector
  have pRun := Parents.groups_run image 774900 13797 parent_words parent_control (by decide) 19 (11+fuel)
    (parentSetup quad3s 9) (by decide) pr.1
    (fun _ => parent_setup_pc quad3s (quad3PC (by decide))) pr.2
  change execute image (1048609+(11+fuel)) (parentSetup quad3s 9) true =
    (do let parents ← packedParentGroups 774900 13797 19 (parentSetup quad3s 9)
        let out ← execute image (11+fuel) parents true
        return out.charge 2883610 262143) at pRun
  rw [execute_parent_setup quad3s (quad3PC (by decide)),pRun]
  simp only [bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro parents reached
  obtain ⟨terms,here⟩ := packed_groups_post 774900 13797 19 _ (by decide)
    (fun _ => parent_setup_pc quad3s (quad3PC (by decide))) pr.1 reached
  have parentPC : parents.pc=995660 := here (by decide)
  have pout : parents.getReg .x8=4294971392 :=
    (Parents.groups_keeps _ 774900 13797 19 .x8 (by decide) (by decide) reached).trans q3out
  rw [execute_root parents parentPC terms.heap pout]
  simp only [bind_assoc,pure_bind,Execution.charge]

end TwoPermutationPrototype.Quad.Commit
