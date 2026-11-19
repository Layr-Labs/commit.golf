import CommitGolfCandidate.QuadNodeLoopMemory
import CommitGolfCandidate.QuadNodeFinish

namespace TwoPermutationPrototype.Quad.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64
set_option maxRecDepth 8192
set_option maxHeartbeats 600000
attribute [local irreducible] execute ByteCopy.copyField ByteCopy.copyRun ByteCopy.copyStep quadSlotPrefix quadSlotLatch

/-- Output cursor of the three actual 32-byte rotation copies. -/
theorem quad_rotation_post (s : MachineState) (r : Fin 4) (proof : Nat)
    (pc : s.pc=5652) (base : s.getReg .x10=12800)
    (offset : s.getReg .x29=BitVec.ofNat 64 (32*r.val))
    (src : s.getReg .x21=BitVec.ofNat 64 proof) (counter : s.getReg .x30=3)
    (room : proof+96≤MEMORY_BYTES) (even : proof%2=0) :
    (quadRotation s).pc=5804 ∧ (quadRotation s).getReg .x10=12800 ∧
      (quadRotation s).getReg .x21=BitVec.ofNat 64 (proof+96) := by
  have p := quad_slot_post s r proof 3 (by decide) (by decide) pc base offset src counter (by omega) even
  have q := quad_slot_post (quadSlot s) (quadNextSlot r) (proof+32) 2 (by decide) (by decide)
    p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 (by omega) (by omega)
  have t := quad_slot_post (quadSlot (quadSlot s)) (quadNextSlot (quadNextSlot r)) (proof+64) 1
    (by decide) (by decide) q.1 q.2.1 q.2.2.1
    (by simpa only [show proof+32+32=proof+64 by omega] using q.2.2.2.1)
    q.2.2.2.2 (by omega) (by omega)
  exact ⟨t.1,t.2.1,by simpa only [quadRotation,show proof+64+32=proof+96 by omega] using t.2.2.2.1⟩

theorem quad_rotation_register (s : MachineState) (r : Fin 4) (proof : Nat)
    (pc : s.pc=5652) (base : s.getReg .x10=12800)
    (offset : s.getReg .x29=BitVec.ofNat 64 (32*r.val))
    (src : s.getReg .x21=BitVec.ofNat 64 proof) (counter : s.getReg .x30=3)
    (room : proof+96≤MEMORY_BYTES) (even : proof%2=0) (reg : Reg)
    (a : reg≠.x21) (b : reg≠.x28) (c : reg≠.x29) (d : reg≠.x30) (e : reg≠.x31) :
    (quadRotation s).getReg reg=s.getReg reg := by
  have p := quad_slot_post s r proof 3 (by decide) (by decide) pc base offset src counter (by omega) even
  have q := quad_slot_post (quadSlot s) (quadNextSlot r) (proof+32) 2 (by decide) (by decide)
    p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 (by omega) (by omega)
  exact (quad_slot_saved (quadSlot (quadSlot s)) 1 (by decide) (by decide) q.2.2.2.2 reg a b c d e).trans
    ((quad_slot_saved (quadSlot s) 2 (by decide) (by decide) p.2.2.2.2 reg a b c d e).trans
      (quad_slot_saved s 3 (by decide) (by decide) counter reg a b c d e))

/-- Full appended quad block, including its actual public permutation query.
The same block computes the quad node and then the quad2 node. -/
def quadNode (s : MachineState) : OracleComp World MachineState :=
  quadFinish (quadRotation (quadPrefix (s.setPC 5564) 22))

theorem quad_set_pc_self (s : MachineState) (pc : s.pc=5564) : s.setPC 5564=s := by
  cases s
  cases pc
  rfl

/-- Workspace preparation, three copies, permutation and loop test execute 141
instructions from the block start, cost 148 cycles, and make exactly one query. -/
theorem execute_quad_body (s : MachineState) (slot : Fin 4) (proof fuel : Nat)
    (pc : s.pc=5564) (pair : s.getReg .x24=12544) (digest : s.getReg .x23=12288)
    (opened : s.getReg .x6 &&& (3#64)=BitVec.ofNat 64 slot.val)
    (src : s.getReg .x21=BitVec.ofNat 64 proof) (room : proof+96≤MEMORY_BYTES) (even : proof%2=0)
    (selector : s.getReg .x5=0) (size : s.getReg .x11=200) (primitive : s.getReg .x13=1) :
    execute packedImage (141+fuel) s false = do
      let finished ← quadNode s
      let result ← execute packedImage fuel finished false
      return result.charge 148 1 := by
  let begin := s.setPC 5564
  let p := quadPrefix begin 22
  have same : begin=s := quad_set_pc_self s pc
  have pairB : begin.getReg .x24=12544 := (MachineState.getReg_setPC).trans pair
  have digestB : begin.getReg .x23=12288 := (MachineState.getReg_setPC).trans digest
  have openedB : begin.getReg .x6 &&& (3#64)=BitVec.ofNat 64 slot.val := by simpa only [begin,MachineState.getReg_setPC] using opened
  have post := quad_prefix_post begin slot rfl pairB openedB
  have srcP : p.getReg .x21=BitVec.ofNat 64 proof :=
    (quad_prefix_register begin .x21 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((MachineState.getReg_setPC).trans src)
  have after := quad_rotation_post p slot proof post.1 post.2.1 post.2.2.2.1 srcP post.2.2.2.2 room even
  have ordinary : GroupHop begin (quadRotation p) 136 :=
    (quad_prefix_hop begin slot rfl pairB digestB openedB).thenDo
      (quad_rotation_hop p slot proof post.1 post.2.1 post.2.2.2.1 srcP post.2.2.2.2 room even)
  rw [same] at ordinary
  have keep (reg : Reg) (a : reg≠.x10) (b : reg≠.x21) (c : reg≠.x28)
      (d : reg≠.x29) (e : reg≠.x30) (f : reg≠.x31) :
      (quadRotation p).getReg reg=s.getReg reg :=
    (quad_rotation_register p slot proof post.1 post.2.1 post.2.2.2.1 srcP post.2.2.2.2 room even
      reg b c d e f).trans
      ((quad_prefix_register begin reg a c d e f).trans MachineState.getReg_setPC)
  have finish := execute_quad_finish (quadRotation p) after.1 after.2.1
    ((keep .x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans digest)
    ((keep .x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans selector)
    ((keep .x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans size)
    ((keep .x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans primitive) fuel
  rw [show 141+fuel=136+(5+fuel) by omega,ordinary,finish]
  simp only [quadNode,bind_assoc,pure_bind,Execution.charge,Nat.zero_add,←Nat.add_assoc]
  rfl

/-- Entry jump plus the first pass: 142 instructions, 149 cycles, one query. -/
theorem execute_quad_node (s : MachineState) (slot : Fin 4) (proof fuel : Nat)
    (pc : s.pc=4336) (pair : s.getReg .x24=12544) (digest : s.getReg .x23=12288)
    (opened : s.getReg .x6 &&& (3#64)=BitVec.ofNat 64 slot.val)
    (src : s.getReg .x21=BitVec.ofNat 64 proof) (room : proof+96≤MEMORY_BYTES) (even : proof%2=0)
    (selector : s.getReg .x5=0) (size : s.getReg .x11=200) (primitive : s.getReg .x13=1) :
    execute packedImage (142+fuel) s false = do
      let finished ← quadNode s
      let result ← execute packedImage fuel finished false
      return result.charge 149 1 := by
  let begin := s.setPC 5564
  have body := execute_quad_body begin slot proof fuel rfl
    ((MachineState.getReg_setPC).trans pair) ((MachineState.getReg_setPC).trans digest)
    (by simpa only [begin,MachineState.getReg_setPC] using opened)
    ((MachineState.getReg_setPC).trans src) room even
    ((MachineState.getReg_setPC).trans selector) ((MachineState.getReg_setPC).trans size)
    ((MachineState.getReg_setPC).trans primitive)
  have node : quadNode begin=quadNode s := by
    unfold quadNode
    rfl
  rw [show 142+fuel=1+(141+fuel) by omega,quad_entry_hop s pc,body,node]
  simp only [bind_assoc,pure_bind,Execution.charge,Nat.zero_add,←Nat.add_assoc]

end TwoPermutationPrototype.Quad.Checker
