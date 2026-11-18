import CommitGolfCandidate.QuadNodeLoopControl

namespace TwoPermutationPrototype.Quad.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64
set_option maxRecDepth 16384
set_option maxHeartbeats 200000
attribute [local irreducible] execute ByteCopy.copyField ByteCopy.copyRun ByteCopy.copyStep quadSlotPrefix quadSlotLatch

theorem quad_slot_ready (s : MachineState) (r : Fin 4) (proof : Nat)
    (pc : s.pc=5652) (base : s.getReg .x10=12800)
    (offset : s.getReg .x29=BitVec.ofNat 64 (32*r.val))
    (src : s.getReg .x21=BitVec.ofNat 64 proof)
    (room : proof+32≤MEMORY_BYTES) (even : proof%2=0) :
    ByteCopy.CopyReady quadSiblingCode (quadSlotPrefix s 3) proof (quadTarget r) 0 := by
  obtain ⟨next,_,dst⟩ := quad_slot_prefix_post s r pc base offset
  refine ⟨next,(quad_slot_prefix_register _ _ (by decide) (by decide)).trans src,dst,room,?_,even,?_⟩
  · fin_cases r <;> decide
  · fin_cases r <;> decide

theorem quad_slot_hop (s : MachineState) (r : Fin 4) (proof left : Nat)
    (positive : 0<left) (bound : left≤3) (pc : s.pc=5652) (base : s.getReg .x10=12800)
    (offset : s.getReg .x29=BitVec.ofNat 64 (32*r.val))
    (src : s.getReg .x21=BitVec.ofNat 64 proof) (counter : s.getReg .x30=BitVec.ofNat 64 left)
    (room : proof+32≤MEMORY_BYTES) (even : proof%2=0) : GroupHop s (quadSlot s) 38 := by
  let p := quadSlotPrefix s 3
  let c := ByteCopy.copyField quadSiblingCode p
  have ready := quad_slot_ready s r proof pc base offset src room even
  have copied : GroupHop p c 32 := by
    intro fuel
    exact ByteCopy.copy_field_execute quadSiblingCode p proof (quadTarget r) ready fuel false
  have copyPc : c.pc=5792 := ByteCopy.copy_field_pc _ _ _ _ ready
  have copyCounter : c.getReg .x30=BitVec.ofNat 64 left :=
    (ByteCopy.copy_field_register _ _ _ (by decide)).trans
      ((quad_slot_prefix_register _ _ (by decide) (by decide)).trans counter)
  change GroupHop s (quadSlotLatch c 3) 38
  exact ((quad_slot_prefix_hop s pc).thenDo copied).thenDo
    (quad_slot_latch_hop c left positive bound copyPc copyCounter)

/-- Cursor after one of the three rotated child copies. -/
theorem quad_slot_post (s : MachineState) (r : Fin 4) (proof left : Nat)
    (positive : 0<left) (bound : left≤3) (pc : s.pc=5652) (base : s.getReg .x10=12800)
    (offset : s.getReg .x29=BitVec.ofNat 64 (32*r.val))
    (src : s.getReg .x21=BitVec.ofNat 64 proof) (counter : s.getReg .x30=BitVec.ofNat 64 left)
    (room : proof+32≤MEMORY_BYTES) (even : proof%2=0) :
    let t := quadSlot s
    t.pc=(if left=1 then 5804 else 5652) ∧ t.getReg .x10=12800 ∧
    t.getReg .x29=BitVec.ofNat 64 (32*(quadNextSlot r).val) ∧
    t.getReg .x21=BitVec.ofNat 64 (proof+32) ∧ t.getReg .x30=BitVec.ofNat 64 (left-1) := by
  let p := quadSlotPrefix s 3
  let c := ByteCopy.copyField quadSiblingCode p
  have ready := quad_slot_ready s r proof pc base offset src room even
  have pref := quad_slot_prefix_post s r pc base offset
  have copyPc : c.pc=5792 := ByteCopy.copy_field_pc _ _ _ _ ready
  have creg (reg : Reg) (kept : reg≠.x31) : c.getReg reg=p.getReg reg :=
    ByteCopy.copy_field_register _ _ _ kept
  have count : c.getReg .x30=BitVec.ofNat 64 left :=
    (creg .x30 (by decide)).trans ((quad_slot_prefix_register _ _ (by decide) (by decide)).trans counter)
  have lat := quad_slot_latch_post c left positive bound copyPc count
  change (quadSlotLatch c 3).pc=_ ∧ _
  refine ⟨lat.1,?_,?_,?_,lat.2.1⟩
  · exact (quad_slot_latch_register c .x10 (by decide) (by decide) left positive bound count).trans
      ((creg .x10 (by decide)).trans ((quad_slot_prefix_register _ _ (by decide) (by decide)).trans base))
  · exact (quad_slot_latch_register c .x29 (by decide) (by decide) left positive bound count).trans
      ((creg .x29 (by decide)).trans pref.2.1)
  · change (quadSlotLatch c 3).getReg .x21=_
    rw [lat.2.2,creg .x21 (by decide),quad_slot_prefix_register _ _ (by decide) (by decide),src]
    change BitVec.ofNat 64 proof+BitVec.ofNat 64 32=BitVec.ofNat 64 (proof+32)
    rw [←BitVec.ofNat_add]

/-- Three 38-instruction copies consume the 96-byte rotated sibling bundle. -/
def quadRotation (s : MachineState) : MachineState := quadSlot (quadSlot (quadSlot s))



theorem quad_rotation_hop (s : MachineState) (r : Fin 4) (proof : Nat)
    (pc : s.pc=5652) (base : s.getReg .x10=12800)
    (offset : s.getReg .x29=BitVec.ofNat 64 (32*r.val))
    (src : s.getReg .x21=BitVec.ofNat 64 proof) (counter : s.getReg .x30=3)
    (room : proof+96≤MEMORY_BYTES) (even : proof%2=0) : GroupHop s (quadRotation s) 114 := by
  have p := quad_slot_post s r proof 3 (by decide) (by decide) pc base offset src counter (by omega) even
  have q := quad_slot_post (quadSlot s) (quadNextSlot r) (proof+32) 2 (by decide) (by decide)
    p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 (by omega) (by omega)
  have first := quad_slot_hop s r proof 3 (by decide) (by decide) pc base offset src counter (by omega) even
  have second := quad_slot_hop (quadSlot s) (quadNextSlot r) (proof+32) 2 (by decide) (by decide)
    p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 (by omega) (by omega)
  have third := quad_slot_hop (quadSlot (quadSlot s)) (quadNextSlot (quadNextSlot r)) (proof+64) 1
    (by decide) (by decide) q.1 q.2.1 q.2.2.1
    (by simpa only [show proof+32+32=proof+64 by omega] using q.2.2.2.1)
    q.2.2.2.2 (by omega) (by omega)
  exact (first.thenDo second).thenDo third

end TwoPermutationPrototype.Quad.Checker
