import CommitGolfCandidate.QuadNodePrefixMemory
import CommitGolfCandidate.QuadNodeRotationMemory
import CommitGolfCandidate.QuadNodeInput

namespace TwoPermutationPrototype.Quad.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
set_option maxRecDepth 8192
set_option maxHeartbeats 900000
attribute [local irreducible] ByteCopy.copyField ByteCopy.copyRun ByteCopy.copyStep quadSlotPrefix quadSlotLatch quadPrefix quadRotation

theorem quad_read_bytes_same (before after : MachineState) (source target count : Nat)
    (same : ∀ i<count, after.getByte (BitVec.ofNat 64 (target+i))=
      before.getByte (BitVec.ofNat 64 (source+i))) :
    readBuffer after target count=readBuffer before source count := by
  unfold readBuffer
  apply congrArg (BitVec.ofNat (8*count))
  apply Finset.sum_congr rfl
  intro i present
  rw [same i (Finset.mem_range.mp present)]

theorem quad_slot_address_ne (a b : Fin 4) (ne : a≠b) (i j : Nat) (hi : i<32) (hj : j<32) :
    BitVec.ofNat 64 (12872+32*a.val+i)≠BitVec.ofNat 64 (12872+32*b.val+j) := by
  have ha := a.isLt
  have hb := b.isLt
  apply quad_byte_address_ne _ _ (by omega) (by omega)
  intro same
  exact ne (Fin.ext (by omega))

/-- Rotated sibling writes preserve the opened slot. -/
theorem quad_rotation_opened (s : MachineState) (r : Fin 4) (proof : Nat)
    (pc : s.pc=5652) (base : s.getReg .x10=12800)
    (offset : s.getReg .x29=BitVec.ofNat 64 (32*r.val))
    (src : s.getReg .x21=BitVec.ofNat 64 proof) (counter : s.getReg .x30=3)
    (room : proof+96≤MEMORY_BYTES) (even : proof%2=0) (above : 32768≤proof) :
    readBuffer (quadRotation s) (12872+32*r.val) 32=readBuffer s (12872+32*r.val) 32 := by
  have bytes := quad_rotation_bytes s r proof pc base offset src counter room even above
  apply quad_read_bytes_same
  intro i hi
  apply bytes.2.2.2
  · intro j hj
    exact quad_slot_address_ne r (quadNextSlot r) (by fin_cases r <;> decide) i j hi hj
  · intro j hj
    exact quad_slot_address_ne r (quadNextSlot (quadNextSlot r)) (by fin_cases r <;> decide) i j hi hj
  · intro j hj
    exact quad_slot_address_ne r (quadNextSlot (quadNextSlot (quadNextSlot r))) (by fin_cases r <;> decide) i j hi hj

/-- The complete prefix-and-copy workspace used by the actual quad call. -/
def quadWorkspace (s : MachineState) : MachineState :=
  quadRotation (quadPrefix (s.setPC 5564) 22)

/-- Fully prepared actual workspace, with children at their ABI slot offsets. -/
theorem quad_workspace_input (s : MachineState) (slot : Fin 4) (proof : Nat)
    (pair : s.getReg .x24=12544) (digest : s.getReg .x23=12288)
    (opened : s.getReg .x6 &&& (3#64)=BitVec.ofNat 64 slot.val)
    (src : s.getReg .x21=BitVec.ofNat 64 proof)
    (room : proof+96≤MEMORY_BYTES) (even : proof%2=0) (above : 32768≤proof) :
    packBuffer (window (memoryView (quadWorkspace s)) 1600)=quadInput (workspaceChildren (quadWorkspace s)) ∧
      workspaceChildren (quadWorkspace s) slot=readBuffer s 12288 32 := by
  let begin := s.setPC 5564
  let p := quadPrefix begin 22
  have pairB : begin.getReg .x24=12544 := (MachineState.getReg_setPC).trans pair
  have digestB : begin.getReg .x23=12288 := (MachineState.getReg_setPC).trans digest
  have openedB : begin.getReg .x6 &&& (3#64)=BitVec.ofNat 64 slot.val := by simpa only [begin,MachineState.getReg_setPC] using opened
  have post := quad_prefix_post begin slot rfl pairB openedB
  have srcP : p.getReg .x21=BitVec.ofNat 64 proof :=
    (quad_prefix_register begin .x21 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((MachineState.getReg_setPC).trans src)
  have bytes := quad_rotation_bytes p slot proof post.1 post.2.1 post.2.2.2.1 srcP post.2.2.2.2 room even above
  have zeroFrame (i : Nat) (inside : i<9) : memoryView (quadRotation p) (1600+i)=memoryView p (1600+i) := by
    apply TwoPermutationPrototype.Packed.Checker.word_eq_of_byte_frame
    intro k hk
    apply bytes.2.2.2
    all_goals intro j hj
    all_goals apply quad_byte_address_ne _ _ (by omega) (by have := quad_target_bound slot; have := quad_target_bound (quadNextSlot slot); have := quad_target_bound (quadNextSlot (quadNextSlot slot)); omega)
    all_goals have := quad_target_bound slot
    all_goals have := quad_target_bound (quadNextSlot slot)
    all_goals have := quad_target_bound (quadNextSlot (quadNextSlot slot))
    all_goals omega
  constructor
  · apply workspace_quad_input
    intro i inside
    change memoryView (quadRotation p) (1600+i)=0
    rw [zeroFrame i inside]
    have z := quad_prefix_workspace_word begin slot pairB digestB openedB ⟨i,by omega⟩
    simpa only [Fin.val_mk,ite_eq_left inside] using z
  · change readBuffer (quadRotation p) (12872+32*slot.val) 32=readBuffer s 12288 32
    rw [quad_rotation_opened p slot proof post.1 post.2.1 post.2.2.2.1 srcP post.2.2.2.2 room even above,
      quad_prefix_opened begin slot pairB digestB openedB]
    rfl

private theorem quad_rotation_address (slot : Fin 4) (child : Nat) (which : child<3) :
    12872+32*((slot.val+child+1)%4) =
      if child=0 then quadTarget slot else if child=1 then quadTarget (quadNextSlot slot)
      else quadTarget (quadNextSlot (quadNextSlot slot)) := by
  fin_cases slot <;> interval_cases child <;> rfl

/-- All three sibling digest values in their final rotation slots come from the
original proof bytes, despite the successive in-place writes. -/
theorem quad_workspace_siblings (s : MachineState) (slot : Fin 4) (proof : Nat)
    (pair : s.getReg .x24=12544) (digest : s.getReg .x23=12288)
    (opened : s.getReg .x6 &&& (3#64)=BitVec.ofNat 64 slot.val)
    (src : s.getReg .x21=BitVec.ofNat 64 proof)
    (room : proof+96≤MEMORY_BYTES) (even : proof%2=0) (above : 32768≤proof)
    (child : Nat) (which : child<3) :
    workspaceChildren (quadWorkspace s) ⟨(slot.val+child+1)%4,Nat.mod_lt _ (by decide)⟩=
      readBuffer s (proof+32*child) 32 := by
  let begin := s.setPC 5564
  let p := quadPrefix begin 22
  have pairB : begin.getReg .x24=12544 := (MachineState.getReg_setPC).trans pair
  have digestB : begin.getReg .x23=12288 := (MachineState.getReg_setPC).trans digest
  have openedB : begin.getReg .x6 &&& (3#64)=BitVec.ofNat 64 slot.val := by simpa only [begin,MachineState.getReg_setPC] using opened
  have post := quad_prefix_post begin slot rfl pairB openedB
  have srcP : p.getReg .x21=BitVec.ofNat 64 proof :=
    (quad_prefix_register begin .x21 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((MachineState.getReg_setPC).trans src)
  have bytes := quad_rotation_bytes p slot proof post.1 post.2.1 post.2.2.2.1 srcP post.2.2.2.2 room even above
  have first := quad_read_bytes_same p (quadRotation p) proof (quadTarget slot) 32 bytes.1
  have second := quad_read_bytes_same p (quadRotation p) (proof+32) (quadTarget (quadNextSlot slot)) 32 bytes.2.1
  have third := quad_read_bytes_same p (quadRotation p) (proof+64) (quadTarget (quadNextSlot (quadNextSlot slot))) 32 bytes.2.2.1
  have initial (j : Nat) (small : j<3) : readBuffer p (proof+32*j) 32=readBuffer s (proof+32*j) 32 := by
    exact (quad_prefix_read_above begin slot pairB digestB openedB _ _ (by omega) (by omega)).trans rfl
  have d₀ := first.trans (by simpa only [Nat.mul_zero,Nat.add_zero] using initial 0 (by decide))
  have d₁ := second.trans (by simpa only [Nat.mul_one] using initial 1 (by decide))
  have d₂ := third.trans (by simpa only [show 32*2=64 by decide] using initial 2 (by decide))
  change readBuffer (quadRotation p) _ 32=readBuffer s _ 32
  have address := quad_rotation_address slot child which
  rw [address]
  interval_cases child
  · simpa only [ite_true,ite_false,ite_eq_left rfl,Nat.mul_zero,Nat.add_zero] using d₀
  · simpa only [ite_true,ite_false,show (1:Nat)≠0 by decide,ite_eq_right,ite_eq_left rfl,Nat.mul_one] using d₁
  · simpa only [ite_true,ite_false,show (2:Nat)≠0 by decide,show (2:Nat)≠1 by decide,ite_eq_right,show 32*2=64 by decide] using d₂


theorem quad_workspace_post (s : MachineState) (slot : Fin 4) (proof : Nat)
    (pair : s.getReg .x24=12544)
    (opened : s.getReg .x6 &&& (3#64)=BitVec.ofNat 64 slot.val)
    (src : s.getReg .x21=BitVec.ofNat 64 proof)
    (room : proof+96≤MEMORY_BYTES) (even : proof%2=0) :
    (quadWorkspace s).pc=5804 ∧ (quadWorkspace s).getReg .x10=12800 ∧
      (quadWorkspace s).getReg .x21=BitVec.ofNat 64 (proof+96) := by
  let begin := s.setPC 5564
  let p := quadPrefix begin 22
  have pairB : begin.getReg .x24=12544 := (MachineState.getReg_setPC).trans pair
  have openedB : begin.getReg .x6 &&& (3#64)=BitVec.ofNat 64 slot.val := by simpa only [begin,MachineState.getReg_setPC] using opened
  have post := quad_prefix_post begin slot rfl pairB openedB
  have srcP : p.getReg .x21=BitVec.ofNat 64 proof :=
    (quad_prefix_register begin .x21 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((MachineState.getReg_setPC).trans src)
  exact quad_rotation_post p slot proof post.1 post.2.1 post.2.2.2.1 srcP post.2.2.2.2 room even

theorem quad_workspace_register (s : MachineState) (slot : Fin 4) (proof : Nat)
    (pair : s.getReg .x24=12544)
    (opened : s.getReg .x6 &&& (3#64)=BitVec.ofNat 64 slot.val)
    (src : s.getReg .x21=BitVec.ofNat 64 proof)
    (room : proof+96≤MEMORY_BYTES) (even : proof%2=0)
    (reg : Reg) (a : reg≠.x10) (b : reg≠.x21) (c : reg≠.x28)
    (d : reg≠.x29) (f : reg≠.x30) (g : reg≠.x31) :
    (quadWorkspace s).getReg reg=s.getReg reg := by
  let begin := s.setPC 5564
  let p := quadPrefix begin 22
  have pairB : begin.getReg .x24=12544 := (MachineState.getReg_setPC).trans pair
  have openedB : begin.getReg .x6 &&& (3#64)=BitVec.ofNat 64 slot.val := by simpa only [begin,MachineState.getReg_setPC] using opened
  have post := quad_prefix_post begin slot rfl pairB openedB
  have srcP : p.getReg .x21=BitVec.ofNat 64 proof :=
    (quad_prefix_register begin .x21 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((MachineState.getReg_setPC).trans src)
  exact (quad_rotation_register p slot proof post.1 post.2.1 post.2.2.2.1 srcP post.2.2.2.2 room even
      reg b c d f g).trans
    ((quad_prefix_register begin reg a c d f g).trans MachineState.getReg_setPC)

/-- Actual quad workspace writes are restricted to the 25 scratch words. -/
theorem quad_workspace_frame (s : MachineState) (slot : Fin 4) (proof : Nat)
    (pair : s.getReg .x24=12544) (digest : s.getReg .x23=12288)
    (opened : s.getReg .x6 &&& (3#64)=BitVec.ofNat 64 slot.val)
    (src : s.getReg .x21=BitVec.ofNat 64 proof)
    (room : proof+96≤MEMORY_BYTES) (even : proof%2=0) (above : 32768≤proof)
    (word : Nat) (bounded : word<2^33) (outside : word<1600 ∨ 1625≤word) :
    memoryView (quadWorkspace s) word=memoryView s word := by
  let begin := s.setPC 5564
  let p := quadPrefix begin 22
  have pairB : begin.getReg .x24=12544 := (MachineState.getReg_setPC).trans pair
  have digestB : begin.getReg .x23=12288 := (MachineState.getReg_setPC).trans digest
  have openedB : begin.getReg .x6 &&& (3#64)=BitVec.ofNat 64 slot.val := by simpa only [begin,MachineState.getReg_setPC] using opened
  have post := quad_prefix_post begin slot rfl pairB openedB
  have srcP : p.getReg .x21=BitVec.ofNat 64 proof :=
    (quad_prefix_register begin .x21 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((MachineState.getReg_setPC).trans src)
  have bytes := quad_rotation_bytes p slot proof post.1 post.2.1 post.2.2.2.1 srcP post.2.2.2.2 room even above
  have prefixFrame : memoryView p word=memoryView s word := by
    apply Eq.trans (quad_prefix_word_frame begin slot pairB digestB openedB (wordAddress word) ?_) rfl
    intro j eq
    have same := wordAddress_injective_of_bound (by omega : word<2^61)
      (by have := j.isLt; omega : 1600+j.val<2^61) eq
    have := j.isLt
    omega
  apply Eq.trans (TwoPermutationPrototype.Packed.Checker.word_eq_of_byte_frame p (quadRotation p) word ?_) prefixFrame
  intro i hi
  apply bytes.2.2.2
  all_goals intro j hj
  all_goals apply quad_byte_address_ne _ _ (by omega) (by have := quad_target_bound slot; have := quad_target_bound (quadNextSlot slot); have := quad_target_bound (quadNextSlot (quadNextSlot slot)); omega)
  all_goals have := quad_target_bound slot
  all_goals have := quad_target_bound (quadNextSlot slot)
  all_goals have := quad_target_bound (quadNextSlot (quadNextSlot slot))
  all_goals omega

end TwoPermutationPrototype.Quad.Checker
