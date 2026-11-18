import CommitGolfCandidate.QuadNodeLoop

namespace TwoPermutationPrototype.Quad.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open TwoPermutationPrototype.RV64
set_option maxRecDepth 8192
set_option maxHeartbeats 400000
attribute [local irreducible] ByteCopy.copyField ByteCopy.copyRun ByteCopy.copyStep

@[local simp] private theorem slot_zero (s : MachineState) : s.getReg .x0=0#64 := rfl

private theorem prefix_memory (s : MachineState) : (quadSlotPrefix s 3).mem=s.mem := rfl

private theorem latch_memory (s : MachineState) (left : Nat) (positive : 0<left) (bound : left≤3)
    (counter : s.getReg .x30=BitVec.ofNat 64 left) : (quadSlotLatch s 3).mem=s.mem := by
  interval_cases left <;>
    simp [quadSlotLatch,quadSlotLatchCode,execInstrBr,signExtend12,counter,MachineState.getReg_setPC,
      Opening.getReg_setReg]
  all_goals rfl

theorem quad_slot_saved (s : MachineState) (left : Nat) (positive : 0<left) (bound : left≤3)
    (counter : s.getReg .x30=BitVec.ofNat 64 left) (reg : Reg)
    (a : reg≠.x21) (b : reg≠.x28) (c : reg≠.x29) (d : reg≠.x30) (e : reg≠.x31) :
    (quadSlot s).getReg reg=s.getReg reg := by
  let p := quadSlotPrefix s 3
  let copied := ByteCopy.copyField quadSiblingCode p
  have count : copied.getReg .x30=BitVec.ofNat 64 left :=
    (ByteCopy.copy_field_register _ _ _ (by decide)).trans
      ((quad_slot_prefix_register _ _ (by decide) (by decide)).trans counter)
  exact (quad_slot_latch_register copied reg a d left positive bound count).trans
    ((ByteCopy.copy_field_register _ _ _ e).trans (quad_slot_prefix_register _ _ c b))

/-- The actual rotation iteration copies exactly the next proof digest and frames
all bytes outside its single 32-byte destination slot. -/
theorem quad_slot_bytes (s : MachineState) (r : Fin 4) (proof left : Nat)
    (positive : 0<left) (bound : left≤3) (pc : s.pc=5652) (base : s.getReg .x10=12800)
    (offset : s.getReg .x29=BitVec.ofNat 64 (32*r.val))
    (src : s.getReg .x21=BitVec.ofNat 64 proof) (counter : s.getReg .x30=BitVec.ofNat 64 left)
    (room : proof+32≤MEMORY_BYTES) (even : proof%2=0) (order : quadTarget r≤proof) :
    (∀ i<32, (quadSlot s).getByte (BitVec.ofNat 64 (quadTarget r+i))=
      s.getByte (BitVec.ofNat 64 (proof+i))) ∧
    (∀ q : Word, (∀ i<32, q≠BitVec.ofNat 64 (quadTarget r+i)) → (quadSlot s).getByte q=s.getByte q) := by
  let p := quadSlotPrefix s 3
  let copied := ByteCopy.copyField quadSiblingCode p
  have ready := quad_slot_ready s r proof pc base offset src room even
  have count : copied.getReg .x30=BitVec.ofNat 64 left :=
    (ByteCopy.copy_field_register _ _ _ (by decide)).trans
      ((quad_slot_prefix_register _ _ (by decide) (by decide)).trans counter)
  have copiedBytes : (∀ i<32, copied.getByte (BitVec.ofNat 64 (quadTarget r+i))=
      p.getByte (BitVec.ofNat 64 (proof+i))) ∧
      (∀ q : Word, (∀ i<32, q≠BitVec.ofNat 64 (quadTarget r+i)) → copied.getByte q=p.getByte q) :=
    ByteCopy.copy_field_bytes quadSiblingCode p proof (quadTarget r) ready order
  have lat : (quadSlot s).mem=copied.mem := latch_memory copied left positive bound count
  have pref : p.mem=s.mem := prefix_memory s
  have byteMem (a b : MachineState) (same : a.mem=b.mem) (q : Word) : a.getByte q=b.getByte q :=
    congrArg (fun mem : Word → Word => extractByte (mem (alignToDword q)) (byteOffset q)) same
  constructor
  · intro i inside
    exact (byteMem (quadSlot s) copied lat (BitVec.ofNat 64 (quadTarget r+i))).trans
      ((copiedBytes.1 i inside).trans (byteMem p s pref (BitVec.ofNat 64 (proof+i))))
  · intro q outside
    exact (byteMem (quadSlot s) copied lat q).trans
      ((copiedBytes.2 q outside).trans (byteMem p s pref q))

end TwoPermutationPrototype.Quad.Checker
