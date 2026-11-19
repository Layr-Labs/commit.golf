import CommitGolfCandidate.QuadLevel
import CommitGolfCandidate.TwoPermutationQuadSpec

namespace TwoPermutationPrototype.Quad.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Packed.Checker (RecordBlock RecordSaved LowerFrame LowerSaved)
open TwoPermutationPrototype.Packed.Checker (buffer_byte_frame)
set_option maxRecDepth 8192

/-- Quad2 records start with the salt, three rotated leaf neighbours and three rotated quad neighbours. -/
def checkProofByte (ordinal : Nat) : Nat := 11190423648+570*ordinal

def lowerNode (index : Index) (level : Nat) : Nat := Opening.lowerNode index (level+4)

theorem lower_node_next (index : Index) (level : Nat) :
    lowerNode index (level+1)=lowerNode index level/2 := by
  unfold lowerNode
  rw [show level+1+4=(level+4)+1 by omega,Opening.lower_node_next]

theorem lower_node_cap_group (index : Index) : lowerNode index 12=Sampling.capGroup index :=
  Opening.lower_node_cap_group index

def lowerProofByte (ordinal level : Nat) : Nat :=
  if level=0 then checkProofByte ordinal+208 else checkProofByte ordinal+240+30*(level-1)

def lowerSiblingWidth (level : Nat) : Nat := if level=0 then 32 else 30

def lowerWireSibling (state : MachineState) (ordinal level : Nat) : Digest :=
  if level=0 then readBuffer state (checkProofByte ordinal+208) 32
  else 0#16 ++ readBuffer state (checkProofByte ordinal+240+30*(level-1)) 30

theorem lower_proof_byte_next (ordinal level : Nat) :
    lowerProofByte ordinal (level+1)=lowerProofByte ordinal level+lowerSiblingWidth level := by
  by_cases h : level=0
  · subst level; simp [lowerProofByte,lowerSiblingWidth,Nat.add_assoc]
  · simp only [lowerProofByte,lowerSiblingWidth,h,ite_false,Nat.succ_ne_zero,Nat.add_sub_cancel]
    omega

theorem lower_proof_byte_end (ordinal : Nat) : lowerProofByte ordinal 12=checkProofByte (ordinal+1) := by
  unfold lowerProofByte checkProofByte
  simp only [show (12:Nat)≠0 by decide,ite_false]
  omega

theorem lower_proof_geometry (ordinal level : Nat) (inside : level<12)
    (room : checkProofByte ordinal+570≤MEMORY_BYTES) :
    32768≤lowerProofByte ordinal level ∧ lowerProofByte ordinal level%2=0 ∧
      lowerProofByte ordinal level+lowerSiblingWidth level≤MEMORY_BYTES := by
  by_cases first : level=0
  · simp only [lowerProofByte,lowerSiblingWidth,first,ite_true]
    unfold checkProofByte at room ⊢; omega
  · simp only [lowerProofByte,lowerSiblingWidth,first,ite_false]
    unfold checkProofByte at room ⊢; omega

theorem lower_width_from_counter (level : Nat) :
    lowerSiblingWidth level=if 12-level=12 then 32 else 30 := by
  unfold lowerSiblingWidth
  simp only [show 12-level=12 ↔ level=0 by omega]

theorem lower_wire_sibling_from_cursor (state : MachineState) (ordinal level : Nat) :
    lowerWireSibling state ordinal level=
      if 12-level=12 then readBuffer state (lowerProofByte ordinal level) 32
      else 0#16 ++ readBuffer state (lowerProofByte ordinal level) 30 := by
  simp only [show 12-level=12 ↔ level=0 by omega]
  by_cases first : level=0 <;> simp [lowerWireSibling,lowerProofByte,first]

theorem lower_wire_sibling_frame (before after : MachineState) (ordinal level : Nat)
    (frame : ∀ j<lowerSiblingWidth level,
      memoryView after ((lowerProofByte ordinal level+j)/8)=
      memoryView before ((lowerProofByte ordinal level+j)/8)) :
    lowerWireSibling after ordinal level=lowerWireSibling before ordinal level := by
  by_cases first : level=0
  · have words : ∀ j<32, memoryView after ((checkProofByte ordinal+208+j)/8)=
        memoryView before ((checkProofByte ordinal+208+j)/8) := by
      simpa only [lowerSiblingWidth,lowerProofByte,first,ite_true] using frame
    simpa only [lowerWireSibling,first,ite_true] using buffer_byte_frame before after _ 32 words
  · have words : ∀ j<30, memoryView after ((checkProofByte ordinal+240+30*(level-1)+j)/8)=
        memoryView before ((checkProofByte ordinal+240+30*(level-1)+j)/8) := by
      simpa only [lowerSiblingWidth,lowerProofByte,first,ite_false] using frame
    simp only [lowerWireSibling,first,ite_false,buffer_byte_frame before after _ 30 words]

end TwoPermutationPrototype.Quad.Checker
