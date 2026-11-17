import CommitGolfCandidate.TwoPermutationPackedTaglessLeafSpec
import CommitGolfCandidate.TwoPermutationPackedLeafOps

namespace TwoPermutationPrototype.RV64.PackedLeaves
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
def nonceWords (state : MachineState) (slot : Fin 4096) : Words 2 := fun i =>
  if i.val = 0 then state.getMem (state.getReg .x22 + (BitVec.ofNat 64 (16*(slot.val%256))-2047))
  else state.getMem (state.getReg .x22 + (BitVec.ofNat 64 (16*(slot.val%256) + 8)-2047))

private theorem address_one (start : Nat) : wordAddress start + 8 = wordAddress (start + 1) := by
  rw [wordAddress_add]; rfl

private theorem address_two (start : Nat) : wordAddress start + 16 = wordAddress (start + 2) := by
  rw [wordAddress_add]; rfl

private theorem address_three (start : Nat) : wordAddress start + 24 = wordAddress (start + 3) := by
  rw [wordAddress_add]; rfl

private theorem address_four (start : Nat) : wordAddress start + 32 = wordAddress (start + 4) := by
  rw [wordAddress_add]; rfl

private theorem address_twelve (start : Nat) : wordAddress start + 96 = wordAddress (start + 12) := by
  rw [wordAddress_add]; rfl

theorem first_header_memory (state : MachineState) (slot : Fin 4096) (start index atWord : Nat)
    (startBound : start + 24 < 2 ^ 61) (wordBound : atWord < 2 ^ 61)
    (source : state.getReg .x10 = wordAddress start) (tag : firstTag index = wordAddress start) :
    memoryView (firstMemory state slot) atWord = writeWindow (memoryView state) start
      (header index (nonceWords state slot)) atWord := by
  have b0 : start < 2 ^ 61 := by omega
  have b1 : start + 1 < 2 ^ 61 := by omega
  have b2 : start + 2 < 2 ^ 61 := by omega
  have b3 : start + 3 < 2 ^ 61 := by omega
  have b4 : start + 4 < 2 ^ 61 := by omega
  unfold firstMemory
  simp only [source, address_one, address_two, address_three, address_four]
  rw [header_as_stores, tag]
  simp only [memory_at_store b4 wordBound, memory_at_store b3 wordBound, memory_at_store b2 wordBound,
    memory_at_store b1 wordBound, memory_at_store b0 wordBound, writeWord]
  simp [nonceWords]

theorem first_call_input (state : MachineState) (slot : Fin 4096) (start index : Nat)
    (startBound : start + 24 < 2 ^ 61)
    (source : state.getReg .x10 = wordAddress start) (tag : firstTag index = wordAddress start)
    (firstDisjoint : ∀ offset ∈ ([0, 8, 16] : List Word),
      state.getReg .x22 + (BitVec.ofNat 64 (16*(slot.val%256))-2047) ≠ state.getReg .x10 + offset)
    (secondDisjoint : ∀ offset ∈ ([0, 8, 16, 24] : List Word),
      state.getReg .x22 + (BitVec.ofNat 64 (16*(slot.val%256) + 8)-2047) ≠ state.getReg .x10 + offset) :
    let before := (firstInstructions slot).foldl execInstrBr state
    window (memoryView before) start = firstInput index (nonceWords state slot) (window (memoryView state) (start + 5)) := by
  rw [← first_window]
  funext i
  have execution := (first_execution state slot firstDisjoint secondDisjoint).1
  change ((firstInstructions slot).foldl execInstrBr state).getMem (wordAddress (start + i.val)) = _
  rw [MachineState.getMem, execution]
  change memoryView (firstMemory state slot) (start + i.val) = _
  exact first_header_memory state slot start index (start + i.val) startBound (by omega) source tag

theorem second_call_input (original afterFirst : MachineState) (slot : Fin 4096) (start index : Nat)
    (nonce : Words 2) (reply : Words 25)
    (afterMemory : ∀ i < 25, memoryView afterFirst (start+12+i) =
      writeWindow (writeWindow (memoryView original) start (header index nonce)) start reply (start+12+i)) :
    let before := (secondInstructions slot).foldl execInstrBr afterFirst
    window (memoryView before) (start+12) = taglessSecondInput reply (window (memoryView original) (start+5)) := by
  rw [←tagless_second_window (memoryView original) start index nonce reply]
  funext i
  have same := (second_execution afterFirst slot).1
  change ((secondInstructions slot).foldl execInstrBr afterFirst).mem (wordAddress (start+12+i.val)) = _
  rw [same]
  exact afterMemory i.val i.isLt

end TwoPermutationPrototype.RV64.PackedLeaves
