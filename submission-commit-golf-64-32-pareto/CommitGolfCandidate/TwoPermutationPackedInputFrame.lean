import CommitGolfCandidate.TwoPermutationPackedCheckCursor

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open TwoPermutationPrototype.RV64
open TwoPermutationPrototype.Checker (checkIndexWord checkSourceWord checker_positions_bound
  RecordInputAddress RecordInputFrame)

/-- Packed records and their footer may begin between two consecutive aligned words. -/
theorem byte_frame (before after : MachineState) (address : Nat)
    (unchanged : memoryView after (address/8) = memoryView before (address/8)) :
    after.getByte (BitVec.ofNat 64 address) = before.getByte (BitVec.ofNat 64 address) := by
  have addr : 8*(address/8)+address%8=address := by omega
  have fit : address%8<64 := by omega
  have a := aligned_byte after (address/8) (address%8) fit
  have b := aligned_byte before (address/8) (address%8) fit
  rw [addr, Nat.div_eq_of_lt (show address%8<8 from by omega), Nat.mul_zero, Nat.add_zero] at a b
  rw [a,b]
  exact congrArg (fun word : Word => extractByte word (address%8%8)) unchanged

theorem buffer_byte_frame (before after : MachineState) (address count : Nat)
    (unchanged : ∀ j < count, memoryView after ((address+j)/8) = memoryView before ((address+j)/8)) :
    readBuffer after address count = readBuffer before address count := by
  unfold readBuffer
  congr 1
  apply Finset.sum_congr rfl
  intro j inside
  rw [byte_frame before after _ (unchanged j (Finset.mem_range.mp inside))]

theorem packed_input_address_after (input : CheckInput) (ordinal word : Nat)
    (used : RecordInputAddress input (ordinal+1) word) :
    (word < checkSourceWord ordinal ∨ checkSourceWord ordinal+37 ≤ word) ∧
      1576 ≤ word := by
  have card := checker_positions_bound input
  rcases used with ⟨first, last⟩ | ⟨first, last⟩ | source
  · unfold checkSourceWord
    omega
  · unfold checkIndexWord at first last
    unfold checkSourceWord
    omega
  · unfold checkSourceWord at *
    omega

private theorem physical_proof_frame (input : CheckInput) (ordinal offset count : Nat) (state : MachineState)
    (frame : RecordInputFrame input ordinal state) (before : ordinal ≤ input.positions.card)
    (bounded : checkProofByte ordinal+offset+count ≤ 2^36) :
    readBuffer state (checkProofByte ordinal+offset) count =
      readBuffer (Assembly.submission.initialState .check input) (checkProofByte ordinal+offset) count := by
  apply buffer_byte_frame
  intro j inside
  have card := checker_positions_bound input
  apply frame _ (by omega)
  exact Or.inr (Or.inr (by unfold checkSourceWord checkProofByte; omega))

/-- The decoder fills missing bytes up to the maximum frontier length. A
malformed wire can put arbitrary values there. The proof-end register still
limits the checker to input.proof; the extra bytes are only a memory witness. -/
def InputFrame (input : CheckInput) (i : Nat) (s : MachineState) : Prop :=
  ∃ tail : Proof, input.proof.length+tail.length≤Assembly.submission.sizes.proof ∧
    RecordInputFrame {input with proof:=input.proof++tail} i s

theorem frame_index (input : CheckInput) (i : Nat) (hi : i< input.positions.card) (s : MachineState)
    (f : InputFrame input i s) :
    memoryView s (checkIndexWord i)=BitVec.ofNat 64 (TwoPermutationPrototype.Checker.honestIndex input.positions i hi).val.val := by
  obtain ⟨tail,_,mem⟩:=f
  exact TwoPermutationPrototype.Checker.record_input_index {input with proof:=input.proof++tail} i hi s mem

theorem frame_value (input : CheckInput) (i : Nat) (hi : i< input.positions.card) (s : MachineState)
    (f : InputFrame input i s) :
    readBuffer s (8*(checkSourceWord i+5)) 256=input.values (TwoPermutationPrototype.Checker.honestIndex input.positions i hi) := by
  obtain ⟨tail,_,mem⟩:=f
  exact TwoPermutationPrototype.Checker.record_input_value {input with proof:=input.proof++tail} i hi s mem

theorem frame_root (input : CheckInput) (i : Nat) (s : MachineState) (f : InputFrame input i s) :
    readBuffer s Assembly.submission.layout.commitment 32=input.commitment := by
  obtain ⟨tail,_,mem⟩:=f
  exact TwoPermutationPrototype.Checker.record_input_root {input with proof:=input.proof++tail} i s mem

theorem frame_step (input : CheckInput) (ordinal : Nat) (s t : MachineState) (f : InputFrame input ordinal s)
    (words : ∀ w<2^33,RecordInputAddress input (ordinal+1) w → memoryView t w=memoryView s w) :
    InputFrame input (ordinal+1) t := by
  obtain ⟨tail,size,mem⟩:=f
  exact ⟨tail,size,TwoPermutationPrototype.Checker.record_input_frame_step _ ordinal s t mem words⟩

section
attribute [local irreducible] Submission.initialState
set_option maxHeartbeats 1500000

theorem record_proof_frame (input : CheckInput) (ordinal offset count : Nat) (state : MachineState)
    (framed : InputFrame input ordinal state) (before : ordinal≤ input.positions.card)
    (bounded : checkProofByte ordinal+offset+count≤2^36)
    (within : 500*ordinal+offset+count≤ input.proof.length) :
    readBuffer state (checkProofByte ordinal+offset) count =
      readBuffer (Assembly.submission.initialState .check input) (checkProofByte ordinal+offset) count := by
  obtain ⟨tail,size,frame⟩:=framed
  let ext:CheckInput:={input with proof:=input.proof++tail}
  have room : ext.proof.length≤Assembly.submission.sizes.proof := by simpa [ext] using size
  refine (physical_proof_frame ext ordinal offset count state frame before bounded).trans ?_
  unfold readBuffer
  congr 1;apply Finset.sum_congr rfl
  intro j hj
  have jBound:=Finset.mem_range.mp hj
  let k:=500*ordinal+offset+j
  have member : k< input.proof.length := by dsimp [k];omega
  have extBound : k<ext.proof.length := by simp [ext];omega
  have address : checkProofByte ordinal+offset+j=Assembly.submission.layout.proof+k := by
    change 10334769248+500*ordinal+offset+j=10334769248+(500*ordinal+offset+j);omega
  have l:=TwoPermutationPrototype.Checker.check_input_proof_byte ext room k extBound
  have right:=TwoPermutationPrototype.Checker.check_input_proof_byte input (by omega) k member
  have agree : ext.proof[k]=input.proof[k] := List.getElem_append_left member
  rw [address]
  exact congrArg (fun v : Byte=>v.toNat*2^(8*j)) (l.trans (agree.trans right.symm))

end
end TwoPermutationPrototype.Packed.Checker
