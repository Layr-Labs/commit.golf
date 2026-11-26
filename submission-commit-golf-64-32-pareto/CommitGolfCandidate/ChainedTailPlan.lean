import CommitGolfCandidate.ChainedTailSourceFrame

/-! Whole native tail traversal refines a byte-write plan from immutable rows. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
attribute [local irreducible] tailStepState

def storeByteFn (memory : Word → BitVec 8) (address : Word) (value : BitVec 8) : Word → BitVec 8 :=
  fun query => if query=address then value else memory query

def writeByteList (memory : Word → BitVec 8) (address : Word) : Proof → Word → BitVec 8
  | [] => memory
  | byte::rest => writeByteList (storeByteFn memory address byte) (address+1) rest

def tailPlanBytes (front : List Bool) : List (List Bool) → Proof
  | [] => []
  | back::rows =>
    let rest := tailPlanBytes (nextTailBits front back) rows
    if (front++back).length<8 then rest else tailBitsWord 8 (front++back)::rest

def tailPlanCarry (front : List Bool) : List (List Bool) → List Bool
  | [] => front
  | back::rows => tailPlanCarry (nextTailBits front back) rows

theorem native_tail_plan (rows : List (List Bool)) (front : List Bool) (s : MachineState)
    (buffer : TailBuffer s front) (small : ∀ row ∈ rows, row.length≤6)
    (memory : BytesAt s (s.getReg .x21) (descriptorBytes rows))
    (apart : TailApart (s.getReg .x21) (s.getReg .x20) rows) :
    TailBuffer (tailFieldsState rows.length s) (tailPlanCarry front rows) ∧
    (∀ query, (tailFieldsState rows.length s).getByte query=
      writeByteList s.getByte (s.getReg .x20) (tailPlanBytes front rows) query) ∧
    (tailFieldsState rows.length s).getReg .x20=
      s.getReg .x20+BitVec.ofNat 64 (tailPlanBytes front rows).length := by
  induction rows generalizing front s with
  | nil =>
    simp only [List.length_nil,tail_fields_state_zero,tailPlanCarry,tailPlanBytes,writeByteList]
    exact ⟨buffer,by simp,by simp⟩
  | cons back rows ih =>
    have bound := small back (by simp)
    have data := descriptor_memory_slot s (s.getReg .x21) (back::rows) memory 0 (by simp) (by simp)
    have nextBuffer := tail_step_buffer s front back buffer data.1 data.2 bound
    have nextMemory := tail_step_source_memory s front back rows buffer bound memory apart
    have nextApart := tail_step_apart s front back rows buffer bound memory apart
    have nextSmall : ∀ row ∈ rows, row.length≤6 := fun row member => small row (by simp [member])
    obtain ⟨finalBuffer,finalMemory,finalPointer⟩ := ih (nextTailBits front back) (tailStepState s)
      nextBuffer nextSmall nextMemory nextApart
    rw [List.length_cons,tail_fields_state_succ]
    refine ⟨finalBuffer,?_,?_⟩
    · by_cases fits : (front++back).length<8
      · have stepMemory : (tailStepState s).getByte=s.getByte := by
          funext query
          rw [tail_step_bits_byte s front back buffer.value buffer.count buffer.eight data.1 data.2 buffer.pending bound,
            ite_eq_left fits]
        rw [stepMemory,tail_step_bits_pointer s front back buffer data.1 data.2 bound,ite_eq_left fits] at finalMemory
        simpa only [tailPlanBytes,fits,↓reduceIte] using finalMemory
      · have stepMemory : (tailStepState s).getByte=storeByteFn s.getByte (s.getReg .x20) (tailBitsWord 8 (front++back)) := by
          funext query
          rw [tail_step_bits_byte s front back buffer.value buffer.count buffer.eight data.1 data.2 buffer.pending bound,
            ite_eq_right fits]
          rfl
        rw [stepMemory,tail_step_bits_pointer s front back buffer data.1 data.2 bound,ite_eq_right fits] at finalMemory
        simpa only [tailPlanBytes,fits,↓reduceIte,writeByteList] using finalMemory
    · rw [tail_step_bits_pointer s front back buffer data.1 data.2 bound] at finalPointer
      by_cases fits : (front++back).length<8
      · simpa only [tailPlanBytes,fits,↓reduceIte] using finalPointer
      · rw [ite_eq_right fits] at finalPointer
        have location : (s.getReg .x20+1)+BitVec.ofNat 64 (tailPlanBytes (nextTailBits front back) rows).length =
            s.getReg .x20+BitVec.ofNat 64 ((tailPlanBytes (nextTailBits front back) rows).length+1) := by
          change (s.getReg .x20+BitVec.ofNat 64 1)+BitVec.ofNat 64 _=_
          rw [byte_offset_add,Nat.add_comm 1]
        rw [location] at finalPointer
        simpa only [tailPlanBytes,fits,↓reduceIte,List.length_cons] using finalPointer

end CommitGolfCandidate.Chained.Native
