import CommitGolfCandidate.ChainedTailPlan
import CommitGolfCandidate.ChainedRawField

/-! Derive complete native tail readiness and final-byte access from finite memory ranges. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
attribute [local irreducible] tailStepState

theorem tail_apart_of_ranges (source destination : Nat) (rows : List (List Bool))
    (separate : destination+rows.length<source) (room : source+2*rows.length≤MEMORY_BYTES) :
    TailApart (BitVec.ofNat 64 source) (BitVec.ofNat 64 destination) rows := by
  intro index inside offset bounded
  rw [←BitVec.ofNat_add,←BitVec.ofNat_add]
  apply word_of_nat_ne
  · unfold MEMORY_BYTES at room; omega
  · unfold MEMORY_BYTES at room; omega
  · omega

theorem tail_rows_access (rows : List (List Bool)) (front : List Bool) (s : MachineState)
    (source destination : Nat) (buffer : TailBuffer s front)
    (small : ∀ row ∈ rows, row.length≤6)
    (memory : BytesAt s (s.getReg .x21) (descriptorBytes rows))
    (sourcePointer : s.getReg .x21=BitVec.ofNat 64 source)
    (outputPointer : s.getReg .x20=BitVec.ofNat 64 destination)
    (count : s.getReg .x22=BitVec.ofNat 64 rows.length)
    (separate : destination+rows.length<source)
    (sourceRoom : source+2*rows.length≤MEMORY_BYTES)
    (outputRoom : destination+rows.length+1≤MEMORY_BYTES) :
    TailFieldsReady rows.length s ∧
    accessValid ((tailFieldsState rows.length s).getReg .x20) 1=true := by
  induction rows generalizing front s source destination with
  | nil =>
    refine ⟨trivial,?_⟩
    rw [List.length_nil,tail_fields_state_zero,outputPointer]
    have numeric : (BitVec.ofNat 64 destination).toNat=destination := by
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt]; unfold MEMORY_BYTES at outputRoom; omega
    simpa using byte_access_offset (BitVec.ofNat 64 destination) 0 (by rw [numeric]; simpa using outputRoom)
  | cons back rows ih =>
    have bound := small back (by simp)
    have apart : TailApart (s.getReg .x21) (s.getReg .x20) (back::rows) := by
      rw [sourcePointer,outputPointer]
      exact tail_apart_of_ranges source destination _ separate sourceRoom
    have data := descriptor_memory_slot s (s.getReg .x21) (back::rows) memory 0 (by simp) (by simp)
    have nextBuffer := tail_step_buffer s front back buffer data.1 data.2 bound
    have nextMemory := tail_step_source_memory s front back rows buffer bound memory apart
    have nextSource : (tailStepState s).getReg .x21=BitVec.ofNat 64 (source+2) := by
      rw [tail_step_source,sourcePointer,BitVec.ofNat_add]
      rfl
    have decreased : (tailStepDecreased s).getReg .x22=BitVec.ofNat 64 rows.length := by
      rw [tailStepDecreased,tail_decrease_count,tailStepEmitted,
        tail_emit_frame _ .x22 (by decide) (by decide) (by decide) (by decide),
        tail_load_frame s .x22 (by decide) (by decide) (by decide),count]
      have fit : 1<2^64 := by decide
      have result := BitVec.ofNat_sub_ofNat_of_le (back::rows).length 1 fit (by simp)
      have one : (1 : Word)=BitVec.ofNat 64 1 := by decide
      rw [one]
      simpa only [List.length_cons,Nat.add_sub_cancel] using result
    have nextCount : (tailStepState s).getReg .x22=BitVec.ofNat 64 rows.length := by
      rw [tailStepState,tail_back_register]
      exact decreased
    have more : tailMore (tailStepDecreased s)=decide (rows.length≠0) := by
      have fit : rows.length<2^64 := by simp only [List.length_cons] at sourceRoom; unfold MEMORY_BYTES at sourceRoom; omega
      rw [tailMore,decreased]
      change (!(rows.length%2^64 == 0))=decide (rows.length≠0)
      rw [Nat.mod_eq_of_lt fit]
      cases rows <;> rfl
    have recurse (step : Nat) (stepBound : step≤1)
        (nextOutput : (tailStepState s).getReg .x20=BitVec.ofNat 64 (destination+step)) :=
      ih (nextTailBits front back) (tailStepState s) (source+2) (destination+step) nextBuffer
        (fun row member => small row (by simp [member])) nextMemory nextSource nextOutput nextCount
        (by simp only [List.length_cons] at separate; omega)
        (by simp only [List.length_cons] at sourceRoom; omega)
        (by simp only [List.length_cons] at outputRoom; omega)
    have result : TailFieldsReady rows.length (tailStepState s) ∧
        accessValid ((tailFieldsState rows.length (tailStepState s)).getReg .x20) 1=true := by
      have pointer := tail_step_bits_pointer s front back buffer data.1 data.2 bound
      by_cases fits : (front++back).length<8
      · rw [ite_eq_left fits,outputPointer] at pointer
        exact recurse 0 (by decide) (by simpa using pointer)
      · rw [ite_eq_right fits,outputPointer] at pointer
        have one : (1 : Word)=BitVec.ofNat 64 1 := by decide
        rw [one,←BitVec.ofNat_add] at pointer
        exact recurse 1 (by decide) pointer
    have numeric : (s.getReg .x21).toNat=source := by
      rw [sourcePointer,BitVec.toNat_ofNat,Nat.mod_eq_of_lt]; unfold MEMORY_BYTES at sourceRoom; omega
    have outNumeric : (s.getReg .x20).toNat=destination := by
      rw [outputPointer,BitVec.toNat_ofNat,Nat.mod_eq_of_lt]; unfold MEMORY_BYTES at outputRoom; omega
    refine ⟨⟨?_,?_,?_,more,result.1⟩,?_⟩
    · simpa using byte_access_offset (s.getReg .x21) 0 (by rw [numeric]; simp only [List.length_cons] at sourceRoom; omega)
    · exact byte_access_offset (s.getReg .x21) 1 (by rw [numeric]; simp only [List.length_cons] at sourceRoom; omega)
    · intro _
      rw [tail_load_frame s .x20 (by decide) (by decide) (by decide)]
      simpa using byte_access_offset (s.getReg .x20) 0 (by rw [outNumeric]; simp only [List.length_cons] at outputRoom; omega)
    · simpa only [List.length_cons,tail_fields_state_succ] using result.2

theorem tail_step_output_increment (s : MachineState) :
    ∃ increment : Nat, increment≤1 ∧
      (tailStepState s).getReg .x20=s.getReg .x20+BitVec.ofNat 64 increment := by
  rw [tailStepState,tail_back_register,tailStepDecreased,
    tail_decrease_frame _ .x20 (by decide),tailStepEmitted,tailEmitState]
  split
  · refine ⟨0,by decide,?_⟩
    rw [tail_guard_register,
      tail_append_frame _ .x20 (by decide) (by decide) (by decide),
      tail_load_frame _ .x20 (by decide) (by decide) (by decide)]
    exact (BitVec.add_zero _).symm
  · refine ⟨1,by decide,?_⟩
    rw [tail_flush_pointer,tail_guard_register,
      tail_append_frame _ .x20 (by decide) (by decide) (by decide),
      tail_load_frame _ .x20 (by decide) (by decide) (by decide)]
    rfl

theorem tail_step_decreased_counter (s : MachineState) :
    (tailStepDecreased s).getReg .x22=(tailStepState s).getReg .x22 := by
  rw [tailStepState,tail_back_register]

theorem tail_fields_range_access (n : Nat) (s : MachineState) (source destination : Nat)
    (sourcePointer : s.getReg .x21=BitVec.ofNat 64 source)
    (outputPointer : s.getReg .x20=BitVec.ofNat 64 destination)
    (count : s.getReg .x22=BitVec.ofNat 64 n)
    (sourceRoom : source+2*n≤MEMORY_BYTES)
    (outputRoom : destination+n+1≤MEMORY_BYTES) :
    TailFieldsReady n s ∧
      accessValid ((tailFieldsState n s).getReg .x20) 1=true ∧
      ∃ increment : Nat, increment≤n ∧
        (tailFieldsState n s).getReg .x20=BitVec.ofNat 64 (destination+increment) := by
  induction n generalizing s source destination with
  | zero =>
    rw [tail_fields_state_zero]
    refine ⟨trivial,?_,0,by omega,by simpa using outputPointer⟩
    rw [outputPointer]
    have numeric : (BitVec.ofNat 64 destination).toNat=destination := by
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt]
      unfold MEMORY_BYTES at outputRoom
      omega
    simpa using byte_access_offset (BitVec.ofNat 64 destination) 0 (by rw [numeric]; omega)
  | succ n ih =>
    have nextSource : (tailStepState s).getReg .x21=BitVec.ofNat 64 (source+2) := by
      rw [tail_step_source,sourcePointer,BitVec.ofNat_add]
      rfl
    have nextCount : (tailStepState s).getReg .x22=BitVec.ofNat 64 n := by
      rw [tail_step_counter,count]
      have one : (1 : Word)=BitVec.ofNat 64 1 := by decide
      rw [one]
      have result := BitVec.ofNat_sub_ofNat_of_le (n+1) 1 (by decide : 1<2^64) (by omega)
      simpa only [Nat.add_sub_cancel] using result
    have decreased : (tailStepDecreased s).getReg .x22=BitVec.ofNat 64 n := by
      rw [tail_step_decreased_counter,nextCount]
    have more : tailMore (tailStepDecreased s)=decide (n≠0) := by
      have fit : n<2^64 := by unfold MEMORY_BYTES at sourceRoom; omega
      rw [tailMore,decreased]
      change (!(n%2^64 == 0))=decide (n≠0)
      rw [Nat.mod_eq_of_lt fit]
      by_cases empty : n=0 <;> simp [empty]
    obtain ⟨step,stepBound,stepOutput⟩ := tail_step_output_increment s
    have nextOutput : (tailStepState s).getReg .x20=BitVec.ofNat 64 (destination+step) := by
      rw [stepOutput,outputPointer,BitVec.ofNat_add]
    obtain ⟨ready,valid,increment,incrementBound,output⟩ :=
      ih (tailStepState s) (source+2) (destination+step) nextSource nextOutput nextCount
        (by omega) (by omega)
    have numeric : (s.getReg .x21).toNat=source := by
      rw [sourcePointer,BitVec.toNat_ofNat,Nat.mod_eq_of_lt]
      unfold MEMORY_BYTES at sourceRoom
      omega
    have outNumeric : (s.getReg .x20).toNat=destination := by
      rw [outputPointer,BitVec.toNat_ofNat,Nat.mod_eq_of_lt]
      unfold MEMORY_BYTES at outputRoom
      omega
    refine ⟨⟨?_,?_,?_,more,ready⟩,?_,step+increment,by omega,?_⟩
    · simpa using byte_access_offset (s.getReg .x21) 0 (by rw [numeric]; omega)
    · exact byte_access_offset (s.getReg .x21) 1 (by rw [numeric]; omega)
    · intro _
      rw [tail_load_frame s .x20 (by decide) (by decide) (by decide)]
      simpa using byte_access_offset (s.getReg .x20) 0 (by rw [outNumeric]; omega)
    · simpa only [tail_fields_state_succ] using valid
    · simpa only [tail_fields_state_succ,Nat.add_assoc] using output

theorem tail_finish_output_increment (s : MachineState) :
    ∃ increment : Nat, increment≤1 ∧
      (tailFinishState s).getReg .x20=s.getReg .x20+BitVec.ofNat 64 increment := by
  rw [tailFinishState]
  split
  · refine ⟨0,by decide,?_⟩
    rw [tail_finish_guard_register]
    exact (BitVec.add_zero _).symm
  · refine ⟨1,by decide,?_⟩
    change (tailFinishGuard s).getReg .x20+1=_
    rw [tail_finish_guard_register]
    rfl

theorem tail_traverse_range_execution (image : Image) (base : Word)
    (code : TailTraverseAt image base) (n : Nat) (s : MachineState)
    (source destination : Nat) (pc : s.pc=base)
    (sourcePointer : s.getReg .x21=BitVec.ofNat 64 source)
    (outputPointer : s.getReg .x20=BitVec.ofNat 64 destination)
    (count : s.getReg .x22=BitVec.ofNat 64 n)
    (sourceRoom : source+2*n≤MEMORY_BYTES)
    (outputRoom : destination+n+1≤MEMORY_BYTES) :
    (∀ fuel coins, execute image (tailTraverseCycles n s+fuel) s coins=
      (do let result ← execute image fuel (tailTraverseState n s) coins
          return result.charge (tailTraverseCycles n s) 0)) ∧
    (tailTraverseState n s).pc=base+68 ∧
    ∃ increment : Nat, increment≤n+1 ∧
      (tailTraverseState n s).getReg .x20=BitVec.ofNat 64 (destination+increment) := by
  have fit : n<2^64 := by unfold MEMORY_BYTES at sourceRoom; omega
  have empty : tailNoFields s=decide (n=0) := by
    rw [tailNoFields,count]
    change (n%2^64 == 0)=decide (n=0)
    rw [Nat.mod_eq_of_lt fit]
    by_cases zero : n=0 <;> simp [zero]
  obtain ⟨ready,valid,increment,bound,output⟩ := tail_fields_range_access n (tailEntryState s)
    source destination (by rw [tail_entry_register,sourcePointer])
    (by rw [tail_entry_register,outputPointer]) (by rw [tail_entry_register,count]) sourceRoom outputRoom
  have entryPC : (tailEntryState s).pc=if n=0 then base+56 else base+4 := by
    rw [tail_entry_pc,pc,empty]
    by_cases zero : n=0 <;> simp [zero]
  refine ⟨fun fuel coins => tail_traverse_execution image base code n s pc empty ready
    (fun _ => valid) fuel coins,tail_fields_finish_pc n _ base entryPC ready,?_⟩
  obtain ⟨last,lastBound,lastOutput⟩ := tail_finish_output_increment (tailFieldsState n (tailEntryState s))
  refine ⟨increment+last,by omega,?_⟩
  change (tailFinishState (tailFieldsState n (tailEntryState s))).getReg .x20=_
  rw [lastOutput,output,←BitVec.ofNat_add,Nat.add_assoc]

end CommitGolfCandidate.Chained.Native
