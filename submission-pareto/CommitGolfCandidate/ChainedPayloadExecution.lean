import CommitGolfCandidate.ChainedPayloadMemory

/-! Couple complete native tail execution to exact record/footer output memory. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp SplitCodec
attribute [local irreducible] execute

theorem native_traverse_payload_bytes_at {spec : Spec} (payload : Payload spec) (s : MachineState) (base : Word)
    (aligned : ∀ field ∈ spec, field.1%8=0) (small : ∀ field ∈ spec, field.2≤6)
    (buffer : TailBuffer s []) (cursor : s.getReg .x20=base+BitVec.ofNat 64 (lowBytes payload).length)
    (body : BytesAt s base (lowBytes payload))
    (memory : BytesAt s (s.getReg .x21) (descriptorBytes (highRows payload)))
    (apart : TailApart (s.getReg .x21) (s.getReg .x20) (highRows payload))
    (fit : (encode payload).length<2^64) :
    BytesAt (tailTraverseState spec.length s) base (encode payload) := by
  have entryByte (query : Word) : (tailEntryState s).getByte query=s.getByte query := by
    simp only [MachineState.getByte,tail_entry_memory]
  have entryBuffer : TailBuffer (tailEntryState s) [] := by
    constructor
    · simpa only [tail_entry_register] using buffer.value
    · simpa only [tail_entry_register] using buffer.count
    · simpa only [tail_entry_register] using buffer.eight
    · exact buffer.pending
  have entryBody : BytesAt (tailEntryState s) base (lowBytes payload) := by
    intro index inside
    rw [entryByte]
    exact body index inside
  have entryMemory : BytesAt (tailEntryState s) ((tailEntryState s).getReg .x21) (descriptorBytes (highRows payload)) := by
    intro index inside
    rw [tail_entry_register,entryByte]
    exact memory index inside
  have entryCursor : (tailEntryState s).getReg .x20=base+BitVec.ofNat 64 (lowBytes payload).length := by
    simpa only [tail_entry_register] using cursor
  have entryApart : TailApart ((tailEntryState s).getReg .x21) ((tailEntryState s).getReg .x20) (highRows payload) := by
    simpa only [tail_entry_register] using apart
  exact native_payload_bytes_at payload (tailEntryState s) base aligned small entryBuffer entryCursor entryBody entryMemory entryApart fit

theorem native_traverse_payload_execution {spec : Spec} (payload : Payload spec)
    (image : Image) (codeBase : Word) (code : TailTraverseAt image codeBase)
    (s : MachineState) (base : Word) (pc : s.pc=codeBase)
    (count : tailNoFields s=decide (spec.length=0)) (ready : TailFieldsReady spec.length (tailEntryState s))
    (valid : ¬tailEmpty (tailFieldsState spec.length (tailEntryState s)) →
      accessValid ((tailFieldsState spec.length (tailEntryState s)).getReg .x20) 1=true)
    (aligned : ∀ field ∈ spec, field.1%8=0) (small : ∀ field ∈ spec, field.2≤6)
    (buffer : TailBuffer s []) (cursor : s.getReg .x20=base+BitVec.ofNat 64 (lowBytes payload).length)
    (body : BytesAt s base (lowBytes payload))
    (memory : BytesAt s (s.getReg .x21) (descriptorBytes (highRows payload)))
    (apart : TailApart (s.getReg .x21) (s.getReg .x20) (highRows payload))
    (fit : (encode payload).length<2^64) (fuel : Nat) (coins : Bool) :
    execute image (tailTraverseCycles spec.length s+fuel) s coins =
      (do let result ← execute image fuel (tailTraverseState spec.length s) coins
          return result.charge (tailTraverseCycles spec.length s) 0) ∧
    BytesAt (tailTraverseState spec.length s) base (encode payload) ∧
    tailTraverseCycles spec.length s≤13*spec.length+4 := by
  exact ⟨tail_traverse_execution image codeBase code spec.length s pc count ready valid fuel coins,
    native_traverse_payload_bytes_at payload s base aligned small buffer cursor body memory apart fit,
    tail_traverse_bound spec.length s⟩

theorem native_empty_tail_memory (s : MachineState) (buffer : TailBuffer s []) (query : Word) :
    (tailTraverseState 0 s).getByte query=s.getByte query := by
  have entryByte (address : Word) : (tailEntryState s).getByte address=s.getByte address := by
    simp only [MachineState.getByte,tail_entry_memory]
  have entryBuffer : TailBuffer (tailEntryState s) [] := by
    constructor
    · simpa only [tail_entry_register] using buffer.value
    · simpa only [tail_entry_register] using buffer.count
    · simpa only [tail_entry_register] using buffer.eight
    · exact buffer.pending
  have result := native_tail_memory [] [] (tailEntryState s) entryBuffer (by simp)
    (by intro index inside; simp [descriptorBytes] at inside) (by intro index inside; simp [TailApart] at inside) query
  simpa only [List.length_nil,List.flatten_nil,List.nil_append,packedBits,SplitCodec.packBits,
    writeByteList,tailTraverseState] using result.trans (entryByte query)

end CommitGolfCandidate.Chained.Native
