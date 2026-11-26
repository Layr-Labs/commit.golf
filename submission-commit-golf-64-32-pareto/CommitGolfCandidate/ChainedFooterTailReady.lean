import CommitGolfCandidate.ChainedFooterPayload
import CommitGolfCandidate.ChainedPayloadExecution
import CommitGolfCandidate.ChainedTailAccess

/-! Derive variable-footer traversal access from the completed DFS memory view. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp SplitCodec
set_option maxRecDepth 8192
attribute [local irreducible] execute

structure FooterTailReady (nodes : List Nat) (footer : Payload (InteriorCodec.footerSpec nodes))
    (s : MachineState) (output metadata : Nat) : Prop where
  buffer : TailBuffer s []
  cursor : s.getReg .x20=BitVec.ofNat 64 (output+(lowBytes footer).length)
  source : s.getReg .x21=BitVec.ofNat 64 metadata
  count : s.getReg .x22=BitVec.ofNat 64 nodes.length
  body : BytesAt s (BitVec.ofNat 64 output) (lowBytes footer)
  rows : BytesAt s (BitVec.ofNat 64 metadata) (descriptorBytes (highRows footer))
  apart : TailApart (s.getReg .x21) (s.getReg .x20) (highRows footer)
  ready : TailFieldsReady nodes.length (tailEntryState s)
  access : accessValid ((tailFieldsState nodes.length (tailEntryState s)).getReg .x20) 1=true
  countFit : nodes.length<2^64

theorem footer_tail_ready (groups nodes : List Nat) (footer : Payload (InteriorCodec.footerSpec nodes))
    (suffix oldPrefix : Proof) (s : MachineState) (node source outputBase metadata : Nat)
    (input : FooterReady groups [] suffix (oldPrefix++lowBytes footer) (descriptorBytes (highRows footer))
      s node source outputBase metadata)
    (gap : outputBase+oldPrefix.length+(lowBytes footer).length+nodes.length<metadata) :
    FooterTailReady nodes footer (footerTailSetupPrefix s 7) (outputBase+oldPrefix.length) metadata := by
  have rowCount : (highRows footer).length=nodes.length :=
    (high_rows_length footer).trans (List.length_map _)
  have rowLength : (descriptorBytes (highRows footer)).length=2*nodes.length := by rw [descriptor_bytes_length,rowCount]
  have count : s.getReg .x19=BitVec.ofNat 64 nodes.length := by
    have equal : (descriptorBytes (highRows footer)).length/2=nodes.length := by rw [rowLength]; omega
    simpa only [equal] using input.count
  have table : (footerTailSetupPrefix s 7).getReg .x21=BitVec.ofNat 64 metadata := by
    apply footer_tail_setup_table s metadata nodes.length _ count
    simpa only [rowLength] using input.data.metaPointer
  have cursor : (footerTailSetupPrefix s 7).getReg .x20=
      BitVec.ofNat 64 ((outputBase+oldPrefix.length)+(lowBytes footer).length) := by
    rw [footer_tail_setup_cursor]
    simpa only [List.length_append,Nat.add_assoc] using input.data.outputPointer
  have body : BytesAt (footerTailSetupPrefix s 7) (BitVec.ofNat 64 (outputBase+oldPrefix.length)) (lowBytes footer) := by
    have data := ((bytes_at_append s _ oldPrefix (lowBytes footer)).mp input.data.output).2
    rw [←BitVec.ofNat_add] at data
    intro index inside
    rw [footer_tail_setup_byte]
    exact data index inside
  have rows : BytesAt (footerTailSetupPrefix s 7) (BitVec.ofNat 64 metadata) (descriptorBytes (highRows footer)) := by
    intro index inside
    rw [footer_tail_setup_byte]
    exact input.data.metadata index inside
  have room : metadata+2*nodes.length≤MEMORY_BYTES := by
    simpa only [rowLength,List.length_nil,Nat.mul_zero,Nat.add_zero] using input.capacity
  have apart : TailApart ((footerTailSetupPrefix s 7).getReg .x21)
      ((footerTailSetupPrefix s 7).getReg .x20) (highRows footer) := by
    rw [table,cursor]
    apply tail_apart_of_ranges
    · simpa only [rowCount] using gap
    · simpa only [rowCount] using room
  have buffer := footer_tail_setup_buffer s
  have entryBuffer : TailBuffer (tailEntryState (footerTailSetupPrefix s 7)) [] := by
    constructor
    · simpa only [tail_entry_register] using buffer.value
    · simpa only [tail_entry_register] using buffer.count
    · simpa only [tail_entry_register] using buffer.eight
    · exact buffer.pending
  have entryRows : BytesAt (tailEntryState (footerTailSetupPrefix s 7))
      ((tailEntryState (footerTailSetupPrefix s 7)).getReg .x21) (descriptorBytes (highRows footer)) := by
    intro index inside
    rw [tail_entry_register,table]
    simp only [MachineState.getByte,tail_entry_memory]
    exact rows index inside
  have accessed := tail_rows_access (highRows footer) [] (tailEntryState (footerTailSetupPrefix s 7))
    metadata ((outputBase+oldPrefix.length)+(lowBytes footer).length) entryBuffer (footer_rows_small nodes footer)
    entryRows (by rw [tail_entry_register,table]) (by rw [tail_entry_register,cursor])
    (by rw [tail_entry_register,footer_tail_setup_count,count,rowCount])
    (by simpa only [rowCount] using gap) (by simpa only [rowCount] using room)
    (by rw [rowCount]; omega)
  rw [rowCount] at accessed
  exact ⟨buffer,cursor,table,(footer_tail_setup_count s).trans count,body,rows,apart,accessed.1,accessed.2,
    by unfold MEMORY_BYTES at room; omega⟩

theorem footer_tail_count (nodes : List Nat) (footer : Payload (InteriorCodec.footerSpec nodes))
    (s : MachineState) (output metadata : Nat) (ready : FooterTailReady nodes footer s output metadata) :
    tailNoFields s=decide (nodes.length=0) := by
  rw [tailNoFields,ready.count]
  change (nodes.length%2^64==0)=decide (nodes.length=0)
  rw [Nat.mod_eq_of_lt ready.countFit]
  cases nodes <;> rfl

theorem footer_tail_pack (nodes : List Nat) (footer : Payload (InteriorCodec.footerSpec nodes))
    (s : MachineState) (output metadata : Nat) (ready : FooterTailReady nodes footer s output metadata)
    (pc : s.pc=13000) (fit : (encode footer).length<2^64) (fuel : Nat) (coins : Bool) :
    execute openingControllerImage (tailTraverseCycles nodes.length s+fuel) s coins=
      (do let result ← execute openingControllerImage fuel (tailTraverseState nodes.length s) coins
          return result.charge (tailTraverseCycles nodes.length s) 0) ∧
    BytesAt (tailTraverseState nodes.length s) (BitVec.ofNat 64 output) (encode footer) ∧
    (tailTraverseState nodes.length s).pc=13068 ∧ tailTraverseCycles nodes.length s≤13*nodes.length+4 := by
  have aligned : ∀ field ∈ InteriorCodec.footerSpec nodes, field.1%8=0 := by
    intro field member
    obtain ⟨node,_,same⟩ := List.mem_map.mp member
    subst field
    change 232%8=0
    decide
  have count := footer_tail_count nodes footer s output metadata ready
  have length : (InteriorCodec.footerSpec nodes).length=nodes.length := List.length_map _
  have run := tail_traverse_execution openingControllerImage 13000 controller_footer_tail_at.2 nodes.length s pc count
    ready.ready (fun _ => ready.access) fuel coins
  have memory : BytesAt (tailTraverseState nodes.length s) (BitVec.ofNat 64 output) (encode footer) := by
    rw [←length]
    apply native_traverse_payload_bytes_at footer s _ aligned (footer_fields_small nodes) ready.buffer _ ready.body _ ready.apart fit
    · rw [←BitVec.ofNat_add]
      exact ready.cursor
    · rw [ready.source]
      exact ready.rows
  have nextPC : (tailEntryState s).pc=if nodes.length=0 then 13000+56 else 13000+4 := by
    rw [tail_entry_pc,pc,count]
    by_cases empty : nodes.length=0 <;> simp [empty]
  exact ⟨run,memory,tail_fields_finish_pc nodes.length (tailEntryState s) 13000 nextPC ready.ready,
    tail_traverse_bound nodes.length s⟩

end CommitGolfCandidate.Chained.Native
