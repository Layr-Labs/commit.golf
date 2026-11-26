import CommitGolfCandidate.ChainedControllerRelocated
import CommitGolfCandidate.ChainedDeliveredSource

/-! Complete relocated opening execution from the exact delivered cached commitment. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp SplitCodec
open TwoPermutationPrototype.Sampling TwoPermutationPrototype.Opening
open CommitGolfCandidate.Permutation.NonceChain (Key)
set_option maxRecDepth 8192
attribute [local irreducible] execute

def cachedEncodedPacket (heap : Nat → BitVec 238) (salts : Index → BitVec 128) (positions : Positions) : Proof :=
  encodedRecords (cachedRecords heap salts positions)++encode (cachedFooter (openingNodes positions) heap)

theorem cached_footer_nodes (positions : Positions) : openingNodes positions=InteriorCodec.footerNodes positions := by
  simp only [openingNodes,InteriorCodec.footerNodes,groupsBefore]
  have ordered : (positions.sort (· ≤ ·)).length=positions.card := by simp
  rw [←ordered,List.take_length]

theorem cached_encoded_length (heap : Nat → BitVec 238) (salts : Index → BitVec 128) (positions : Positions) :
    (cachedEncodedPacket heap salts positions).length=InteriorCodec.proofLength positions := by
  rw [cachedEncodedPacket,List.length_append,encodedRecords,InteriorCodec.records_length,cached_records_count,
    InteriorCodec.encode_footer_length,cached_footer_nodes]
  rfl

theorem cached_encoded_empty (heap : Nat → BitVec 238) (salts : Index → BitVec 128) (positions : Positions)
    (empty : positions.card=0) : cachedEncodedPacket heap salts positions=[] := by
  apply List.length_eq_zero_iff.mp
  rw [cached_encoded_length,InteriorCodec.proof_length_empty positions empty]

private theorem cached_relocated_entry (before : MachineState) (pc : before.pc=9836) :
    relocatedState 5740 (before.setPC 4096)=before := by
  change before.setPC 9836=before
  rw [←pc]
  cases before
  rfl

theorem cached_boundary_postpass (oracle : Oracle) (message : Message) (key : Key)
    (positions : Positions) (before : MachineState)
    (boundary : CachedPrefixBoundary Artifact.submission
      (Artifact.submission.readCommit (deliveredSeedOutput oracle message key)).2 positions before) :
    let heap := referenceHeap oracle (pinnedLeafNodes oracle (deliveredReady oracle message key))
    let packet := cachedEncodedPacket heap (deliveredSalts oracle key) positions
    ∃ after cycles, (∀ fuel coins, execute cachedControllerImage (cycles+fuel) before coins=
        pure ⟨.success,after,cycles,0⟩) ∧
      BytesAt after (BitVec.ofNat 64 proofBase) packet ∧
      (after.getReg .x11).toNat=packet.length ∧
      cycles≤2273*positions.card+66460+13*(openingNodes positions).length := by
  have entry := cached_relocated_entry before boundary.pc
  by_cases empty : positions.card=0
  · obtain ⟨after,ran,length,bytes⟩ := opening_entry_empty (before.setPC 4096) rfl
      (by simpa only [MachineState.getReg_setPC,empty] using boundary.count)
    refine ⟨relocatedState 5740 after,10,?_,?_,?_,by omega⟩
    · intro fuel coins
      simpa only [entry] using controller_execution_relocated (10+fuel) (before.setPC 4096) coins after 10 (ran fuel coins)
    · rw [cached_encoded_empty _ _ positions empty]
      intro index inside
      simp only [List.length_nil] at inside
      omega
    · rw [relocated_reg,length,cached_encoded_empty _ _ positions empty]
      rfl
  · obtain ⟨after,cycles,ran,bytes,cursor,length,bound⟩ :=
      delivered_cached_nonempty_postpass oracle message key positions before empty boundary
    refine ⟨relocatedState 5740 after,cycles,?_,?_,?_,bound⟩
    · intro fuel coins
      simpa only [entry] using controller_execution_relocated (cycles+fuel) (before.setPC 4096) coins after cycles (ran fuel coins)
    · simpa only [BytesAt,relocated_byte,cachedEncodedPacket] using bytes
    · simpa only [relocated_reg,cachedEncodedPacket,List.length_append] using length

theorem delivered_cached_opening (oracle : Oracle) (message : Message) (key : Key) (positions : Positions) :
    let trapdoor := (Artifact.submission.readCommit (deliveredSeedOutput oracle message key)).2
    let heap := referenceHeap oracle (pinnedLeafNodes oracle (deliveredReady oracle message key))
    let packet := cachedEncodedPacket heap (deliveredSalts oracle key) positions
    ∃ after cycles, (∀ fuel coins, execute cachedControllerImage
        (TwoPermutationPrototype.PackedOpening.scheduledCycles positions+cycles+fuel)
        (Artifact.submission.initialState .opening (trapdoor,positions)) coins=
        pure ⟨.success,after,TwoPermutationPrototype.PackedOpening.scheduledCycles positions+cycles,0⟩) ∧
      BytesAt after (BitVec.ofNat 64 proofBase) packet ∧
      (after.getReg .x11).toNat=packet.length ∧
      cycles≤2273*positions.card+66460+13*(openingNodes positions).length := by
  have layout : OpeningLayout Artifact.submission := ⟨rfl,rfl,rfl,rfl⟩
  have above : 8192≤dataBase (Artifact.submission.image .opening) := by decide +kernel
  obtain ⟨before,ranPrefix,boundary,_⟩ :=
    delivered_cached_boundary cachedControllerImage cached_controller_prefix layout above oracle message key positions
  obtain ⟨after,cycles,ran,bytes,length,bound⟩ := cached_boundary_postpass oracle message key positions before boundary
  refine ⟨after,cycles,?_,bytes,length,bound⟩
  intro fuel coins
  rw [Nat.add_assoc,execute_add,ranPrefix coins]
  simp only [pure_bind,resume,ite_true]
  rw [ran fuel coins]
  rfl

private theorem range_postpass_arithmetic (a b c : Nat) (h : a≤2273*b+66455+13*c) :
    5+a≤2273*b+66460+13*c := by omega

theorem cached_boundary_range_postpass
    (trapdoor : BitVec (8*Artifact.submission.sizes.trapdoor)) (positions : Positions) (before : MachineState)
    (boundary : CachedPrefixBoundary Artifact.submission trapdoor positions before) :
    ∃ after cycles, (∀ fuel coins, execute cachedControllerImage (cycles+fuel) before coins=
      pure ⟨.success,after,cycles,0⟩) ∧
      cycles≤2273*positions.card+66460+13*(openingNodes positions).length := by
  have entry := cached_relocated_entry before boundary.pc
  by_cases empty : positions.card=0
  · obtain ⟨after,ran,_,_⟩ := opening_entry_empty (before.setPC 4096) rfl
      (by simpa only [MachineState.getReg_setPC,empty] using boundary.count)
    refine ⟨relocatedState 5740 after,10,?_,by omega⟩
    intro fuel coins
    simpa only [entry] using controller_execution_relocated (10+fuel) (before.setPC 4096) coins after 10 (ran fuel coins)
  · let records := cachedRecords (fun _ => 0) (fun _ => 0) positions
    let groups := groupsBefore positions positions.card
    let initial := before.setPC 4096
    let begin := openingEntryPrefix initial 5
    have cardinal : positions.card≤16777216 := by
      have bound : positions.card≤LENGTH := by simpa [Index] using Finset.card_le_univ positions
      exact bound
    have recordCount : records.length=positions.card := cached_records_count _ _ positions
    have nonempty : records≠[] := by intro noRecords; rw [noRecords] at recordCount; simp only [List.length_nil] at recordCount; omega
    have occupied : initial.getReg .x16≠0#64 := by
      intro zero
      have value := congrArg BitVec.toNat zero
      rw [show initial.getReg .x16=BitVec.ofNat 64 positions.card from boundary.count,
        BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : positions.card<2^64)] at value
      change positions.card=0 at value
      exact empty value
    have data := opening_entry_data initial
    have beginPC : begin.pc=4120 := opening_entry_pc initial rfl occupied
    have sourcePointer : begin.getReg .x5=BitVec.ofNat 64 proofBase := data.1.trans boundary.pointer
    have outputPointer : begin.getReg .x6=BitVec.ofNat 64 proofBase := data.2.1.trans boundary.pointer
    have scratch : begin.getReg .x17+0x200000000=BitVec.ofNat 64 (proofBase+2^33) := by
      rw [data.2.2.1,show initial.getReg .x20=BitVec.ofNat 64 proofBase from boundary.pointer]
      change BitVec.ofNat 64 proofBase+BitVec.ofNat 64 (2^33)=_
      rw [←BitVec.ofNat_add]
    have count : begin.getReg .x29=BitVec.ofNat 64 records.length := by
      rw [data.2.2.2,show initial.getReg .x16=BitVec.ofNat 64 positions.card from boundary.count,recordCount]
    have frontier : openingNodes positions=capFrontierNodes groups 1 8 := by
      simp only [openingNodes,empty,↓reduceIte,groups]
    have nodeBound : (capFrontierNodes groups 1 8).length≤128 := by
      rw [←frontier]; exact opening_nodes_bound positions
    have separate : proofBase+498*records.length+30*(capFrontierNodes groups 1 8).length≤proofBase+2^33 := by
      rw [recordCount]
      omega
    have metaRoom : proofBase+2^33+34≤MEMORY_BYTES := by decide
    have footerRoom : proofBase+2^33+2*(capFrontierNodes groups 1 8).length≤MEMORY_BYTES := by
      have reserve : proofBase+2^33+256≤MEMORY_BYTES := by decide
      omega
    have marks (node : Nat) (bound : node<512) :
        begin.getMem (BitVec.ofNat 64 (4096+8*node))=markWord groups node := by
      rw [opening_entry_memory]
      exact boundary.marks node bound
    obtain ⟨after,cycles,ran,bound⟩ := native_packet_range_execution groups records begin proofBase proofBase
      (proofBase+2^33) beginPC sourcePointer outputPointer scratch count nonempty (Nat.le_refl _) separate
      metaRoom footerRoom marks (by decide) (by decide)
    refine ⟨relocatedState 5740 after,5+cycles,?_,?_⟩
    · intro fuel coins
      have run : execute openingControllerImage (5+cycles+fuel) initial coins=pure ⟨.success,after,5+cycles,0⟩ := by
        rw [Nat.add_assoc,opening_entry_execution initial rfl,ran fuel coins]
        simp only [pure_bind,Execution.charge]
      simpa only [initial,entry] using controller_execution_relocated (5+cycles+fuel) initial coins after (5+cycles) run
    · rw [recordCount,←frontier] at bound
      exact range_postpass_arithmetic cycles positions.card (openingNodes positions).length bound

end CommitGolfCandidate.Chained.Native
