import CommitGolfCandidate.ChainedCachedDispatch
import CommitGolfCandidate.ChainedCachedMarks
import CommitGolfCandidate.TwoPermutationPackedOpeningTranscript

/-! Execute the copied-record/footer prefix under any image retaining its actual instruction words. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype
open TwoPermutationPrototype.Sampling TwoPermutationPrototype.PackedOpening
open TwoPermutationPrototype.Opening (OpeningLayout proofBase trapdoorBase groupsBefore openingNodes
  capDigestAddress)
set_option maxRecDepth 8192
attribute [local irreducible] execute capPreparation setupPrefix readBuffer

structure CachedPrefixBoundary (s : Submission) (trapdoor : BitVec (8*s.sizes.trapdoor))
    (positions : Positions) (before : MachineState) : Prop where
  pc : before.pc=9836
  count : before.getReg .x16=BitVec.ofNat 64 positions.card
  pointer : before.getReg .x20=BitVec.ofNat 64 proofBase
  source : proofBytes before (proofLength positions)=proofFromTrapdoor (s := s) trapdoor positions
  marks : ∀ node, node<512 → before.getMem (BitVec.ofNat 64 (4096+8*node))=
    Opening.markWord (groupsBefore positions positions.card) node

private theorem byte_frame (before after : MachineState) (address : Nat) (fit : address<MEMORY_BYTES)
    (frame : ∀ query : Nat, trapdoorBase≤query → query<2^64 →
      after.getMem (BitVec.ofNat 64 query)=before.getMem (BitVec.ofNat 64 query))
    (above : trapdoorBase≤address) :
    after.getByte (BitVec.ofNat 64 address)=before.getByte (BitVec.ofNat 64 address) := by
  let aligned := alignToDword (BitVec.ofNat 64 address)
  have safe : MEMORY_BYTES+8≤2^64 := by decide
  have lower := aligned_dword_above trapdoorBase address (by decide) above (by omega)
  have stable := frame aligned.toNat lower aligned.isLt
  rw [BitVec.ofNat_toNat,BitVec.setWidth_eq] at stable
  change extractByte (after.getMem aligned) _ = _
  rw [stable]
  rfl

theorem cached_prefix_nonempty (target : Image)
    (codePrefix : target.code.take 1435=openingImage.code.take 1435)
    (s : Submission) (layout : OpeningLayout s) (dataAbove : 8192≤dataBase (s.image .opening))
    (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions) (nonempty : 0<positions.card) :
    ∃ before, (∀ coins, execute target (scheduledCycles positions)
      (s.initialState .opening (trapdoor,positions)) coins=
        pure ⟨.unfinished,before,scheduledCycles positions,0⟩) ∧
      CachedPrefixBoundary s trapdoor positions before := by
  let initial := s.initialState .opening (trapdoor,positions)
  let grouped := groupsBefore positions positions.card
  let nodes := capFrontierNodes grouped 1 8
  let dest := recordBase positions.card
  let begin := setupPrefix initial 13
  let lower := runRecords positions.card 0 positions.card begin
  let prepared := capPreparation lower
  have empty : positions.card≠0 := by omega
  have countReg : initial.getReg .x16=BitVec.ofNat 64 positions.card := rfl
  have ready := opening_first_boundary s layout trapdoor positions nonempty
  have marks := initial_record_marks_of_data_base s layout dataAbove trapdoor positions
  have assembled := execute_records_from_step execute_record s layout trapdoor positions begin 0 positions.card
    (by omega) ready marks (fun j _ first => (by omega : False).elim)
  have atCap : RecordBoundary s trapdoor positions lower positions.card := by
    simpa only [Nat.zero_add] using assembled.boundary
  have written : CompletedRecords s trapdoor positions lower positions.card := by
    simpa only [Nat.zero_add] using assembled.bytes
  have groups : Opening.RecordMarks positions lower positions.card := by
    simpa only [Nat.zero_add] using assembled.marks
  have leafMarks (node : Nat) (leaf : 255<node) (inside : node<512) :
      Opening.machineMarks lower node=Opening.markWord grouped node := by
    rw [groups node inside,Opening.mark_word_leaf grouped ⟨node,inside⟩ (show 256≤node by omega)]
  have ⟨rootPC,root⟩ := cap_preparation_context lower grouped dest
    atCap.marks atCap.capHeap atCap.capLeaves atCap.proofBegin atCap.dest leafMarks
  have frontier : openingNodes positions=nodes := by simp [openingNodes,empty,nodes,grouped]
  have allFit := (Nat.add_le_add_left (proof_fits_every_cardinality positions) _).trans packed_proof_memory
  have room : dest+30*nodes.length≤MEMORY_BYTES := by
    simpa only [proofLength,frontier,dest,recordBase,Nat.add_assoc] using allFit
  have aligned : dest%2=0 := by
    have base : proofBase%2=0 := by decide
    unfold dest recordBase recordBytes
    omega
  have above : proofBase≤dest := by unfold dest recordBase; omega
  obtain ⟨after,ranCap,afterPC,endPosition,footerBytes⟩ :=
    cap_subtree grouped prepared 1 8 dest Opening.cap_span_root root rootPC above aligned room
  have ranSetup : RunsOpeningBlock initial begin 13 :=
    fun fuel coins => execute_setup initial rfl fuel coins (countReg ▸ nonempty_count positions nonempty)
  have ranRecords : RunsOpeningBlock begin lower (590*positions.card-1) := by
    have charged : recordsCost positions.card 0 positions.card=590*positions.card-1 := by
      simp [recordsCost,nonempty]
    exact charged ▸ assembled.run
  have ranPrep : RunsOpeningBlock lower prepared 770 :=
    execute_cap_preparation lower (by simpa using atCap.pc) atCap.marks
  have prefixTrace := ((ranSetup.next ranRecords).next ranPrep).next ranCap
  have lowerFrame (address : Nat) (fromProof : proofBase≤address) (beforeCap : address<dest) :
      after.getByte (BitVec.ofNat 64 address)=lower.getByte (BitVec.ofNat 64 address) := by
    have safe : MEMORY_BYTES<2^64 := by decide
    have heapBefore : trapdoorBase≤proofBase := by decide
    have prepStable := byte_frame lower prepared address (by omega)
      (fun query low fit => cap_preparation_frame lower query low fit atCap.marks)
      (heapBefore.trans fromProof)
    exact (footerBytes.frame address (by omega)
      (Or.inl beforeCap)).trans prepStable
  have completed : CompletedRecords s trapdoor positions after positions.card := by
    intro ordinal present earlier
    obtain ⟨nonce,siblings⟩ := written ordinal present earlier
    constructor
    · intro byte inside
      have bound : recordBase ordinal+byte<dest := by unfold dest recordBase recordBytes; omega
      exact (lowerFrame _ (by unfold recordBase; omega) bound).trans (nonce byte inside)
    · intro level levelBound byte inside
      have bound : siblingDestination ordinal level+byte<dest := by
        have reached := destination_mono ordinal (show level+1≤16 by omega)
        rw [record_end] at reached
        have step : siblingDestination ordinal (level+1)=siblingDestination ordinal level+siblingWidth level := by
          simp only [siblingDestination,sibling_offset_next,Nat.add_assoc]
        unfold dest recordBase recordBytes at *
        omega
      exact (lowerFrame _ (by unfold siblingDestination recordBase; omega) bound).trans
        (siblings level levelBound byte inside)
  have footer : ∀ i (inside : i<(openingNodes positions).length),
      readBuffer after (recordBase positions.card+30*i) 30=
        (trapdoor.extractLsb' (256*(openingNodes positions)[i]) 256).extractLsb' 0 240 := by
    intro i inside
    have insideNodes : i<nodes.length := frontier ▸ inside
    let node := nodes[i]'insideNodes
    have nodeEq : (openingNodes positions)[i]=node := by
      have found := congrArg (fun l : List Nat => l[i]?) frontier
      rw [List.getElem?_eq_getElem inside,List.getElem?_eq_getElem insideNodes] at found
      exact Option.some.inj found
    rw [nodeEq]
    have small : node<512 := Opening.cap_frontier_nodes_small grouped 1 8 Opening.cap_span_root
      node (List.getElem_mem insideNodes)
    have stable : readBuffer prepared (capDigestAddress node) 32=readBuffer initial (capDigestAddress node) 32 := by
      have ⟨aligned,beforeProof⟩ := Opening.cap_digest_bounds node small
      apply Opening.copied_buffer _ _ _ _ 4 aligned aligned (by decide)
      intro j low
      have aboveHeap : trapdoorBase≤capDigestAddress node+8*j := by unfold capDigestAddress; omega
      have belowProof : capDigestAddress node+8*j<proofBase := by omega
      have fit : proofBase<2^64 := by decide
      exact (cap_preparation_frame lower _ aboveHeap (by omega) atCap.marks).trans
        (atCap.input _ aboveHeap belowProof)
    have digest : readBuffer initial (capDigestAddress node) 32=trapdoor.extractLsb' (256*node) 256 :=
      Opening.input_digest s layout trapdoor positions node (small.trans_le (by decide : 512≤2*LENGTH))
    have copied := footerBytes.digest i insideNodes
    rw [stable,digest] at copied
    exact copied
  have source := unpacked_opening_proof_layout s layout trapdoor positions after completed footer
  have zeroLower : lower.getMem (BitVec.ofNat 64 4096)=0 := by
    have word := groups 0 (by decide)
    simpa [Opening.machineMarks,Opening.markBase,cached_group_zero_absent] using word
  have zeroAfter : after.getMem (BitVec.ofNat 64 4096)=0 := by
    have proofFloor : 8192≤proofBase := by decide
    have safe : MEMORY_BYTES<2^64 := by decide
    have word : after.getMem (BitVec.ofNat 64 4096)=prepared.getMem (BitVec.ofNat 64 4096) := by
      apply aligned_word_of_byte_frame prepared after 4096 (by decide)
      intro index inside
      exact footerBytes.frame (4096+index) (by omega) (Or.inl (by omega))
    exact word.trans ((cached_preparation_zero lower).trans zeroLower)
  have dispatch := cached_root_execution after afterPC endPosition.nodeWord
  have frame := cached_root_frame after afterPC endPosition.nodeWord
  have ran := prefixTrace.next dispatch
  have charge : scheduledCycles positions=13+(590*positions.card-1)+770+capSubtreeCycles grouped 1 8+8 := by
    rw [scheduledCycles,if_neg empty]
    dsimp only [grouped]
    omega
  have reached (coins : Bool) :
      (⟨.unfinished,cachedRootPrefix after 8,scheduledCycles positions,0⟩ : Execution) ∈
        support (execute openingImage (scheduledCycles positions) initial coins) := by
    rw [charge,show 13+(590*positions.card-1)+770+capSubtreeCycles grouped 1 8+8=
      (13+(590*positions.card-1)+770+capSubtreeCycles grouped 1 8+8)+0 by omega,ran]
    simp [execute,Execution.charge]
  refine ⟨cachedRootPrefix after 8,?_,frame.1,?_,?_,?_,?_⟩
  · intro coins
    exact cached_prefix_replay target codePrefix _ initial coins _ (reached coins) rfl (by rw [frame.1]; decide)
  · exact (opening_keeps_count _ initial false _ (reached false)).trans countReg
  · exact frame.2.2.2.trans endPosition.context.proofStart
  · exact (proof_bytes_congr frame.2.1 _).trans source
  · intro node small
    by_cases zero : node=0
    · subst node
      exact (congrFun frame.2.1 _).trans (zeroAfter.trans (cached_mark_zero positions positions.card).symm)
    · exact (congrFun frame.2.1 _).trans (endPosition.context.markValue node (by omega) small)

theorem cached_prefix_empty (target : Image)
    (codePrefix : target.code.take 1435=openingImage.code.take 1435)
    (s : Submission) (layout : OpeningLayout s) (dataAbove : 8192≤dataBase (s.image .opening))
    (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions) (empty : positions.card=0) :
    ∃ before, (∀ coins, execute target (scheduledCycles positions)
      (s.initialState .opening (trapdoor,positions)) coins=
        pure ⟨.unfinished,before,scheduledCycles positions,0⟩) ∧
      CachedPrefixBoundary s trapdoor positions before := by
  let initial := s.initialState .opening (trapdoor,positions)
  have count : initial.getReg .x16=0#64 := by change BitVec.ofNat 64 positions.card=0; rw [empty]; rfl
  have ran := cached_empty_execution initial rfl count
  have frame := cached_empty_frame initial rfl count
  have charge : scheduledCycles positions=7 := by simp [scheduledCycles,empty]
  have reached (coins : Bool) : (⟨.unfinished,cachedEmptyPrefix initial 7,7,0⟩ : Execution) ∈
      support (execute openingImage 7 initial coins) := by
    rw [show 7=7+0 from rfl,ran]
    simp [execute,Execution.charge]
  refine ⟨cachedEmptyPrefix initial 7,?_,frame.1,?_,?_,?_,?_⟩
  · intro coins
    rw [charge]
    exact cached_prefix_replay target codePrefix _ initial coins _ (reached coins) rfl (by rw [frame.1]; decide)
  · simpa only [empty] using frame.2.2.1
  · exact frame.2.2.2.trans (congrArg (BitVec.ofNat 64) layout.proof)
  · have noPositions : positions=∅ := Finset.card_eq_zero.mp empty
    rw [noPositions]
    simp [proofLength,openingNodes,PackedOpening.proofBytes,proofFromTrapdoor]
  · intro node small
    have zero := initial_mark_word_of_data_base s layout dataAbove trapdoor positions node small
    have memory : (cachedEmptyPrefix initial 7).getMem (BitVec.ofNat 64 (4096+8*node))=0 :=
      (congrFun frame.2.1 _).trans zero
    simpa [groupsBefore,empty,Opening.markWord,capIsMarked] using memory

theorem cached_prefix (target : Image)
    (codePrefix : target.code.take 1435=openingImage.code.take 1435)
    (s : Submission) (layout : OpeningLayout s) (dataAbove : 8192≤dataBase (s.image .opening))
    (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions) :
    ∃ before, (∀ coins, execute target (scheduledCycles positions)
      (s.initialState .opening (trapdoor,positions)) coins=
        pure ⟨.unfinished,before,scheduledCycles positions,0⟩) ∧
      CachedPrefixBoundary s trapdoor positions before := by
  by_cases empty : positions.card=0
  · exact cached_prefix_empty target codePrefix s layout dataAbove trapdoor positions empty
  · exact cached_prefix_nonempty target codePrefix s layout dataAbove trapdoor positions (by omega)

end CommitGolfCandidate.Chained.Native
