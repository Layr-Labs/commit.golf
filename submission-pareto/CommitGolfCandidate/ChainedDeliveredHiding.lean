import CommitGolfCandidate.ChainedCheckerAcceptedRefinement
import CommitGolfCandidate.ChainedOpeningDelivered
import CommitGolfCandidate.NonceChainSecurity

/-! The delivered transcript depends on opened salts and the pinned digest tape. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype TwoPermutationPrototype.RV64 TwoPermutationPrototype.RV64.PackedLeaves
open TwoPermutationPrototype.Sampling TwoPermutationPrototype.Opening
open CommitGolfCandidate.Permutation.NonceChain (Key)
local instance deliveredHidingDiscrete {α : Type} : MeasurableSpace α := ⊤

theorem compression_query_evaluation (oracle : Oracle) (input : BitVec 512) :
    checkEvaluation oracle (liftM (World.query (.inr (.inl input))) : OracleComp World Output)=(oracle.compression input,1) := by
  exact check_evaluation_public oracle (.inl input)

theorem continuation_compression_congr (left right : Oracle) (same : left.compression=right.compression)
    (h : Height) (count : Nat) : ∀ stage value,
    checkEvaluation left (continuationTrace h stage count value)=checkEvaluation right (continuationTrace h stage count value) := by
  induction count with
  | zero => intro stage value; simp only [continuationTrace,check_evaluation_pure]
  | succ count ih =>
    intro stage value
    simp only [continuationTrace,check_evaluation_bind,compression_query_evaluation,same]
    exact congrArg (fun observed : Output × Nat => (observed.1,1+observed.2))
      (ih (stage+1) (right.compression (encodeNext h (stage+1) value)))

theorem parent_value_compression_congr (left right : Oracle) (same : left.compression=right.compression)
    (h : Height) (a b : BitVec 238) : parentValue left h a b=parentValue right h a b := by
  simp only [parentValue,parentDigestTrace,check_evaluation_bind,compression_query_evaluation,
    same,check_evaluation_pure]
  exact congrArg (fun observed : Output × Nat => finalValue h observed.1)
    (continuation_compression_congr left right same h (calls h-1) 0
      (right.compression (canonicalEncoding.first h (b ++ a))))

theorem reference_node_congr (left right : Oracle) (same : left.compression=right.compression)
    (a b : Nat → BitVec 238) (height : Nat) : ∀ node,
    (∀ offset, offset<2^height → a (node*2^height+offset)=b (node*2^height+offset)) →
    referenceNode left a height node=referenceNode right b height node := by
  induction height with
  | zero =>
    intro node agree
    simpa only [referenceNode,Nat.pow_zero,Nat.mul_one,Nat.add_zero] using agree 0 (by decide)
  | succ height ih =>
    intro node agree
    rw [referenceNode,referenceNode]
    apply congrArg (fun value : Output => BitVec.ofNat 238 value.toNat)
    rw [parent_value_compression_congr left right same]
    congr 1
    · apply ih
      intro offset small
      have paired := agree offset (by rw [Nat.pow_succ];omega)
      convert paired using 1 <;> congr 1 <;> rw [Nat.pow_succ] <;> ring
    · apply ih
      intro offset small
      have paired := agree (2^height+offset) (by rw [Nat.pow_succ];omega)
      convert paired using 1 <;> congr 1 <;> rw [Nat.pow_succ] <;> ring

theorem reference_heap_congr (left right : Oracle) (same : left.compression=right.compression)
    (a b : Nat → BitVec 238) (agree : ∀ node, LENGTH≤node → node<2*LENGTH → a node=b node)
    (node : Nat) (positive : 0<node) (small : node<2*LENGTH) :
    referenceHeap left a node=referenceHeap right b node := by
  have lower : 2^(Nat.log2 node)≤node := (Nat.le_log2 (by omega : node≠0)).mp (Nat.le_refl _)
  have upper : node<2^(Nat.log2 node+1) := by
    by_contra absent
    have impossible : Nat.log2 node+1≤Nat.log2 node := (Nat.le_log2 (by omega : node≠0)).mpr (by omega)
    omega
  have logSmall : Nat.log2 node≤24 := by
    by_contra absent
    have power : 2^25≤2^(Nat.log2 node) := Nat.pow_le_pow_right (by decide) (by omega)
    have numeric : node<33554432 := small
    norm_num at power
    omega
  have product : 2^(Nat.log2 node)*2^(24-Nat.log2 node)=LENGTH := by
    rw [←Nat.pow_add,Nat.add_sub_of_le logSmall]
    rfl
  have twice : 2^(Nat.log2 node+1)*2^(24-Nat.log2 node)=2*LENGTH := by
    rw [Nat.pow_succ]
    calc
      2^Nat.log2 node*2*2^(24-Nat.log2 node)=2*(2^Nat.log2 node*2^(24-Nat.log2 node)) := by ring
      _=2*LENGTH := by rw [product]
  apply reference_node_congr left right same a b _ node
  intro offset inside
  apply agree
  · have bound := Nat.mul_le_mul_right (2^(24-Nat.log2 node)) lower
    rw [product] at bound
    omega
  · have bound := Nat.mul_le_mul_right (2^(24-Nat.log2 node)) (show node+1≤2^(Nat.log2 node+1) by omega)
    rw [twice,Nat.add_mul,Nat.one_mul] at bound
    omega

theorem delivered_leaf_digest (oracle : Oracle) (message : Message) (key : Key) (index : Index) :
    pinnedLeafNodes oracle (deliveredReady oracle message key) (LENGTH+index.val)=
      (pinnedFullLeafDigests (BiPermutation.equiv Block oracle.permutation) message (maskedNonces oracle.permutation key) index).setWidth 238 := by
  have content := Chain.final_content oracle Artifact.submission rfl rfl message key (artifact_commit_entry message)
  have words : Chain.BodyContent (deliveredReady oracle message key) message (maskedNonces oracle.permutation key) := content.2
  rw [pinnedLeafNodes,Nat.add_sub_cancel_left,pinnedFinalReply,words.messages index,words.nonces index]
  simp only [pinnedFullLeafDigests,pinnedLeafDigest,pinnedFirstRow,pinnedSecondRow,pinned_typed_words]
  rfl

open SplitCodec

theorem cached_payload_congr (spec : Spec) (a b : Nat → BitVec 256)
    (agree : ∀ ordinal, ordinal<spec.length → a ordinal=b ordinal) :
    cachedPayload spec a=cachedPayload spec b := by
  induction spec generalizing a b with
  | nil => rfl
  | cons field spec ih =>
    rcases field with ⟨low,high⟩
    simp only [cachedPayload]
    congr 1
    · exact congrArg (fun value : BitVec 256 => value.setWidth (low+high)) (agree 0 (by simp))
    · apply ih
      intro ordinal inside
      exact agree (ordinal+1) (by simpa using inside)

theorem cached_record_heap_congr (a b : Nat → BitVec 238)
    (agree : ∀ node, 0<node → node<2*LENGTH → a node=b node) (salt : BitVec 128) (index : Index) :
    cachedRecord a salt index=cachedRecord b salt index := by
  apply cached_payload_congr
  intro ordinal inside
  have count : ordinal<17 := inside
  cases ordinal with
  | zero => rfl
  | succ level =>
    change (a (lowerNode index level ^^^ 1)).setWidth 256=(b (lowerNode index level ^^^ 1)).setWidth 256
    exact congrArg (fun value : BitVec 238 => value.setWidth 256)
      (agree _ (cached_sibling_positive index level (by omega)) (lower_swap_bound index level))

theorem cached_footer_heap_congr (a b : Nat → BitVec 238) (nodes : List Nat)
    (agree : ∀ node ∈ nodes, a node=b node) : cachedFooter nodes a=cachedFooter nodes b := by
  apply cached_payload_congr
  intro ordinal inside
  have live : ordinal<nodes.length := by simpa only [InteriorCodec.footerSpec,List.length_map] using inside
  change (a (nodes.getD ordinal 0)).setWidth 256=(b (nodes.getD ordinal 0)).setWidth 256
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem live]
  exact congrArg (fun value : BitVec 238 => value.setWidth 256) (agree _ (List.getElem_mem live))

theorem cached_packet_congr (a b : Nat → BitVec 238) (leftSalts rightSalts : Index → BitVec 128)
    (positions : Positions) (heaps : ∀ node, 0<node → node<2*LENGTH → a node=b node)
    (salts : ∀ index ∈ positions, leftSalts index=rightSalts index) :
    cachedEncodedPacket a leftSalts positions=cachedEncodedPacket b rightSalts positions := by
  rw [cachedEncodedPacket,cachedEncodedPacket]
  congr 1
  · apply congrArg encodedRecords
    unfold cachedRecords
    apply List.map_congr_left
    intro index member
    rw [salts index (by simpa only [Finset.mem_sort] using member)]
    exact cached_record_heap_congr a b heaps _ index
  · apply congrArg encode
    apply cached_footer_heap_congr
    intro node member
    have domain := cached_opening_node_domain positions node member
    exact heaps node domain.1 (by have := domain.2; change node<2*16777216; omega)

def compressionOracle (compress : Compression) : Oracle := ⟨compress,Equiv.refl _⟩

def digestTapeNodes (leaves : DigestTape) (node : Nat) : BitVec 238 :=
  (leaves ⟨(node-LENGTH)%LENGTH,Nat.mod_lt _ (by decide)⟩).setWidth 238

noncomputable def builderHeap (compress : Compression) (leaves : DigestTape) : Nat → BitVec 238 :=
  referenceHeap (compressionOracle compress) (digestTapeNodes leaves)

noncomputable def deliveredBuilder : TranscriptBuilder := fun compress positions opened leaves =>
  let heap := builderHeap compress leaves
  ((heap 1).setWidth 256,cachedEncodedPacket heap (publicOpenedSalts opened) positions)

theorem delivered_heap_builder (oracle : Oracle) (message : Message) (key : Key)
    (node : Nat) (positive : 0<node) (small : node<2*LENGTH) :
    referenceHeap oracle (pinnedLeafNodes oracle (deliveredReady oracle message key)) node=
      builderHeap oracle.compression
        (pinnedFullLeafDigests (BiPermutation.equiv Block oracle.permutation) message (maskedNonces oracle.permutation key)) node := by
  apply reference_heap_congr oracle (compressionOracle oracle.compression) rfl _ _ _ node positive small
  intro leaf lower upper
  have inside : leaf-LENGTH<LENGTH := by omega
  let index : Index := ⟨leaf-LENGTH,inside⟩
  have numeric : leaf=LENGTH+index.val := by dsimp only [index];omega
  rw [numeric,delivered_leaf_digest]
  simp only [digestTapeNodes,Nat.add_sub_cancel_left,Nat.mod_eq_of_lt index.isLt]

theorem delivered_packet_builder (oracle : Oracle) (message : Message) (key : Key) (positions : Positions) :
    cachedEncodedPacket (referenceHeap oracle (pinnedLeafNodes oracle (deliveredReady oracle message key)))
      (deliveredSalts oracle key) positions=
    cachedEncodedPacket (builderHeap oracle.compression
      (pinnedFullLeafDigests (BiPermutation.equiv Block oracle.permutation) message (maskedNonces oracle.permutation key)))
      (publicOpenedSalts (fun index : {i // i∈positions} => maskedNonces oracle.permutation key index.val)) positions := by
  apply cached_packet_congr
  · exact delivered_heap_builder oracle message key
  · intro index present
    simp only [publicOpenedSalts,present,↓reduceDIte]
    rfl

theorem delivered_commit_fixed (oracle : Oracle) (message : Message) :
    fixedOracleRun oracle (Artifact.submission.scheme.commit message)=
      (do let key ← $ᵗ Key
          pure (Artifact.submission.readCommit (deliveredSeedOutput oracle message key))) := by
  have seeded : fixedOracleRun oracle (Artifact.submission.run .commit message)=
      (do let key ← $ᵗ Key; pure (deliveredSeedOutput oracle message key)) := by
    unfold fixedOracleRun
    rw [delivered_counted_run]
    simp only [map_bind,map_pure]
  change fixedOracleRun oracle (Artifact.submission.readCommit <$> Artifact.submission.run .commit message)=_
  rw [map_eq_bind_pure_comp,fixed_oracle_run_bind,seeded]
  simp only [bind_assoc,pure_bind,Function.comp_apply,fixed_oracle_run_pure]
  rfl

theorem delivered_opening_reference (oracle : Oracle) (message : Message) (key : Key) (positions : Positions) :
    Artifact.submission.scheme.opening (Artifact.submission.readCommit (deliveredSeedOutput oracle message key)).2 positions=
      pure (cachedEncodedPacket (referenceHeap oracle (pinnedLeafNodes oracle (deliveredReady oracle message key)))
        (deliveredSalts oracle key) positions) := by
  obtain ⟨after,cycles,ran,read,bound⟩ := artifact_opening_run oracle message key positions
  change Artifact.submission.readProof <$> Artifact.submission.run .opening _=_
  rw [ran,map_pure,read]

theorem delivered_transcript_fixed (oracle : Oracle) (message : Message) (positions : Positions) :
    fixedOracleRun oracle (executableTranscript Artifact.submission.scheme message positions)=
      (do let key ← $ᵗ Key
          pure ((Artifact.submission.readCommit (deliveredSeedOutput oracle message key)).1,
            cachedEncodedPacket (referenceHeap oracle (pinnedLeafNodes oracle (deliveredReady oracle message key)))
              (deliveredSalts oracle key) positions)) := by
  unfold executableTranscript
  change fixedOracleRun oracle
    (do let value ← Artifact.submission.readCommit <$> Artifact.submission.run .commit message
        let opening ← Artifact.submission.readProof <$> Artifact.submission.run .opening (value.2,positions)
        pure (value.1,opening))=_
  have commit : fixedOracleRun oracle (Artifact.submission.readCommit <$> Artifact.submission.run .commit message)=
      (do let key ← $ᵗ Key; pure (Artifact.submission.readCommit (deliveredSeedOutput oracle message key))) :=
    delivered_commit_fixed oracle message
  rw [fixed_oracle_run_bind,commit]
  simp only [bind_assoc,pure_bind,Function.comp_apply]
  apply bind_congr
  intro key
  obtain ⟨after,cycles,ran,read,bound⟩ := artifact_opening_run oracle message key positions
  rw [ran,map_pure,pure_bind,fixed_oracle_run_pure,read]

theorem delivered_chain_transcript : ChainTranscriptRefines Artifact.submission.scheme deliveredBuilder := by
  intro oracle message positions
  rw [delivered_transcript_fixed]
  apply EvalDistEq.bind_right
  intro key
  have root := (delivered_physical_results oracle message key).1
  have heap := delivered_heap_builder oracle message key 1 (by decide) (by decide)
  have packet := delivered_packet_builder oracle message key positions
  rw [root,heap,packet]
  exact EvalDistEq.refl _

theorem delivered_scheme_hiding : Artifact.submission.scheme.Hiding
    (fun _ budget => min 1 (((budget : ℝ)+1)/2^120)) :=
  scheme_hiding_of_chain Artifact.submission.scheme deliveredBuilder delivered_chain_transcript

theorem checker_empty_input_run (input : CheckInput) (empty : input.positions.card=0)
    (zero : input.proof.length=0) :
    Artifact.submission.run .check input=
      pure ⟨.success,checkerEmptyState 20 (Artifact.submission.initialState .check input),21,0⟩ := by
  have registers := checker_input_registers input
  have valid : input.proof.length≤Artifact.submission.sizes.proof := by rw [zero]; exact Nat.zero_le _
  have room : 21≤Artifact.submission.steps .check := by decide +kernel
  have run : Artifact.submission.run .check input=execute (Artifact.submission.image .check)
      (Artifact.submission.steps .check) (Artifact.submission.initialState .check input) false := by
    simp [Submission.run,valid]
  rw [run,show Artifact.submission.steps .check=21+(Artifact.submission.steps .check-21) by omega]
  apply artifact_checking_empty _ registers.1
  · rw [registers.2.2.2.2.2.1,empty]
  · rw [registers.2.2.2.2.2.2,zero]

theorem checker_empty_input_accepts (input : CheckInput) (empty : input.positions.card=0)
    (zero : input.proof.length=0) :
    Artifact.submission.scheme.check input.commitment input.positions input.values input.proof=Pure.pure (true : Bool) := by
  change (fun result : Execution => result.exit==.success) <$>
    simulateQ checkHandler (Artifact.submission.run .check input)=_
  rw [checker_empty_input_run input empty zero]
  rfl

theorem checker_decode_encoded_records (records : List InteriorCodec.Record) (suffix : Proof) :
    checkerDecodeRecords records.length (encodedRecords records++suffix)=records := by
  induction records with
  | nil => rfl
  | cons record records ih =>
    change checkerDecodeRecords (records.length+1) ((SplitCodec.encode record++encodedRecords records)++suffix)=_
    rw [List.append_assoc,checkerDecodeRecords,←InteriorCodec.encode_record_length record,List.take_left,
      List.drop_left,SplitCodec.decode_encode,ih]

theorem checker_cached_input_raw_records (input : CheckInput) (heap : Nat → BitVec 238)
    (salts : Index → BitVec 128) (proof : input.proof=cachedEncodedPacket heap salts input.positions) :
    checkerInputRawRecords input=rawRecordStream (cachedRecords heap salts input.positions) := by
  rw [checkerInputRawRecords,proof,cachedEncodedPacket,←cached_records_count heap salts input.positions,
    checker_decode_encoded_records]

theorem checker_cached_input_decodes (input : CheckInput) (heap : Nat → BitVec 238)
    (salts : Index → BitVec 128) (nonempty : input.positions.card≠0)
    (proof : input.proof=cachedEncodedPacket heap salts input.positions) :
    ∃ after cycles, RunsCheckerFooterBlock (Artifact.submission.initialState .check input) after cycles ∧
      cycles≤47652+2387*input.positions.card ∧
      CheckerDecodedInput input (cachedFooter (checkerInputFooterNodes input) heap) after := by
  have nodes : openingNodes input.positions=checkerInputFooterNodes input := by
    rw [cached_footer_nodes,InteriorCodec.footerNodes,ite_eq_right nonempty]
    rfl
  have recordBytes : (encodedRecords (cachedRecords heap salts input.positions)).length=482*input.positions.card := by
    rw [encoded_records_length,cached_records_count]
  have encoded : checkerInputFooterBytes input=SplitCodec.encode (cachedFooter (checkerInputFooterNodes input) heap) := by
    rw [checkerInputFooterBytes,proof,cachedEncodedPacket,←recordBytes,List.drop_left,nodes]
  have footprint := cached_encoded_length heap salts input.positions
  rw [←proof] at footprint
  have footerBound : InteriorCodec.footerBits (InteriorCodec.footerNodes input.positions)≤30208 := by
    rw [InteriorCodec.footerNodes,ite_eq_right nonempty]
    exact InteriorCodec.footer_bits_bound _
  change input.proof.length=482*input.positions.card+
    (InteriorCodec.footerBits (InteriorCodec.footerNodes input.positions)+7)/8 at footprint
  exact checker_encoded_input_decodes input nonempty (by omega) (by omega) _ encoded

theorem checker_delivered_opening_decodes (oracle : Oracle) (message : Message) (key : Key) (input : CheckInput)
    (nonempty : input.positions.card≠0)
    (opened : input.proof∈support (Artifact.submission.scheme.opening
      (Artifact.submission.readCommit (deliveredSeedOutput oracle message key)).2 input.positions)) :
    let heap := referenceHeap oracle (pinnedLeafNodes oracle (deliveredReady oracle message key))
    ∃ after cycles, RunsCheckerFooterBlock (Artifact.submission.initialState .check input) after cycles ∧
      cycles≤47652+2387*input.positions.card ∧
      CheckerDecodedInput input (cachedFooter (checkerInputFooterNodes input) heap) after := by
  rw [delivered_opening_reference,support_pure,Set.mem_singleton_iff] at opened
  exact checker_cached_input_decodes input _ _ nonempty opened

theorem checker_delivered_empty_opening_accepts (oracle : Oracle) (message : Message) (key : Key) (input : CheckInput)
    (empty : input.positions.card=0)
    (opened : input.proof∈support (Artifact.submission.scheme.opening
      (Artifact.submission.readCommit (deliveredSeedOutput oracle message key)).2 input.positions)) :
    Artifact.submission.scheme.check input.commitment input.positions input.values input.proof=Pure.pure (true : Bool) := by
  rw [delivered_opening_reference,cached_encoded_empty _ _ _ empty,support_pure,Set.mem_singleton_iff] at opened
  exact checker_empty_input_accepts input empty (by rw [opened]; rfl)

namespace Refinement
open RecordLeaf RecordTail CheckerCap CheckerCap.Visit

theorem continuation_chain_value (oracle : Oracle) (height : Height) (seed : Seed) (stage count : Nat) :
    (checkEvaluation oracle (continuationTrace height stage count (canonicalChainValue oracle height seed stage))).1=
      canonicalChainValue oracle height seed (stage+count) := by
  induction count generalizing stage with
  | zero => rfl
  | succ count ih =>
    rw [continuationTrace,check_evaluation_bind]
    change (checkEvaluation oracle (continuationTrace height (stage+1) count
      (canonicalChainValue oracle height seed (stage+1)))).1=_
    rw [ih]
    congr 1
    omega

theorem parent_value_chain (oracle : Oracle) (height : Height) (left right : Node) :
    (parentValue oracle height left right).setWidth 238=
      nodeDigest (width height) (canonicalChainValue oracle height (right++left) (calls height-1)) := by
  simp only [parentValue,parentDigestTrace,check_evaluation_bind,check_evaluation_pure]
  change (finalValue height (checkEvaluation oracle (continuationTrace height 0 (calls height-1)
    (canonicalChainValue oracle height (right++left) 0))).1).setWidth 238=_
  rw [continuation_chain_value,Nat.zero_add,final_value_node]

theorem first_lower_parent_value (oracle : Oracle) {base : CheckerRecordBase} {record : Nat}
    (input : CheckInput) (state : MachineState) (ready : CheckerFirstPathReady input state base record)
    (left right : Node) (children : firstRecordedSeed state base.value=right++left) :
    (readBuffer (firstLowerObservation oracle state).1.1 12288 32).setWidth 238=
      (parentValue oracle firstRecordedHeight left right).setWidth 238 := by
  rw [first_lower_observation_node oracle input state ready,firstRecordedValues,children,parent_value_chain]

theorem later_lower_parent_value (oracle : Oracle) {base : CheckerRecordBase} (height : Fin 16)
    (state : MachineState) (ready : CheckerLaterPathReady height state base) (left right : Node)
    (children : laterRecordedSeed state=right++left) :
    (readBuffer (laterLowerObservation oracle height state).1.1 12288 32).setWidth 238=
      (parentValue oracle ⟨height.val,by omega⟩ left right).setWidth 238 := by
  rw [later_lower_observation_node oracle height state ready,laterRecordedValues,children,parent_value_chain]

theorem heap_path_seed (heap : Nat → Node) (node : Nat) :
    pathSeed node (heap node) (heap (node ^^^ 1))=heap (2*(node/2)+1)++heap (2*(node/2)) := by
  by_cases even : node%2=0
  · rw [pathSeed,ite_eq_left even,Nat.xor_one_of_even (Nat.even_iff.mpr even),
      show 2*(node/2)+1=node+1 by omega,show 2*(node/2)=node by omega]
  · rw [pathSeed,ite_eq_right even,Nat.xor_one_of_odd (Nat.odd_iff.mpr (by omega)),
      show 2*(node/2)+1=node by omega,show 2*(node/2)=node-1 by omega]

theorem canonical_heap_climb (oracle : Oracle) (heap : Nat → Node) (tree : ChainedTree oracle heap)
    (height : Height) (node : Nat) (lower : heightCount height≤node/2) (upper : node/2<2*heightCount height) :
    nodeDigest (width height) (canonicalChainValue oracle height (pathSeed node (heap node) (heap (node ^^^ 1)))
      (calls height-1))=heap (node/2) := by
  rw [heap_path_seed,←parent_value_chain,←tree height (node/2) lower upper]
  apply BitVec.eq_of_getLsbD_eq
  intro bit inside
  simp only [BitVec.getLsbD_setWidth,inside,show bit<256 by omega,decide_true,Bool.true_and]

theorem uniform_flat_map_byte (values : List Nat) (entry : Nat → Proof) (size : Nat)
    (lengths : ∀ value, (entry value).length=size) (ordinal byte : Nat)
    (inside : ordinal<values.length) (short : byte<size) :
    (values.flatMap entry).getD (size*ordinal+byte) 0=(entry (values.getD ordinal 0)).getD byte 0 := by
  induction values generalizing ordinal with
  | nil => simp at inside
  | cons value values ih =>
    cases ordinal with
    | zero =>
      rw [List.flatMap_cons,List.getD_append _ _ _ _ (by simpa only [lengths,Nat.mul_zero,Nat.zero_add] using short)]
      simp only [Nat.mul_zero,Nat.zero_add,List.getD_cons_zero]
    | succ ordinal =>
      rw [List.flatMap_cons,List.getD_append_right _ _ _ _ (by rw [lengths,Nat.mul_add,Nat.mul_one]; omega),lengths,
        show size*(ordinal+1)+byte-size=size*ordinal+byte by rw [Nat.mul_add,Nat.mul_one]; omega]
      simpa only [List.getD_cons_succ] using ih ordinal (by simpa using inside)

theorem lower_record_sibling_byte (heap : Nat → Output) (index : Index) (salt : BitVec 128)
    (height : Fin 16) (byte : Nat) (inside : byte<(if height.val=0 then 32 else 30)) :
    (lowerRecord true heap index salt).getD (16+(if height.val=0 then 0 else 32+30*(height.val-1))+byte) 0=
      (heap (lowerNode index height.val ^^^ 1)).extractLsb' (8*byte) 8 := by
  let entry : Nat → Proof := fun level => proofDigestBytes true (heap (lowerNode index (level+1) ^^^ 1))
  have split : lowerRecord true heap index salt=saltBytes salt++
      (digestBytes (heap (lowerNode index 0 ^^^ 1))++(List.range 15).flatMap entry) := by
    unfold lowerRecord
    rw [List.range_succ_eq_map,List.flatMap_cons,List.flatMap_map]
    rfl
  rw [split,List.getD_append_right _ _ _ _ (by simp only [saltBytes,List.length_ofFn]; omega)]
  simp only [saltBytes,List.length_ofFn]
  by_cases first : height.val=0
  · simp only [first,ite_true,Nat.add_zero,Nat.add_sub_cancel_left] at inside ⊢
    rw [List.getD_append _ _ _ byte (by simpa only [digestBytes,List.length_ofFn] using inside)]
    simp only [digestBytes,List.getD_eq_getElem?_getD,List.getElem?_ofFn,inside,↓reduceDIte,Option.getD_some]
  · simp only [first,ite_false] at inside ⊢
    rw [show 16+(32+30*(height.val-1))+byte-16=32+(30*(height.val-1)+byte) by omega,
      List.getD_append_right _ _ _ _ (by simp only [digestBytes,List.length_ofFn]; omega)]
    simp only [digestBytes,List.length_ofFn,Nat.add_sub_cancel_left]
    have ordinal : height.val-1<15 := by have := height.isLt; omega
    rw [uniform_flat_map_byte (List.range 15) entry 30
      (by intro level; simp [entry,proofDigestBytes,digestBytes]) (height.val-1) byte
      (by simpa only [List.length_range] using ordinal) inside]
    have item : (List.range 15).getD (height.val-1) 0=height.val-1 := by
      rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by simpa only [List.length_range] using ordinal),
        Option.getD_some,List.getElem_range]
    rw [item]
    change ((digestBytes (heap (lowerNode index (height.val-1+1) ^^^ 1))).take 30).getD byte 0=_
    rw [Nat.sub_add_cancel (show 1≤height.val by omega)]
    simp only [List.getD_eq_getElem?_getD,List.getElem?_take,inside,↓reduceIte]
    simp only [digestBytes,List.getElem?_ofFn,show byte<32 by omega,↓reduceDIte,Option.getD_some]

theorem read_lower_record_sibling (state : MachineState) (source : Nat) (heap : Nat → Node)
    (index : Index) (salt : BitVec 128) (height : Fin 16)
    (raw : BytesAt state (BitVec.ofNat 64 source) (lowerRecord true (fun node => (heap node).setWidth 256) index salt)) :
    (readBuffer state (source+16+(if height.val=0 then 0 else 32+30*(height.val-1)))
      (if height.val=0 then 32 else 30)).setWidth 238=heap (lowerNode index height.val ^^^ 1) := by
  have data := read_serialized_slice state ((heap (lowerNode index height.val ^^^ 1)).setWidth 256)
    (source+16+(if height.val=0 then 0 else 32+30*(height.val-1))) 0
    (if height.val=0 then 32 else 30) (by
      intro byte inside
      have present : 16+(if height.val=0 then 0 else 32+30*(height.val-1))+byte<
          (lowerRecord true (fun node => (heap node).setWidth 256) index salt).length := by
        rw [lower_record_length]
        have bounded := height.isLt
        split_ifs at inside ⊢ <;> omega
      have memory := (raw _ present).trans
        (lower_record_sibling_byte (fun node => (heap node).setWidth 256) index salt height byte inside)
      simpa only [←BitVec.ofNat_add,Nat.add_assoc,Nat.zero_add] using memory)
  rw [data]
  apply BitVec.eq_of_getLsbD_eq
  intro bit inside
  have fits : bit<8*(if height.val=0 then 32 else 30) := by split_ifs <;> omega
  simp only [BitVec.getLsbD_setWidth,BitVec.getLsbD_extractLsb',Nat.mul_zero,Nat.zero_add,inside,fits,
    show bit<256 by omega,decide_true,Bool.true_and]

theorem lower_node_parent_range (index : Index) (height : Height) :
    heightCount height≤lowerNode index height.val/2 ∧ lowerNode index height.val/2<2*heightCount height := by
  have heightBound := height.isLt
  have indexBound := index.isLt
  have positive : 0<2^(height.val+1) := by positivity
  have product : 2^(23-height.val)*2^(height.val+1)=2^24 := by
    rw [←Nat.pow_add,show 23-height.val+(height.val+1)=24 by omega]
  have quotient : lowerNode index height.val/2=(LENGTH+index.val)/2^(height.val+1) := by
    rw [lowerNode,Nat.div_div_eq_div_mul,Nat.pow_succ]
  rw [quotient]
  constructor
  · apply (Nat.le_div_iff_mul_le positive).mpr
    change 2^(23-height.val)*2^(height.val+1)≤LENGTH+index.val
    rw [product]
    change 16777216≤16777216+index.val
    omega
  · apply (Nat.div_lt_iff_lt_mul positive).mpr
    change LENGTH+index.val<(2*2^(23-height.val))*2^(height.val+1)
    rw [Nat.mul_assoc,product]
    change 16777216+index.val<2*16777216
    change index.val<16777216 at indexBound
    omega

theorem first_lower_recovers_heap (oracle : Oracle) {base : CheckerRecordBase} {record : Nat}
    (input : CheckInput) (state : MachineState) (ready : CheckerFirstPathReady input state base record)
    (heap : Nat → Node) (tree : ChainedTree oracle heap) (index : Index) (salt : BitVec 128)
    (raw : BytesAt state (BitVec.ofNat 64 base.value)
      (lowerRecord true (fun node => (heap node).setWidth 256) index salt))
    (node : (state.getReg .x6).toNat=lowerNode index 0)
    (child : (readBuffer state 12288 32).setWidth 238=heap (lowerNode index 0)) :
    (readBuffer (firstLowerObservation oracle state).1.1 12288 32).setWidth 238=heap (lowerNode index 0/2) := by
  have sibling := read_lower_record_sibling state base.value heap index salt ⟨0,by decide⟩ raw
  change (readBuffer state (base.value+16) 32).setWidth 238=heap (lowerNode index 0 ^^^ 1) at sibling
  rw [first_lower_observation_node oracle input state ready,firstRecordedValues,first_recorded_seed_eq,
    node,child,sibling]
  apply canonical_heap_climb oracle heap tree firstRecordedHeight (lowerNode index 0)
  · simpa only [first_recorded_height_val] using (lower_node_parent_range index firstRecordedHeight).1
  · simpa only [first_recorded_height_val] using (lower_node_parent_range index firstRecordedHeight).2

theorem read_buffer_prefix (state : MachineState) (address large small : Nat) (fits : small≤large) :
    readBuffer state address small=(readBuffer state address large).extractLsb' 0 (8*small) := by
  exact read_serialized_slice state (readBuffer state address large) address 0 small (by
    intro byte inside
    simpa only [Nat.zero_add] using (read_buffer_byte state address large byte (by omega)).symm)

theorem read_buffer_node_30 (state : MachineState) (address : Nat) :
    (readBuffer state address 32).setWidth 238=(readBuffer state address 30).setWidth 238 := by
  rw [read_buffer_prefix state address 32 30 (by decide)]
  apply BitVec.eq_of_getLsbD_eq
  intro bit inside
  simp only [BitVec.getLsbD_setWidth,BitVec.getLsbD_extractLsb',Nat.zero_add,inside,
    show bit<8*30 by omega,decide_true,Bool.true_and]

theorem clear_tail_low_buffer (state : MachineState) (target : Nat) (even : target%2=0)
    (room : target+32≤2^64) :
    readBuffer (state.setHalfword (BitVec.ofNat 64 (target+30)) 0) target 30=readBuffer state target 30 := by
  apply lower_buffer_bytes
  intro byte inside
  apply CommitGolfCandidate.ProjectedHalfword.store_outside
  · rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show target+30<2^64 by omega)]
    omega
  · constructor
    · exact word_of_nat_ne _ _ (by omega) (by omega) (by omega)
    · have next : (BitVec.ofNat 64 (target+30) : Word)+1=BitVec.ofNat 64 (target+31) := by
        rw [show (1 : Word)=BitVec.ofNat 64 1 from rfl,←BitVec.ofNat_add]
      rw [next]
      exact word_of_nat_ne _ _ (by omega) (by omega) (by omega)

theorem later_pad_low_buffer (order : FirstSiblingOrder) (state : MachineState)
    (pair : state.getReg .x24=12544) :
    readBuffer (checkerLaterPadState order state) (match order with | .even => 12576 | .odd => 12544) 30=
      readBuffer state (match order with | .even => 12576 | .odd => 12544) 30 := by
  rw [checkerLaterPadState]
  change readBuffer (state.setHalfword (state.getReg .x24+signExtend12 order.laterPadOffset) 0) _ 30=_
  rw [pair]
  cases order with
  | even => exact clear_tail_low_buffer state 12576 (by decide) (by decide)
  | odd => exact clear_tail_low_buffer state 12544 (by decide) (by decide)

theorem first_child_low_buffer_outside (order : FirstSiblingOrder) (state : MachineState)
    (digest : state.getReg .x23=12288) (pair : state.getReg .x24=12544) (address : Nat)
    (aligned : address%8=0) (room : address+32≤2^64)
    (apart : 12544+order.childOffset+32≤address ∨ address+32≤12544+order.childOffset) :
    readBuffer (checkerFirstChildPrefix order state 8) address 30=readBuffer state address 30 := by
  rw [read_buffer_prefix _ address 32 30 (by decide),
    checker_first_child_buffer_outside order state digest pair address aligned room apart,
    ←read_buffer_prefix state address 32 30 (by decide)]

theorem later_ordered_sibling_buffer {base : CheckerRecordBase} (height : Fin 16)
    (state : MachineState) (ready : CheckerLaterPathReady height state base) :
    readBuffer (checkerLaterOrderedState state) (if state.getReg .x6 &&& 1=0 then 12576 else 12544) 30=
      readBuffer state (checkerLowerCursor ⟨height.val,by omega⟩ base.value) 30 := by
  have digest : (checkerLaterDispatchPrefix state 5).getReg .x23=12288 :=
    (checker_later_dispatch_register _ _ (by decide) (by decide)).trans ready.digest
  have pair : (checkerLaterDispatchPrefix state 5).getReg .x24=12544 :=
    (checker_later_dispatch_register _ _ (by decide) (by decide)).trans ready.pair
  have ordered : 12576≤checkerLowerCursor ⟨height.val,by omega⟩ base.value := by
    have := base.above
    simp only [checkerLowerCursor]
    omega
  have dispatch (address : Nat) : readBuffer (checkerLaterDispatchPrefix state 5) address 30=readBuffer state address 30 := by
    apply read_buffer_memory_congr
    funext query
    exact checker_later_dispatch_memory state query
  have jump (order : FirstSiblingOrder) (before : MachineState) (address : Nat) :
      readBuffer (checkerLaterJumpState order before) address 30=readBuffer before address 30 := by
    apply read_buffer_memory_congr
    funext query
    exact checker_later_jump_memory order before query
  rw [checkerLaterOrderedState]
  by_cases even : state.getReg .x6 &&& 1=0
  · simp only [even,ite_true]
    have childPair := (checker_first_child_register .even (checkerLaterDispatchPrefix state 5) 8
      (by omega) .x24 (by decide)).trans pair
    have copyPair := (checker_copy_register .even
      (checkerFirstChildPrefix .even (checkerLaterDispatchPrefix state 5) 8) .x24 (by decide)).trans childPair
    have copied := checker_copy_buffer .even _ _ _ (checker_later_even_copy_ready height state ready even) ordered
    simp only [CheckerCopySite.count,Nat.reduceMul] at copied
    have sourceAbove : 32768≤checkerLowerCursor ⟨height.val,by omega⟩ base.value := by
      have := base.above
      simp only [checkerLowerCursor]
      omega
    have sourceRoom : checkerLowerCursor ⟨height.val,by omega⟩ base.value+32≤2^64 := by
      have high : base.value+528≤2^36 := base.room
      have := height.isLt
      simp only [checkerLowerCursor]
      split_ifs <;> omega
    have childSource : readBuffer (checkerFirstChildPrefix .even (checkerLaterDispatchPrefix state 5) 8)
        (checkerLowerCursor ⟨height.val,by omega⟩ base.value) 30=
        readBuffer (checkerLaterDispatchPrefix state 5) (checkerLowerCursor ⟨height.val,by omega⟩ base.value) 30 := by
      rw [read_buffer_prefix _ _ 32 30 (by decide),
        checker_first_child_buffer_above .even _ digest pair _ sourceAbove sourceRoom,
        ←read_buffer_prefix _ _ 32 30 (by decide)]
    rw [jump,later_pad_low_buffer .even _ copyPair]
    simp only []
    rw [copied,childSource,dispatch]
  · simp only [even,ite_false]
    have copyPair := (checker_copy_register .odd (checkerLaterDispatchPrefix state 5) .x24 (by decide)).trans pair
    have copyDigest := (checker_copy_register .odd (checkerLaterDispatchPrefix state 5) .x23 (by decide)).trans digest
    have padPair := (checker_later_pad_register .odd _ .x24).trans copyPair
    have padDigest := (checker_later_pad_register .odd _ .x23).trans copyDigest
    have copied := checker_copy_buffer .odd _ _ _ (checker_later_odd_copy_ready height state ready even) (by omega)
    simp only [CheckerCopySite.count,Nat.reduceMul] at copied
    rw [jump,first_child_low_buffer_outside .odd _ padDigest padPair _ (by decide) (by decide) (Or.inr (by decide)),
      later_pad_low_buffer .odd _ copyPair]
    simp only []
    rw [copied,dispatch]

theorem later_recorded_sibling_data {base : CheckerRecordBase} (height : Fin 16)
    (state : MachineState) (ready : CheckerLaterPathReady height state base) :
    laterRecordedSibling state=(readBuffer state (checkerLowerCursor ⟨height.val,by omega⟩ base.value) 30).setWidth 238 := by
  have data := later_ordered_sibling_buffer height state ready
  rw [laterRecordedSibling]
  by_cases even : state.getReg .x6 &&& 1=0
  · simp only [even,ite_true] at data ⊢
    rw [read_buffer_node_30,data]
  · simp only [even,ite_false] at data ⊢
    rw [read_buffer_node_30,data]

theorem read_lower_record_positive_sibling (state : MachineState) (source : Nat) (heap : Nat → Node)
    (index : Index) (salt : BitVec 128) (height : Fin 16) (positive : 0<height.val)
    (raw : BytesAt state (BitVec.ofNat 64 source) (lowerRecord true (fun node => (heap node).setWidth 256) index salt)) :
    (readBuffer state (checkerLowerCursor ⟨height.val,by omega⟩ source) 30).setWidth 238=
      heap (lowerNode index height.val ^^^ 1) := by
  rcases height with ⟨level,small⟩
  cases level with
  | zero =>
    change 0<0 at positive
    omega
  | succ level =>
    have data := read_lower_record_sibling state source heap index salt ⟨level+1,small⟩ raw
    change (readBuffer state (source+16+(32+30*level)) 30).setWidth 238=
      heap (lowerNode index (level+1) ^^^ 1) at data
    change (readBuffer state (source+(48+30*level)) 30).setWidth 238=_
    rw [show source+(48+30*level)=source+16+(32+30*level) by omega]
    exact data

theorem later_lower_recovers_heap (oracle : Oracle) {base : CheckerRecordBase} (height : Fin 16)
    (state : MachineState) (ready : CheckerLaterPathReady height state base)
    (heap : Nat → Node) (tree : ChainedTree oracle heap) (index : Index) (salt : BitVec 128)
    (raw : BytesAt state (BitVec.ofNat 64 base.value)
      (lowerRecord true (fun node => (heap node).setWidth 256) index salt))
    (node : (state.getReg .x6).toNat=lowerNode index height.val)
    (child : (readBuffer state 12288 32).setWidth 238=heap (lowerNode index height.val)) :
    (readBuffer (laterLowerObservation oracle height state).1.1 12288 32).setWidth 238=
      heap (lowerNode index height.val/2) := by
  have sibling : laterRecordedSibling state=heap (lowerNode index height.val ^^^ 1) := by
    rw [later_recorded_sibling_data height state ready]
    exact read_lower_record_positive_sibling state base.value heap index salt height ready.positive raw
  rw [later_lower_observation_node oracle height state ready,laterRecordedValues,
    later_recorded_seed_eq height state ready,node,child,sibling]
  exact canonical_heap_climb oracle heap tree ⟨height.val,by omega⟩ (lowerNode index height.val)
    (lower_node_parent_range index ⟨height.val,by omega⟩).1
    (lower_node_parent_range index ⟨height.val,by omega⟩).2

theorem lower_record_raw_frame (before after : MachineState) (base : CheckerRecordBase)
    (same : ∀ query, OutsideLower query → after.getMem query=before.getMem query)
    (heap : Nat → Node) (index : Index) (salt : BitVec 128)
    (raw : BytesAt before (BitVec.ofNat 64 base.value)
      (lowerRecord true (fun node => (heap node).setWidth 256) index salt)) :
    BytesAt after (BitVec.ofNat 64 base.value)
      (lowerRecord true (fun node => (heap node).setWidth 256) index salt) := by
  intro byte inside
  have short : byte<498 := by simpa only [lower_record_length,ite_true] using inside
  have low := base.above
  have high : base.value+528≤2^36 := base.room
  have room : 2^36+64<2^64 := by decide
  have memory := raw byte inside
  rw [←BitVec.ofNat_add] at memory ⊢
  exact (lower_memory_byte before after same (base.value+byte) (by omega) (by omega)).trans memory

theorem lower_suffix_recovers_heap (oracle : Oracle) {base : CheckerRecordBase} (count : Nat)
    (height : Fin 17) (room : height.val+count≤16) (state : MachineState)
    (positive : 0<height.val) (ready : CheckerLowerLoopReady height state base)
    (heap : Nat → Node) (tree : ChainedTree oracle heap) (index : Index) (salt : BitVec 128)
    (raw : BytesAt state (BitVec.ofNat 64 base.value)
      (lowerRecord true (fun node => (heap node).setWidth 256) index salt))
    (node : (state.getReg .x6).toNat=lowerNode index height.val)
    (child : (readBuffer state 12288 32).setWidth 238=heap (lowerNode index height.val)) :
    (readBuffer (lowerSuffixObservation oracle count height room state).1.1 12288 32).setWidth 238=
      heap (lowerNode index (height.val+count)) := by
  induction count generalizing height state with
  | zero =>
    rw [lower_suffix_observation_eq,checkerLowerSuffixTrace,record_rows_pure,check_evaluation_pure]
    simpa only [Nat.add_zero] using child
  | succ count ih =>
    have active : height.val<16 := by omega
    have stepReady := checker_lower_loop_later height state positive active ready
    have reached : (laterLowerObservation oracle ⟨height.val,active⟩ state).1.1∈
        support (checkerLaterLowerTrace ⟨height.val,active⟩ state) := by
      rw [later_lower_observation_eq]
      exact recorded_evaluation_support oracle _
    have nextReady := checker_later_lower_next ⟨height.val,active⟩ state _ stepReady reached
    have nextRaw := lower_record_raw_frame state _ base
      (checker_later_lower_memory ⟨height.val,active⟩ state _ stepReady reached) heap index salt raw
    have nextNode : ((laterLowerObservation oracle ⟨height.val,active⟩ state).1.1.getReg .x6).toNat=
        lowerNode index (height.val+1) := by
      rw [(checker_later_lower_values ⟨height.val,active⟩ state _ stepReady reached).2.1]
      simp only [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,Nat.pow_one,node,lower_node_next]
    have nextChild : (readBuffer (laterLowerObservation oracle ⟨height.val,active⟩ state).1.1 12288 32).setWidth 238=
        heap (lowerNode index (height.val+1)) := by
      simpa only [lower_node_next] using
        later_lower_recovers_heap oracle ⟨height.val,active⟩ state stepReady heap tree index salt raw node child
    have tail := ih ⟨height.val+1,by omega⟩ (by change height.val+1+count≤16; omega) _
      (by change 0<height.val+1; omega) nextReady nextRaw nextNode nextChild
    rw [lower_suffix_observation_succ]
    simpa only [show height.val+1+count=height.val+(count+1) by omega] using tail

theorem first_boundary_raw (oracle : Oracle) {base : CheckerRecordBase} {record : Nat}
    (input : CheckInput) (state : MachineState) (ready : CheckerFirstPathReady input state base record)
    (heap : Nat → Node) (index : Index) (salt : BitVec 128)
    (raw : BytesAt state (BitVec.ofNat 64 base.value)
      (lowerRecord true (fun node => (heap node).setWidth 256) index salt)) :
    BytesAt (firstBoundaryState oracle state) (BitVec.ofNat 64 base.value)
      (lowerRecord true (fun node => (heap node).setWidth 256) index salt) :=
  lower_record_raw_frame state _ base
    (checker_first_lower_memory input state _ ready (first_boundary_support oracle state)) heap index salt raw

theorem first_boundary_lower_index (oracle : Oracle) {base : CheckerRecordBase} {record : Nat}
    (input : CheckInput) (state : MachineState) (ready : CheckerFirstPathReady input state base record) (index : Index)
    (node : (state.getReg .x6).toNat=lowerNode index 0) :
    ((firstBoundaryState oracle state).getReg .x6).toNat=lowerNode index 1 := by
  rw [first_boundary_index_nat oracle input state ready,node]
  exact (lower_node_next index 0).symm

theorem first_boundary_recovers_heap (oracle : Oracle) {base : CheckerRecordBase} {record : Nat}
    (input : CheckInput) (state : MachineState) (ready : CheckerFirstPathReady input state base record)
    (heap : Nat → Node) (tree : ChainedTree oracle heap) (index : Index) (salt : BitVec 128)
    (raw : BytesAt state (BitVec.ofNat 64 base.value)
      (lowerRecord true (fun node => (heap node).setWidth 256) index salt))
    (node : (state.getReg .x6).toNat=lowerNode index 0)
    (child : (readBuffer state 12288 32).setWidth 238=heap (lowerNode index 0)) :
    (readBuffer (firstBoundaryState oracle state) 12288 32).setWidth 238=heap (lowerNode index 1) := by
  rw [first_boundary_state_eq]
  simpa only [lower_node_next] using first_lower_recovers_heap oracle input state ready heap tree index salt raw node child

theorem height_one_suffix_recovers_heap (oracle : Oracle) {base : CheckerRecordBase} (count : Nat)
    (closes : count+1=16) (state : MachineState) (ready : CheckerLowerLoopReady ⟨1,by decide⟩ state base)
    (heap : Nat → Node) (tree : ChainedTree oracle heap) (index : Index) (salt : BitVec 128)
    (raw : BytesAt state (BitVec.ofNat 64 base.value)
      (lowerRecord true (fun node => (heap node).setWidth 256) index salt))
    (node : (state.getReg .x6).toNat=lowerNode index 1)
    (child : (readBuffer state 12288 32).setWidth 238=heap (lowerNode index 1)) :
    (readBuffer (lowerSuffixObservation oracle count ⟨1,by decide⟩ (by change 1+count≤16; omega) state).1.1
      12288 32).setWidth 238=heap (lowerNode index 16) := by
  have recovered := lower_suffix_recovers_heap oracle count ⟨1,by decide⟩
    (by change 1+count≤16; omega) state (by decide)
    ready heap tree index salt raw node child
  simpa only [show 1+count=16 by omega] using recovered

theorem height_one_fifteen_suffix_recovers_heap (oracle : Oracle) {base : CheckerRecordBase}
    (state : MachineState) (ready : CheckerLowerLoopReady ⟨1,by decide⟩ state base)
    (heap : Nat → Node) (tree : ChainedTree oracle heap) (index : Index) (salt : BitVec 128)
    (raw : BytesAt state (BitVec.ofNat 64 base.value)
      (lowerRecord true (fun node => (heap node).setWidth 256) index salt))
    (node : (state.getReg .x6).toNat=lowerNode index 1)
    (child : (readBuffer state 12288 32).setWidth 238=heap (lowerNode index 1)) :
    (readBuffer (lowerSuffixObservation oracle 15 ⟨1,by decide⟩ (by decide) state).1.1 12288 32).setWidth 238=
      heap (lowerNode index 16) :=
  height_one_suffix_recovers_heap oracle 15 (by decide) state ready heap tree index salt raw node child

theorem observed_value_of_append {α β γ δ : Type} (value : α → δ)
    (first later whole : (α × List β) × γ) (combine : γ → γ → γ)
    (mapped : whole=((later.1.1,first.1.2++later.1.2),combine first.2 later.2))
    (root : δ) (result : value later.1.1=root) : value whole.1.1=root := by
  rw [mapped]
  exact result

theorem lower_sixteen_recovers_heap (oracle : Oracle) {base : CheckerRecordBase} {record : Nat}
    (input : CheckInput) (state : MachineState) (ready : CheckerFirstPathReady input state base record)
    (heap : Nat → Node) (tree : ChainedTree oracle heap) (index : Index) (salt : BitVec 128)
    (raw : BytesAt state (BitVec.ofNat 64 base.value)
      (lowerRecord true (fun node => (heap node).setWidth 256) index salt))
    (node : (state.getReg .x6).toNat=lowerNode index 0)
    (child : (readBuffer state 12288 32).setWidth 238=heap (lowerNode index 0)) :
    (readBuffer (lowerSixteenObservation oracle state).1.1 12288 32).setWidth 238=heap (lowerNode index 16) :=
  observed_value_of_append (fun out : MachineState => (readBuffer out 12288 32).setWidth 238)
    ((firstBoundaryState oracle state,(firstLowerObservation oracle state).1.2),(firstLowerObservation oracle state).2)
    (lowerSuffixObservation oracle 15 ⟨1,by decide⟩ (by decide) (firstBoundaryState oracle state))
    (lowerSixteenObservation oracle state) Nat.add (lower_sixteen_boundary_bind oracle state) _
    (height_one_fifteen_suffix_recovers_heap oracle _ (first_boundary_ready oracle input state ready) heap tree index salt
      (first_boundary_raw oracle input state ready heap index salt raw)
      (first_boundary_lower_index oracle input state ready index node)
      (first_boundary_recovers_heap oracle input state ready heap tree index salt raw node child))

theorem canonical_heap_parent (oracle : Oracle) (heap : Nat → Node) (tree : ChainedTree oracle heap)
    (height : Height) (node : Nat) (lower : heightCount height≤node) (upper : node<2*heightCount height) :
    nodeDigest (width height) (canonicalChainValue oracle height (heap (2*node+1)++heap (2*node))
      (calls height-1))=heap node := by
  rw [←parent_value_chain,←tree height node lower upper]
  apply BitVec.eq_of_getLsbD_eq
  intro bit inside
  simp only [BitVec.getLsbD_setWidth,inside,show bit<256 by omega,decide_true,Bool.true_and]

theorem cap_seed_heap_nodes (state : MachineState) (node : Fin 256) :
    capRecordedSeed state node=capHeapNode state (2*node.val+1)++capHeapNode state (2*node.val) := by
  rw [capRecordedSeed,capHeapNode,capHeapNode,
    show 16384+32*(2*node.val+1)=16384+64*node.val+32 by omega,
    show 16384+32*(2*node.val)=16384+64*node.val by omega]

theorem cap_loop_recovers_heap (oracle : Oracle) (height : Fin 8) (node : Fin 256)
    (range : CapNodeRange height node) (state : MachineState) (pc : state.pc=4096+4*2708)
    (child : state.getReg .x6=BitVec.ofNat 64 (2*node.val+1)) (roots : state.getReg .x25=16384)
    (heap : Nat → Node) (tree : ChainedTree oracle heap)
    (left : capHeapNode state (2*node.val)=heap (2*node.val))
    (right : capHeapNode state (2*node.val+1)=heap (2*node.val+1)) :
    capHeapNode (capLoopObservation oracle height state).1.1 node.val=heap node.val := by
  have heightBound := height.isLt
  have counted : heightCount (CheckerCap.capHeight height)=2^(7-height.val) := by
    change 2^(23-(16+height.val))=2^(7-height.val)
    congr 1
    omega
  have lower : heightCount (CheckerCap.capHeight height)≤node.val := by rw [counted]; exact range.1
  have upper : node.val<2*heightCount (CheckerCap.capHeight height) := by
    rw [counted]
    simpa only [show 8-height.val=7-height.val+1 by omega,Nat.pow_succ,Nat.mul_comm] using range.2
  rw [capHeapNode,cap_loop_observation_node oracle height node range state pc child roots,
    capRecordedValues,cap_call_seed,cap_seed_heap_nodes,left,right]
  exact canonical_heap_parent oracle heap tree _ node.val lower upper

theorem read_proof_digest_buffer (state : MachineState) (source : Nat) (value : Node)
    (raw : BytesAt state (BitVec.ofNat 64 source) (proofDigestBytes true (value.setWidth 256))) :
    readBuffer state source 30=(value.setWidth 256).extractLsb' 0 240 := by
  apply read_serialized_slice state (value.setWidth 256) source 0 30
  intro byte inside
  have memory := raw byte (by simpa only [proof_digest_length,ite_true] using inside)
  rw [←BitVec.ofNat_add] at memory
  simp only [proofDigestBytes,ite_true,List.getD_eq_getElem?_getD,List.getElem?_take,inside,↓reduceIte,
    digestBytes,List.getElem?_ofFn,show byte<32 by omega,↓reduceDIte,Option.getD_some] at memory
  simpa only [Nat.zero_add] using memory

theorem padded_proof_digest (state : MachineState) (source : Nat) (value : Node)
    (raw : BytesAt state (BitVec.ofNat 64 source) (proofDigestBytes true (value.setWidth 256))) :
    (0#16++readBuffer state source 30)=value.setWidth 256 := by
  rw [read_proof_digest_buffer state source value raw]
  apply BitVec.eq_of_getLsbD_eq
  intro bit inside
  simp only [BitVec.getLsbD_append,BitVec.getLsbD_extractLsb',Nat.zero_add,
    BitVec.getLsbD_setWidth,BitVec.getLsbD_zero]
  by_cases low : bit<240
  · simp only [low,ite_true,inside,decide_true,Bool.true_and]
  · simp only [low,ite_false,inside,decide_true,Bool.true_and]
    exact (BitVec.getLsbD_of_ge value bit (by omega)).symm

theorem cap_frontier_recovers_heap (state : MachineState) (node source : Nat) (ready : FrontierReady state node source)
    (fits : ¬state.getReg .x22<state.getReg .x21+30#64) (value : Node)
    (raw : BytesAt state (BitVec.ofNat 64 source) (proofDigestBytes true (value.setWidth 256))) :
    TwoPermutationPrototype.Checker.capRootAt (frontierRead state) node=value.setWidth 256 := by
  have read := actualFrontier.digest state node source ready fits
  change TwoPermutationPrototype.Checker.capRootAt (frontierRead state) node=_ at read
  exact read.trans (padded_proof_digest state source value raw)

theorem read_masked_node_buffer (state : MachineState) (address : Nat) (aligned : address%8=0)
    (room : address+32≤2^64) :
    readBuffer (state.setMem (BitVec.ofNat 64 (address+24))
      ((state.getMem (BitVec.ofNat 64 (address+24)) <<< 18) >>> 18)) address 32=
      ((readBuffer state address 32).setWidth 238).setWidth 256 := by
  apply output_ext_words
  intro word
  rw [BitVec.extractLsb'_setWidth_of_le (by have := word.isLt; omega)]
  change (readBuffer _ address 32).extractLsb' (64*word.val) 64=
    childWord ((readBuffer state address 32).setWidth 238) word.val
  rw [lower_child_word,read_digest_word _ address word.val aligned word.isLt]
  by_cases last : word.val=3
  · simp only [last,ite_true]
    rw [read_digest_word state address 3 aligned (by decide)]
    exact MachineState.getMem_setMem_eq
  · simp only [last,ite_false]
    rw [read_digest_word state address word.val aligned word.isLt]
    apply MachineState.getMem_setMem_ne
    exact word_of_nat_ne _ _ (by have := word.isLt; omega) (by omega) (by have := word.isLt; omega)

theorem cap_finish_buffer (state : MachineState) (node : Fin 256)
    (destination : state.getReg .x12=capDestination node) :
    readBuffer (capFinishPrefix state 7) (16384+32*node.val) 32=
      ((readBuffer state (16384+32*node.val) 32).setWidth 238).setWidth 256 := by
  rw [read_buffer_memory_congr _ _ (cap_finish_mask_memory state) (16384+32*node.val) 32,destination]
  have address : capDestination node+24=BitVec.ofNat 64 (16384+32*node.val+24) := by
    rw [capDestination,show (24 : Word)=BitVec.ofNat 64 24 from rfl,←BitVec.ofNat_add]
  rw [address]
  exact read_masked_node_buffer state _ (by omega) (by have := node.isLt; omega)

theorem extended_node_shrink (value : Node) : (value.setWidth 256).setWidth 238=value := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit inside
  simp only [BitVec.getLsbD_setWidth,inside,show bit<256 by omega,decide_true,Bool.true_and]

theorem buffer_eq_extended_of_mask (buffer source : Output) (node : Node)
    (full : buffer=(source.setWidth 238).setWidth 256) (low : buffer.setWidth 238=node) :
    buffer=node.setWidth 256 := by
  rw [full,extended_node_shrink] at low
  exact full.trans (congrArg (fun value : Node => value.setWidth 256) low)

theorem checker_lower_finish_buffer (state : MachineState) (digest : state.getReg .x23=12288) :
    readBuffer (checkerLowerFinishPrefix state 10) 12288 32=
      ((readBuffer state 12288 32).setWidth 238).setWidth 256 := by
  rw [read_buffer_memory_congr _ _ (checker_lower_finish_memory state digest) 12288 32,
    trunc_lower_digest state digest]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat,BitVec.toNat_setWidth]

theorem cap_loop_recovers_full_heap (oracle : Oracle) (height : Fin 8) (node : Fin 256)
    (range : CapNodeRange height node) (state : MachineState) (pc : state.pc=4096+4*2708)
    (child : state.getReg .x6=BitVec.ofNat 64 (2*node.val+1)) (roots : state.getReg .x25=16384)
    (heap : Nat → Node) (tree : ChainedTree oracle heap)
    (left : capHeapNode state (2*node.val)=heap (2*node.val))
    (right : capHeapNode state (2*node.val+1)=heap (2*node.val+1)) :
    readBuffer (capLoopObservation oracle height state).1.1 (16384+32*node.val) 32=(heap node.val).setWidth 256 := by
  have low := cap_loop_recovers_heap oracle height node range state pc child roots heap tree left right
  rw [capHeapNode] at low
  refine buffer_eq_extended_of_mask _
    (readBuffer (checkerHashReturned .cap (capHashObservation oracle height (capCallPrefix state 6)).1.1)
      (16384+32*node.val) 32) _ ?_ low
  rw [cap_loop_observation_map]
  exact cap_finish_buffer _ node (cap_loop_restored_destination oracle height node range state pc child roots)

@[irreducible] def LowerDigestFits (state : MachineState) : Prop :=
  ((readBuffer state 12288 32).setWidth 238).setWidth 256=readBuffer state 12288 32

theorem lower_digest_fits_of_finish (state : MachineState) (digest : state.getReg .x23=12288) :
    LowerDigestFits (checkerLowerFinishPrefix state 10) := by
  rw [LowerDigestFits,checker_lower_finish_buffer state digest,extended_node_shrink]

theorem first_lower_digest_fits (oracle : Oracle) {base : CheckerRecordBase} {record : Nat}
    (input : CheckInput) (state : MachineState) (ready : CheckerFirstPathReady input state base record) :
    LowerDigestFits (firstLowerObservation oracle state).1.1 := by
  have reached := first_hash_observation_support oracle state
  have digest := checker_first_sibling_return_digest input state _ ready reached
  rw [first_lower_observation_map]
  exact lower_digest_fits_of_finish _ digest

theorem later_lower_digest_fits (oracle : Oracle) {base : CheckerRecordBase} (height : Fin 16)
    (state : MachineState) (ready : CheckerLaterPathReady height state base) :
    LowerDigestFits (laterLowerObservation oracle height state).1.1 := by
  have reached : (laterHashObservation oracle height state).1.1∈support (checkerLaterHashTrace height state) := by
    rw [later_hash_observation_eq]
    exact recorded_evaluation_support oracle _
  have digest := checker_later_return_digest height state _ ready reached
  rw [later_lower_observation_map]
  exact lower_digest_fits_of_finish _ digest

theorem lower_suffix_digest_fits (oracle : Oracle) {base : CheckerRecordBase} (count : Nat)
    (height : Fin 17) (room : height.val+count≤16) (state : MachineState)
    (positive : 0<height.val) (ready : CheckerLowerLoopReady height state base) (fits : LowerDigestFits state) :
    LowerDigestFits (lowerSuffixObservation oracle count height room state).1.1 := by
  induction count generalizing height state with
  | zero =>
    rw [lower_suffix_observation_eq,checkerLowerSuffixTrace,record_rows_pure,check_evaluation_pure]
    exact fits
  | succ count ih =>
    have active : height.val<16 := by omega
    have stepReady := checker_lower_loop_later height state positive active ready
    have reached : (laterLowerObservation oracle ⟨height.val,active⟩ state).1.1∈
        support (checkerLaterLowerTrace ⟨height.val,active⟩ state) := by
      rw [later_lower_observation_eq]
      exact recorded_evaluation_support oracle _
    have nextReady := checker_later_lower_next ⟨height.val,active⟩ state _ stepReady reached
    have nextFits := later_lower_digest_fits oracle ⟨height.val,active⟩ state stepReady
    rw [lower_suffix_observation_succ]
    exact ih ⟨height.val+1,by omega⟩ (by change height.val+1+count≤16; omega) _
      (by change 0<height.val+1; omega) nextReady nextFits

theorem observed_predicate_of_append {α β γ : Type} (predicate : α → Prop)
    (first later whole : (α × List β) × γ) (combine : γ → γ → γ)
    (mapped : whole=((later.1.1,first.1.2++later.1.2),combine first.2 later.2))
    (holds : predicate later.1.1) : predicate whole.1.1 := by
  rw [mapped]
  exact holds

theorem first_boundary_digest_fits (oracle : Oracle) {base : CheckerRecordBase} {record : Nat}
    (input : CheckInput) (state : MachineState) (ready : CheckerFirstPathReady input state base record) :
    LowerDigestFits (firstBoundaryState oracle state) := by
  rw [first_boundary_state_eq]
  exact first_lower_digest_fits oracle input state ready

theorem lower_sixteen_digest_fits (oracle : Oracle) {base : CheckerRecordBase} {record : Nat}
    (input : CheckInput) (state : MachineState) (ready : CheckerFirstPathReady input state base record) :
    LowerDigestFits (lowerSixteenObservation oracle state).1.1 :=
  observed_predicate_of_append LowerDigestFits
    ((firstBoundaryState oracle state,(firstLowerObservation oracle state).1.2),(firstLowerObservation oracle state).2)
    (lowerSuffixObservation oracle 15 ⟨1,by decide⟩ (by decide) (firstBoundaryState oracle state))
    (lowerSixteenObservation oracle state) Nat.add (lower_sixteen_boundary_bind oracle state)
    (lower_suffix_digest_fits oracle 15 ⟨1,by decide⟩ (by decide) _ (by decide)
      (first_boundary_ready oracle input state ready) (first_boundary_digest_fits oracle input state ready))

theorem lower_sixteen_recovers_full_heap (oracle : Oracle) {base : CheckerRecordBase} {record : Nat}
    (input : CheckInput) (state : MachineState) (ready : CheckerFirstPathReady input state base record)
    (heap : Nat → Node) (tree : ChainedTree oracle heap) (index : Index) (salt : BitVec 128)
    (raw : BytesAt state (BitVec.ofNat 64 base.value)
      (lowerRecord true (fun node => (heap node).setWidth 256) index salt))
    (node : (state.getReg .x6).toNat=lowerNode index 0)
    (child : (readBuffer state 12288 32).setWidth 238=heap (lowerNode index 0)) :
    readBuffer (lowerSixteenObservation oracle state).1.1 12288 32=(heap (lowerNode index 16)).setWidth 256 := by
  have low := lower_sixteen_recovers_heap oracle input state ready heap tree index salt raw node child
  have fits := lower_sixteen_digest_fits oracle input state ready
  rw [LowerDigestFits] at fits
  exact fits.symm.trans (congrArg (fun value : Node => value.setWidth 256) low)

theorem checker_cached_input_record (input : CheckInput) (heap : Nat → Node) (salts : Index → BitVec 128)
    (record : Nat) (present : record < input.positions.card)
    (proof : input.proof=cachedEncodedPacket heap salts input.positions) :
    checkerDecodedRecordAt input record=cachedRecord heap (salts (checkerRecordInputIndex input record))
      (checkerRecordInputIndex input record) := by
  have live : record<(input.positions.sort (·≤·)).length := by simpa using present
  rw [checkerDecodedRecordAt,proof,cachedEncodedPacket,←cached_records_count heap salts input.positions,
    checker_decode_encoded_records,cachedRecords,List.getElem?_eq_getElem (by simpa only [List.length_map] using live),
    Option.getD_some,List.getElem_map,checkerRecordInputIndex,List.getElem?_eq_getElem live,Option.getD_some]

theorem cached_record_nonce (heap : Nat → Node) (salt : BitVec 128) (index : Index)
    (masked : salt.toNat<2^121) : checkerDecodedNonce (cachedRecord heap salt index)=salt := by
  change ((salt.setWidth 256).setWidth 121).setWidth 128=salt
  apply BitVec.eq_of_toNat_eq
  have wide : salt.toNat<2^256 := salt.isLt.trans_le (Nat.pow_le_pow_right (by decide) (by decide : 128≤256))
  simp only [BitVec.toNat_setWidth,Nat.mod_eq_of_lt wide,Nat.mod_eq_of_lt masked,Nat.mod_eq_of_lt salt.isLt]

theorem checker_cached_input_nonce (input : CheckInput) (heap : Nat → Node) (salts : Index → BitVec 128)
    (masked : ∀ index, (salts index).toNat<2^121) (record : Nat) (present : record < input.positions.card)
    (proof : input.proof=cachedEncodedPacket heap salts input.positions) :
    checkerDecodedNonce (checkerDecodedRecordAt input record)=salts (checkerRecordInputIndex input record) := by
  rw [checker_cached_input_record input heap salts record present proof]
  exact cached_record_nonce heap _ _ (masked _)

theorem node_digest_238 (value : Output) : nodeDigest 238 value=value.setWidth 238 := by
  apply BitVec.eq_of_toNat_eq
  simp [nodeDigest,lowBits,BitVec.toNat_setWidth,BitVec.toNat_ofNat]

theorem delivered_reference_leaf (oracle : Oracle) (message : Message) (key : Key) (index : Index) :
    referenceHeap oracle (pinnedLeafNodes oracle (deliveredReady oracle message key)) (LENGTH+index.val)=
      nodeDigest 238 (pinnedLeafDigest oracle.permutation index
        (saltWords (deliveredSalts oracle key index)) (entryWords (message index))) := by
  have small := index.isLt
  rw [reference_heap_leaf oracle _ _ (by change 2^24≤2^24+index.val; omega)
    (by change 2^24+index.val<2^25; change index.val<2^24 at small; omega),delivered_leaf_digest,node_digest_238]
  rfl

theorem checker_honest_record_leaf (oracle : Oracle) (message : Message) (key : Key) {input : CheckInput}
    {footer : Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))} {before state : MachineState}
    (decoded : CheckerDecodedInput input footer before) {record remaining : Nat}
    (boundary : CheckerRecordBoundary input (checkerCryptoRecordState before) record remaining state)
    (active : remaining≠0) (values : ∀ item, input.values item=message item.val)
    (proof : input.proof=cachedEncodedPacket
      (referenceHeap oracle (pinnedLeafNodes oracle (deliveredReady oracle message key)))
      (deliveredSalts oracle key) input.positions) :
    (readBuffer (recordPathState oracle input record (754975239+32*record) state) 12288 32).setWidth 238=
      referenceHeap oracle (pinnedLeafNodes oracle (deliveredReady oracle message key))
        (LENGTH+(checkerRecordInputIndex input record).val) := by
  have present : record < input.positions.card := by have := boundary.balance; omega
  have typed := record_path_typed_node oracle decoded boundary active
  dsimp only at typed
  rw [checker_cached_input_nonce input _ _ (delivered_salt_width oracle key) record present proof,
    values,checker_record_value_index] at typed
  exact typed.trans (delivered_reference_leaf oracle message key _).symm

theorem checker_honest_record_raw (oracle : Oracle) (message : Message) (key : Key) {input : CheckInput}
    {footer : Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))} {before state : MachineState}
    (decoded : CheckerDecodedInput input footer before) {record remaining : Nat}
    (boundary : CheckerRecordBoundary input (checkerCryptoRecordState before) record remaining state)
    (active : remaining≠0)
    (proof : input.proof=cachedEncodedPacket
      (referenceHeap oracle (pinnedLeafNodes oracle (deliveredReady oracle message key)))
      (deliveredSalts oracle key) input.positions) :
    BytesAt state (BitVec.ofNat 64 (checkingRawBase+498*record))
      (lowerRecord true (fun node =>
        (referenceHeap oracle (pinnedLeafNodes oracle (deliveredReady oracle message key)) node).setWidth 256)
        (checkerRecordInputIndex input record) (deliveredSalts oracle key (checkerRecordInputIndex input record))) := by
  have present : record < input.positions.card := by have := boundary.balance; omega
  have raw := checker_boundary_raw_memory decoded boundary active
  rw [checker_cached_input_record input _ _ record present proof,
    cached_record_raw_bytes oracle _ _ _ (delivered_salt_width oracle key _),cached_record_source] at raw
  exact raw

theorem record_path_memory (oracle : Oracle) {input : CheckInput} {record : Nat} {base : CheckerRecordBase}
    {src : Nat} {state : MachineState} (ready : CheckerRecordCoreReady input record base src state)
    (word : Nat) (lower : 1600≤word) (room : word<2^33) (outside : word<src ∨ src+26≤word) :
    memoryView (recordPathState oracle input record src state) word=memoryView state word := by
  rw [record_path_state_eq]
  have reached : (recordLeafObservation oracle input record src state).1.1∈
      support (leafQueries (checkerRecordCoreNonceState state) src (checkerRecordInputIndex input record)) := by
    rw [record_leaf_observation_eq]
    exact recorded_evaluation_support oracle _
  generalize equality : (recordLeafObservation oracle input record src state).1.1=after at *
  simp only [leafQueries,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
  obtain ⟨a,_,b,_,rfl⟩ := reached
  have args := checker_record_core_leaf_ready ready
  have digest : (secondReplyState (checkerRecordCoreNonceState state) src a b).getReg .x23=12288 :=
    (checker_leaf_preserved_register _ _ _ _ .x23 (by decide) (by decide) (by decide)).trans args.destination
  rw [checker_leaf_path_eq,trunc_lower_frame _ digest word (by omega) (by omega),
    checker_leaf_frame args a b word room outside (Or.inr (by omega))]
  have nonce := checker_record_core_nonce_buffer ready (8*word) 8 (by omega) (by omega)
  simpa only [TwoPermutationPrototype.Packed.Checker.read_buffer_word] using nonce

theorem checker_honest_path_raw (oracle : Oracle) (message : Message) (key : Key) {input : CheckInput}
    {footer : Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))} {before state : MachineState}
    (decoded : CheckerDecodedInput input footer before) {record remaining : Nat}
    (boundary : CheckerRecordBoundary input (checkerCryptoRecordState before) record remaining state)
    (active : remaining≠0)
    (proof : input.proof=cachedEncodedPacket
      (referenceHeap oracle (pinnedLeafNodes oracle (deliveredReady oracle message key)))
      (deliveredSalts oracle key) input.positions) :
    BytesAt (recordPathState oracle input record (754975239+32*record) state)
      (BitVec.ofNat 64 (checkingRawBase+498*record))
      (lowerRecord true (fun node =>
        (referenceHeap oracle (pinnedLeafNodes oracle (deliveredReady oracle message key)) node).setWidth 256)
        (checkerRecordInputIndex input record) (deliveredSalts oracle key (checkerRecordInputIndex input record))) := by
  obtain ⟨fit,core⟩ := checker_record_boundary_core boundary active
  have raw := checker_honest_record_raw oracle message key decoded boundary active proof
  have high : checkingRawBase+498*LENGTH+528≤2^36 := by decide +kernel
  have above : 8*(754975239+32*LENGTH)≤checkingRawBase := by decide +kernel
  have cardinal := boundary.limit
  have present : record < input.positions.card := by have := boundary.balance; omega
  intro byte inside
  have short : byte<498 := by simpa only [lower_record_length,ite_true] using inside
  have memory := TwoPermutationPrototype.Packed.Checker.byte_eq_of_word_frame state
    (recordPathState oracle input record (754975239+32*record) state) (checkingRawBase+498*record+byte)
    (record_path_memory oracle core _ (by omega) (by omega) (.inr (by omega)))
  have content := raw byte inside
  rw [←BitVec.ofNat_add] at content ⊢
  exact memory.trans content

theorem checker_honest_record_lower (oracle : Oracle) (message : Message) (key : Key) {input : CheckInput}
    {footer : Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))} {before state : MachineState}
    (decoded : CheckerDecodedInput input footer before) {record remaining : Nat}
    (boundary : CheckerRecordBoundary input (checkerCryptoRecordState before) record remaining state)
    (active : remaining≠0) (values : ∀ item, input.values item=message item.val)
    (proof : input.proof=cachedEncodedPacket
      (referenceHeap oracle (pinnedLeafNodes oracle (deliveredReady oracle message key)))
      (deliveredSalts oracle key) input.positions) :
    readBuffer (recordLowerObservation oracle input record (754975239+32*record) state).1.1 12288 32=
      (referenceHeap oracle (pinnedLeafNodes oracle (deliveredReady oracle message key))
        (checkerRecordGroup input record)).setWidth 256 := by
  obtain ⟨fit,core⟩ := checker_record_boundary_core boundary active
  have raw := checker_honest_path_raw oracle message key decoded boundary active proof
  have child := checker_honest_record_leaf oracle message key decoded boundary active values proof
  have start : (readBuffer (recordPathState oracle input record (754975239+32*record) state) 12288 32).setWidth 238=
      referenceHeap oracle (pinnedLeafNodes oracle (deliveredReady oracle message key))
        (lowerNode (checkerRecordInputIndex input record) 0) := by
    simpa only [lowerNode,Nat.pow_zero,Nat.div_one] using child
  have indexNode : ((recordPathState oracle input record (754975239+32*record) state).getReg .x6).toNat=
      lowerNode (checkerRecordInputIndex input record) 0 := by
    simpa only [lowerNode,Nat.pow_zero,Nat.div_one] using record_path_node oracle core
  have recovered := lower_sixteen_recovers_full_heap oracle input _ (record_path_ready oracle core)
    _ (reference_heap_tree oracle _) _ _ raw indexNode start
  have group : lowerNode (checkerRecordInputIndex input record) 16=checkerRecordGroup input record := by
    change (16777216+(checkerRecordInputIndex input record).val)/65536=
      256+(checkerRecordInputIndex input record).val/65536
    omega
  rw [group] at recovered
  exact observed_value_of_append (fun out : MachineState => readBuffer out 12288 32)
    (recordLeafObservation oracle input record (754975239+32*record) state)
    (lowerSixteenObservation oracle (recordPathState oracle input record (754975239+32*record) state))
    (recordLowerObservation oracle input record (754975239+32*record) state) Nat.add
    (record_lower_observation_bind oracle input record (754975239+32*record) state) _ recovered

theorem record_lower_heap_buffer {input : CheckInput} {record source : Nat} {base : CheckerRecordBase}
    {state out : MachineState} (ready : CheckerRecordCoreReady input record base source state)
    (reached : out∈support (checkerRecordLowerTrace input record source state)) (sourceBound : 4096 ≤ source)
    (node : Nat) (bounded : node<512) :
    readBuffer out (16384+32*node) 32=readBuffer state (16384+32*node) 32 := by
  apply read_digest_congr _ _ _ (by omega)
  intro word inside
  have frame := checker_record_lower_memory ready reached (2048+4*node+word) (by omega) (by omega) (.inl (by omega))
  have address : wordAddress (2048+4*node+word)=BitVec.ofNat 64 (16384+32*node+8*word) := by
    unfold wordAddress
    congr 1
    omega
  simpa only [memoryView,address] using frame

theorem group_memory_other_buffer (state : MachineState) (node query : Nat) (bounded : node<512)
    (queryBound : query<512) (apart : query≠node) :
    readBuffer (TwoPermutationPrototype.Checker.groupMemory state node) (16384+32*query) 32=
      readBuffer state (16384+32*query) 32 := by
  apply read_digest_congr _ _ _ (by omega)
  intro word inside
  have frame := TwoPermutationPrototype.Checker.group_memory_other state node (2048+4*query+word)
    bounded (by omega) (by omega) (by omega)
  have address : wordAddress (2048+4*query+word)=BitVec.ofNat 64 (16384+32*query+8*word) := by
    unfold wordAddress
    congr 1
    omega
  simpa only [address] using frame

@[irreducible] def CanonicalMarkedGroups (heap : Nat → Node) (state : MachineState) : Prop :=
  ∀ node, 256≤node → node<512 → memoryView state (512+node)≠0 →
    readBuffer state (16384+32*node) 32=(heap node).setWidth 256

theorem canonical_marked_transport (heap : Nat → Node) (left right : MachineState)
    (memory : left.mem=right.mem) (stored : CanonicalMarkedGroups heap right) : CanonicalMarkedGroups heap left := by
  rw [CanonicalMarkedGroups] at stored ⊢
  intro node low high occupied
  have flag : memoryView left (512+node)=memoryView right (512+node) := congrFun memory _
  rw [flag] at occupied
  exact (read_buffer_memory_congr left right memory _ _).trans (stored node low high occupied)

theorem record_lower_canonical_groups {input : CheckInput} {record source : Nat} {base : CheckerRecordBase}
    {state out : MachineState} (ready : CheckerRecordCoreReady input record base source state)
    (reached : out∈support (checkerRecordLowerTrace input record source state)) (sourceBound : 4096 ≤ source)
    (heap : Nat → Node) (stored : CanonicalMarkedGroups heap state) : CanonicalMarkedGroups heap out := by
  rw [CanonicalMarkedGroups] at stored ⊢
  intro node low high occupied
  rw [checker_record_lower_mark_memory ready reached (512+node) (by omega) (by omega)] at occupied
  exact (record_lower_heap_buffer ready reached sourceBound node high).trans (stored node low high occupied)

theorem group_accepted_canonical (heap : Nat → Node) (state : MachineState) (node : Nat)
    (low : 256≤node) (high : node<512) (stored : CanonicalMarkedGroups heap state)
    (incoming : readBuffer state 12288 32=(heap node).setWidth 256) :
    TwoPermutationPrototype.Checker.GroupAccepted state node := by
  by_cases fresh : memoryView state (512+node)=0
  · exact Or.inl fresh
  · apply Or.inr
    rw [show 8*(2048+4*node)=16384+32*node by omega]
    rw [CanonicalMarkedGroups] at stored
    exact (stored node low high fresh).trans incoming.symm

theorem group_memory_canonical_groups (heap : Nat → Node) (state : MachineState) (node : Nat)
    (low : 256≤node) (high : node<512) (stored : CanonicalMarkedGroups heap state)
    (incoming : readBuffer state 12288 32=(heap node).setWidth 256) :
    CanonicalMarkedGroups heap (TwoPermutationPrototype.Checker.groupMemory state node) := by
  have accepted := group_accepted_canonical heap state node low high stored incoming
  rw [CanonicalMarkedGroups] at stored ⊢
  intro query queryLow queryHigh occupied
  by_cases same : query=node
  · subst query
    rw [show 16384+32*node=8*(2048+4*node) by omega,
      TwoPermutationPrototype.Checker.group_memory_root state node high accepted,incoming]
  · have flag := TwoPermutationPrototype.Checker.group_memory_other state node (512+query)
      high (by omega) (by omega) (.inl (by omega))
    change memoryView (TwoPermutationPrototype.Checker.groupMemory state node) (512+query)=
      memoryView state (512+query) at flag
    rw [flag] at occupied
    exact (group_memory_other_buffer state node query high queryHigh same).trans (stored query queryLow queryHigh occupied)

theorem checker_honest_record_step (oracle : Oracle) (message : Message) (key : Key) {input : CheckInput}
    {footer : Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))} {before state : MachineState}
    (decoded : CheckerDecodedInput input footer before) {record remaining : Nat}
    (boundary : CheckerRecordBoundary input (checkerCryptoRecordState before) record (remaining+1) state)
    (values : ∀ item, input.values item=message item.val)
    (proof : input.proof=cachedEncodedPacket
      (referenceHeap oracle (pinnedLeafNodes oracle (deliveredReady oracle message key)))
      (deliveredSalts oracle key) input.positions)
    (stored : CanonicalMarkedGroups (referenceHeap oracle (pinnedLeafNodes oracle (deliveredReady oracle message key))) state) :
    let after := (recordLowerObservation oracle input record (754975239+32*record) state).1.1
    TwoPermutationPrototype.Checker.GroupAccepted after (checkerRecordGroup input record) ∧
      CanonicalMarkedGroups (referenceHeap oracle (pinnedLeafNodes oracle (deliveredReady oracle message key)))
        (groupRun after (checkerRecordGroup input record)).1 := by
  obtain ⟨fit,core⟩ := checker_record_boundary_core boundary (by omega)
  have reached := recorded_evaluation_support oracle (checkerRecordLowerTrace input record (754975239+32*record) state)
  rw [←record_lower_observation_eq] at reached
  have full := checker_honest_record_lower oracle message key decoded boundary (by omega) values proof
  have kept := record_lower_canonical_groups core reached (by omega) _ stored
  have bounds := checker_record_group_bounds input record
  have accepted := group_accepted_canonical _ _ _ bounds.1 bounds.2 kept full
  refine ⟨accepted,?_⟩
  have cardinal : input.positions.card≤16777216 := boundary.limit
  have ready := checker_record_group_ready core reached remaining boundary.counter
    (by have := boundary.balance; have := boundary.limit; omega) boundary.roots boundary.marks
  apply canonical_marked_transport _ _ _ (group_run_state _ _ remaining ready).memory
  exact group_memory_canonical_groups _ _ _ bounds.1 bounds.2 kept full

attribute [local irreducible] groupRun

theorem honest_record_observer_induction {α : Type}
    (observe : Nat → Nat → α → (α × Bool) × List PublicRow)
    (advance : Nat → α → α) (stepRows : Nat → α → List PublicRow) (okay : Nat → α → Bool)
    (ready : Nat → Nat → α → Prop) (invariant : α → Prop)
    (zero : ∀ record state, observe 0 record state=((state,false),[]))
    (step : ∀ count record state, observe (count+1) record state=
      if okay record state then
        let later := observe count (record+1) (advance record state)
        ((later.1.1,later.1.2),stepRows record state++later.2)
      else ((advance record state,true),stepRows record state))
    (honest : ∀ count record state, ready (count+1) record state → invariant state → okay record state=true)
    (nextReady : ∀ count record state, ready (count+1) record state → okay record state=true →
      ready count (record+1) (advance record state))
    (nextStored : ∀ count record state, ready (count+1) record state → invariant state → okay record state=true →
      invariant (advance record state)) (count : Nat) :
    ∀ record state, ready count record state → invariant state →
      (observe count record state).1.2=false ∧ invariant (observe count record state).1.1 := by
  induction count with
  | zero =>
    intro record state prepared stored
    rw [zero]
    exact ⟨rfl,stored⟩
  | succ count ih =>
    intro record state prepared stored
    have good := honest count record state prepared stored
    rw [step]
    simp only [good,ite_true]
    exact ih (record+1) (advance record state) (nextReady count record state prepared good)
      (nextStored count record state prepared stored good)

theorem canonical_marked_initial (heap : Nat → Node) {input : CheckInput} {reference state : MachineState}
    {remaining : Nat} (boundary : CheckerRecordBoundary input reference 0 remaining state) :
    CanonicalMarkedGroups heap state := by
  rw [CanonicalMarkedGroups]
  intro node low high occupied
  rw [boundary.marked node low high] at occupied
  simp [checkerProcessedGroups] at occupied

theorem checker_honest_prefix (oracle : Oracle) (message : Message) (key : Key) {input : CheckInput}
    {footer : Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))} {before : MachineState}
    (decoded : CheckerDecodedInput input footer before)
    (values : ∀ item, input.values item=message item.val)
    (proof : input.proof=cachedEncodedPacket
      (referenceHeap oracle (pinnedLeafNodes oracle (deliveredReady oracle message key)))
      (deliveredSalts oracle key) input.positions) (count : Nat) :
    ∀ (record remaining : Nat) (state : MachineState),
      CheckerRecordBoundary input (checkerCryptoRecordState before) record remaining state → count≤remaining →
      CanonicalMarkedGroups (referenceHeap oracle (pinnedLeafNodes oracle (deliveredReady oracle message key))) state →
      (recordPrefixObservation oracle input count record state).1.1.rejected=false ∧
      CanonicalMarkedGroups (referenceHeap oracle (pinnedLeafNodes oracle (deliveredReady oracle message key)))
        (recordPrefixObservation oracle input count record state).1.1.state := by
  intro record remaining state boundary enough stored
  have result := honest_record_observer_induction (recordPrefixView oracle input)
    (fun record state => (groupRun (recordLowerObservation oracle input record (754975239+32*record) state).1.1
      (checkerRecordGroup input record)).1)
    (fun record state => (recordLowerObservation oracle input record (754975239+32*record) state).1.2)
    (fun record state => decide (TwoPermutationPrototype.Checker.GroupAccepted
      (recordLowerObservation oracle input record (754975239+32*record) state).1.1 (checkerRecordGroup input record)))
    (fun count record state => ∃ remaining, CheckerRecordBoundary input (checkerCryptoRecordState before) record remaining state ∧ count≤remaining)
    (CanonicalMarkedGroups (referenceHeap oracle (pinnedLeafNodes oracle (deliveredReady oracle message key))))
    (record_prefix_view_zero oracle input) (record_prefix_view_step oracle input)
    (by
      intro count record state prepared stored
      obtain ⟨remaining,boundary,enough⟩ := prepared
      cases remaining with
      | zero => omega
      | succ remaining =>
        have step := checker_honest_record_step oracle message key decoded boundary values proof stored
        simp only [step.1,decide_true])
    (by
      intro count record state prepared good
      obtain ⟨remaining,boundary,enough⟩ := prepared
      cases remaining with
      | zero => omega
      | succ remaining =>
        have reached := recorded_evaluation_support oracle (checkerRecordLowerTrace input record (754975239+32*record) state)
        rw [←record_lower_observation_eq] at reached
        exact ⟨remaining,checker_record_boundary_next boundary reached (of_decide_eq_true good),by omega⟩)
    (by
      intro count record state prepared stored good
      obtain ⟨remaining,boundary,enough⟩ := prepared
      cases remaining with
      | zero => omega
      | succ remaining =>
        exact (checker_honest_record_step oracle message key decoded boundary values proof stored).2)
    count record state ⟨remaining,boundary,enough⟩ stored
  simpa only [recordPrefixView,recordResultProjection] using result

theorem checker_honest_all_records (oracle : Oracle) (message : Message) (key : Key) {input : CheckInput}
    {footer : Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))} {before : MachineState}
    (decoded : CheckerDecodedInput input footer before) (nonempty : input.positions.card≠0)
    (values : ∀ item, input.values item=message item.val)
    (proof : input.proof=cachedEncodedPacket
      (referenceHeap oracle (pinnedLeafNodes oracle (deliveredReady oracle message key)))
      (deliveredSalts oracle key) input.positions) :
    (recordPrefixObservation oracle input input.positions.card 0 (checkerRecordEntryState before)).1.1.rejected=false ∧
      CanonicalMarkedGroups (referenceHeap oracle (pinnedLeafNodes oracle (deliveredReady oracle message key)))
        (recordPrefixObservation oracle input input.positions.card 0 (checkerRecordEntryState before)).1.1.state := by
  have boundary := checker_record_boundary_initial nonempty decoded
  exact checker_honest_prefix oracle message key decoded values proof input.positions.card 0 input.positions.card
    _ boundary (Nat.le_refl _) (canonical_marked_initial _ boundary)

theorem bytes_at_memory (left right : MachineState) (memory : left.mem=right.mem)
    (address : Word) (data : Proof) (raw : BytesAt right address data) : BytesAt left address data := by
  intro byte inside
  simpa only [MachineState.getByte,MachineState.getMem,memory] using raw byte inside

theorem cap_raw_byte_frame (before after : MachineState)
    (frame : ∀ query, OutsideCap query → after.getMem query=before.getMem query)
    (address : Nat) (above : 32768 ≤ address) (room : address < MEMORY_BYTES) :
    after.getByte (BitVec.ofNat 64 address)=before.getByte (BitVec.ofNat 64 address) := by
  have bound : address<2^36 := room
  have numeric : (wordAddress (address/8)).toNat=8*(address/8) := by
    simp only [wordAddress,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : 8*(address/8)<2^64)]
  have outside : OutsideCap (wordAddress (address/8)) := by
    refine ⟨⟨?_,?_,?_⟩,?_⟩
    · rw [numeric]; omega
    · rw [numeric]; omega
    · rw [numeric]; omega
    · rw [numeric]; omega
  exact TwoPermutationPrototype.Packed.Checker.byte_eq_of_word_frame before after address (frame _ outside)

theorem cap_raw_bytes_frame (before after : MachineState)
    (frame : ∀ query, OutsideCap query → after.getMem query=before.getMem query)
    (pointer : Nat) (data : Proof) (above : 32768 ≤ pointer) (room : pointer+data.length ≤ MEMORY_BYTES)
    (raw : BytesAt before (BitVec.ofNat 64 pointer) data) : BytesAt after (BitVec.ofNat 64 pointer) data := by
  intro byte inside
  have content := raw byte inside
  rw [←BitVec.ofNat_add] at content ⊢
  exact (cap_raw_byte_frame before after frame (pointer+byte) (by omega) (by omega)).trans content

@[irreducible] def CapFrontierContents (heap : Nat → Node) (nodes : List Nat) (pointer : Nat)
    (state : MachineState) : Prop :=
  ∀ ordinal, ordinal<nodes.length → BytesAt state (BitVec.ofNat 64 (pointer+30*ordinal))
    (proofDigestBytes true ((heap (nodes.getD ordinal 0)).setWidth 256))

theorem cap_frontier_contents_memory (heap : Nat → Node) (nodes : List Nat) (pointer : Nat)
    (left right : MachineState) (memory : left.mem=right.mem) (raw : CapFrontierContents heap nodes pointer right) :
    CapFrontierContents heap nodes pointer left := by
  rw [CapFrontierContents] at raw ⊢
  intro ordinal inside
  exact bytes_at_memory left right memory _ _ (raw ordinal inside)

theorem cap_frontier_contents_frame (heap : Nat → Node) (nodes : List Nat) (pointer : Nat)
    (before after : MachineState) (frame : ∀ query, OutsideCap query → after.getMem query=before.getMem query)
    (above : 32768 ≤ pointer) (room : pointer+30*nodes.length ≤ MEMORY_BYTES)
    (raw : CapFrontierContents heap nodes pointer before) : CapFrontierContents heap nodes pointer after := by
  rw [CapFrontierContents] at raw ⊢
  intro ordinal inside
  apply cap_raw_bytes_frame before after frame _ _ (by omega) _ (raw ordinal inside)
  simp only [proof_digest_length,ite_true]
  omega

theorem cap_frontier_contents_left (heap : Nat → Node) (left right : List Nat) (pointer : Nat) (state : MachineState)
    (raw : CapFrontierContents heap (left++right) pointer state) : CapFrontierContents heap left pointer state := by
  rw [CapFrontierContents] at raw ⊢
  intro ordinal inside
  have content := raw ordinal (by rw [List.length_append]; omega)
  rw [List.getD_append _ _ _ _ inside] at content
  exact content

theorem cap_frontier_contents_right (heap : Nat → Node) (left right : List Nat) (pointer : Nat) (state : MachineState)
    (raw : CapFrontierContents heap (left++right) pointer state) :
    CapFrontierContents heap right (pointer+30*left.length) state := by
  rw [CapFrontierContents] at raw ⊢
  intro ordinal inside
  have content := raw (left.length+ordinal) (by rw [List.length_append]; omega)
  rw [List.getD_append_right _ _ _ _ (by omega),Nat.add_sub_cancel_left] at content
  have address : pointer+30*(left.length+ordinal)=(pointer+30*left.length)+30*ordinal := by omega
  simpa only [address] using content

attribute [local irreducible] capTreeTrace capLookup capAfterTests capRight

theorem cap_tree_observation_frontier (oracle : Oracle) (groups : List Nat) (height : Nat) (small : height≤8)
    (node : Nat) (state : MachineState) (marked : capIsMarked groups node height=false) :
    capTreeObservation oracle groups height small node state=((frontierRead (capLookup state),[]),0) := by
  rw [cap_tree_observation_eq,(cap_tree_unmarked groups height small node state marked).1,
    record_rows_pure,check_evaluation_pure]

theorem cap_tree_unmarked_canonical (oracle : Oracle) (groups : List Nat) (height finish : Nat)
    (endBound : finish≤MEMORY_BYTES) (small : height≤8) (node pointer : Nat) (state : MachineState)
    (position : TwoPermutationPrototype.Packed.Checker.CapPosition groups state node pointer)
    (span : TwoPermutationPrototype.Opening.CapSpan node height)
    (endReg : state.getReg .x22=BitVec.ofNat 64 finish)
    (room : pointer+30*(capFrontierNodes groups node height).length≤finish)
    (heap : Nat → Node) (raw : CapFrontierContents heap (capFrontierNodes groups node height) pointer state)
    (marked : capIsMarked groups node height=false) :
    readBuffer (capTreeObservation oracle groups height small node state).1.1 (16384+32*node) 32=(heap node).setWidth 256 := by
  have fields : capFrontierNodes groups node height=[node] := by
    cases height <;> simp [capFrontierNodes,marked]
  rw [fields] at room raw
  have space : pointer+30≤finish := by simpa only [List.length_singleton,Nat.mul_one] using room
  obtain ⟨target,next,mem⟩ := cap_lookup_position position span
  have looked : TwoPermutationPrototype.Packed.Checker.CapPosition groups (capLookup state) node pointer := by
    simpa [marked] using next
  have ready : FrontierReady (capLookup state) node pointer :=
    ⟨by simpa [marked] using target,looked.heap,looked.context.controls.roots,looked.proof,
      (TwoPermutationPrototype.Opening.cap_span_node node height span).2,looked.above,looked.even,by omega⟩
  have finishReg : (capLookup state).getReg .x22=BitVec.ofNat 64 finish :=
    ((cap_lookup_stable state) .x22 (by decide)).trans endReg
  have fits := cap_frontier_fits looked finishReg endBound space
  rw [CapFrontierContents] at raw
  have content := raw 0 (by simp)
  simp only [Nat.mul_zero,Nat.add_zero,List.getD_cons_zero] at content
  have copied := cap_frontier_recovers_heap (capLookup state) node pointer ready fits (heap node)
    (bytes_at_memory _ _ mem _ _ content)
  change readBuffer (frontierRead (capLookup state)) (8*(2048+4*node)) 32=_ at copied
  rw [show 8*(2048+4*node)=16384+32*node by omega] at copied
  rw [cap_tree_observation_frontier oracle groups height small node state marked]
  exact copied

theorem cap_tree_canonical (oracle : Oracle) (groups : List Nat) (heap : Nat → Node)
    (tree : ChainedTree oracle heap) (height finish : Nat) (endBound : finish≤MEMORY_BYTES) :
    ∀ (small : height≤8) (node pointer : Nat) (state : MachineState),
    TwoPermutationPrototype.Packed.Checker.CapPosition groups state node pointer →
    TwoPermutationPrototype.Opening.CapSpan node height → state.pc=4096+4*2661 →
    state.getReg .x22=BitVec.ofNat 64 finish →
    pointer+30*(capFrontierNodes groups node height).length≤finish →
    (∀ group, group∈groups → group/2^height=node →
      readBuffer state (16384+32*group) 32=(heap group).setWidth 256) →
    CapFrontierContents heap (capFrontierNodes groups node height) pointer state →
    readBuffer (capTreeObservation oracle groups height small node state).1.1 (16384+32*node) 32=(heap node).setWidth 256 := by
  induction height with
  | zero =>
    intro small node pointer state position span pc endReg room leaves raw
    by_cases marked : capIsMarked groups node 0=true
    · have member : node∈groups := by
        simp only [capIsMarked,List.any_eq_true,beq_iff_eq] at marked
        obtain ⟨group,member,same⟩ := marked
        have index : group=node := by simpa only [Nat.pow_zero,Nat.div_one] using same
        simpa only [index] using member
      rw [cap_tree_observation_leaf oracle groups node state marked]
      exact (read_buffer_memory_congr _ _ (cap_lookup_position position span).2.2 _ _).trans
        (leaves node member (by simp only [Nat.pow_zero,Nat.div_one]))
    · exact cap_tree_unmarked_canonical oracle groups 0 finish endBound small node pointer state
        position span endReg room heap raw (by simpa using marked)
  | succ height ih =>
    intro small node pointer state position span pc endReg room leaves raw
    by_cases marked : capIsMarked groups node (height+1)=true
    · have children := TwoPermutationPrototype.Opening.cap_span_children node height span
      have fields : capFrontierNodes groups node (height+1)=
          capFrontierNodes groups (2*node) height++capFrontierNodes groups (2*node+1) height := by
        simp [capFrontierNodes,marked]
      rw [fields,List.length_append] at room
      rw [fields] at raw
      have bound : 0<node ∧ 2*node<512 := by
        have := (TwoPermutationPrototype.Opening.cap_span_node node (height+1) span).1
        have := TwoPermutationPrototype.Opening.cap_span_is_internal node height span
        omega
      obtain ⟨target,next,mem⟩ := cap_lookup_position position span
      have leftPC : (capLookup state).pc=4096+4*2661 := by simpa [marked] using target
      have leftPos : TwoPermutationPrototype.Packed.Checker.CapPosition groups (capLookup state) (2*node) pointer := by
        simpa [marked] using next
      have leftEnd : (capLookup state).getReg .x22=BitVec.ofNat 64 finish :=
        ((cap_lookup_stable state) .x22 (by decide)).trans endReg
      let left := capTreeObservation oracle groups height (by omega) (2*node) (capLookup state)
      have reachedLeft := cap_tree_observation_support oracle groups height (by omega) (2*node) (capLookup state)
      have leftOk := cap_tree_correct groups height finish endBound (by omega) (2*node) pointer
        (capLookup state) leftPos children.1 leftPC leftEnd (by omega)
      have postLeft := leftOk.post left.1.1 reachedLeft
      have sibling := cap_sibling_position postLeft.2.1 postLeft.1 bound
      have stable := ((cap_lookup_stable state).trans postLeft.2.2.1).trans
        ((cap_tests_stable left.1.1).trans (cap_right_stable (capAfterTests left.1.1)))
      have rightEnd := (stable .x22 (by decide)).trans endReg
      have leftLeaves : ∀ group, group∈groups → group/2^height=2*node →
          readBuffer (capLookup state) (16384+32*group) 32=(heap group).setWidth 256 := by
        intro group member onLeft
        have atParent : group/2^(height+1)=node := by
          rw [Nat.pow_succ,←Nat.div_div_eq_div_mul,onLeft]
          omega
        exact (read_buffer_memory_congr _ _ mem _ _).trans (leaves group member atParent)
      have leftRaw := cap_frontier_contents_memory heap _ pointer (capLookup state) state mem
        (cap_frontier_contents_left heap _ _ pointer state raw)
      have leftValue := ih (by omega) (2*node) pointer (capLookup state) leftPos children.1 leftPC leftEnd
        (by omega) leftLeaves leftRaw
      have rightLeaves : ∀ group, group∈groups → group/2^height=2*node+1 →
          readBuffer (capRight (capAfterTests left.1.1)) (16384+32*group) 32=(heap group).setWidth 256 := by
        intro group member onRight
        have atParent : group/2^(height+1)=node := by
          rw [Nat.pow_succ,←Nat.div_div_eq_div_mul,onRight]
          omega
        have leafBounds := cap_leaf_bounds group (2*node+1) height children.2 onRight
        have startFrame := cap_tree_heap_buffer_frame endBound (by omega) _ left.1.1 leftPos children.1 leftPC leftEnd
          (by omega) reachedLeft group leafBounds.2.1 (.inr leafBounds.2.2.1)
        exact (read_buffer_memory_congr _ _ sibling.2.2 _ _).trans
          (startFrame.trans ((read_buffer_memory_congr _ _ mem _ _).trans (leaves group member atParent)))
      have rightRawAfter := cap_frontier_contents_frame heap _
        (pointer+30*(capFrontierNodes groups (2*node) height).length) state left.1.1
        (fun query outside => (postLeft.2.2.2 query outside).trans (congrFun mem query))
        (by have := position.above; omega) (by omega)
        (cap_frontier_contents_right heap _ _ pointer state raw)
      have rightRaw := cap_frontier_contents_memory heap _ _ (capRight (capAfterTests left.1.1)) left.1.1
        sibling.2.2 rightRawAfter
      let right := capTreeObservation oracle groups height (by omega) (2*node+1) (capRight (capAfterTests left.1.1))
      have reachedRight := cap_tree_observation_support oracle groups height (by omega) (2*node+1)
        (capRight (capAfterTests left.1.1))
      have rightOk := cap_tree_correct groups height finish endBound (by omega) (2*node+1)
        (pointer+30*(capFrontierNodes groups (2*node) height).length) (capRight (capAfterTests left.1.1))
        sibling.2.1 children.2 sibling.1 rightEnd (by omega)
      have postRight := rightOk.post right.1.1 reachedRight
      have rightValue := ih (by omega) (2*node+1) _ (capRight (capAfterTests left.1.1))
        sibling.2.1 children.2 sibling.1 rightEnd (by omega) rightLeaves rightRaw
      have middleFrame := cap_tree_heap_buffer_frame endBound (by omega) _ right.1.1 sibling.2.1 children.2
        sibling.1 rightEnd (by omega) reachedRight (2*node) (by omega) (.inl (by omega))
      have leftFull : readBuffer (capAfterTests right.1.1) (16384+32*(2*node)) 32=(heap (2*node)).setWidth 256 :=
        (read_buffer_memory_congr _ _ (cap_tests_memory right.1.1) _ _).trans
          (middleFrame.trans ((read_buffer_memory_congr _ _ sibling.2.2 _ _).trans leftValue))
      have rightFull : readBuffer (capAfterTests right.1.1) (16384+32*(2*node+1)) 32=(heap (2*node+1)).setWidth 256 :=
        (read_buffer_memory_congr _ _ (cap_tests_memory right.1.1) _ _).trans rightValue
      let parent : Fin 256 := ⟨node,TwoPermutationPrototype.Opening.cap_span_is_internal node height span⟩
      let level : Fin 8 := ⟨height,by omega⟩
      have ascend := cap_ascend_ready level parent span right.1.1 postRight.2.1 postRight.1
      have recovered := cap_loop_recovers_full_heap oracle level parent (cap_range_from_span level parent span)
        (capAfterTests right.1.1) ascend.1 ascend.2.heap ascend.2.context.controls.roots heap tree
        (by change capHeapNode _ (2*node)=_; rw [capHeapNode,leftFull,extended_node_shrink])
        (by change capHeapNode _ (2*node+1)=_; rw [capHeapNode,rightFull,extended_node_shrink])
      rw [cap_tree_observation_branch oracle groups height small node state marked]
      exact recovered
    · exact cap_tree_unmarked_canonical oracle groups (height+1) finish endBound small node pointer state
        position span endReg room heap raw (by simpa using marked)

theorem cap_frontier_node_bounds (groups : List Nat) (node height : Nat)
    (span : TwoPermutationPrototype.Opening.CapSpan node height) (entry : Nat)
    (member : entry∈capFrontierNodes groups node height) : 0<entry ∧ entry<512 := by
  induction height generalizing node with
  | zero =>
    unfold capFrontierNodes at member
    split at member
    · simp at member
    · rw [List.mem_singleton] at member
      subst entry
      exact TwoPermutationPrototype.Opening.cap_span_node _ _ span
  | succ height ih =>
    unfold capFrontierNodes at member
    split at member
    · obtain ⟨left,right⟩ := TwoPermutationPrototype.Opening.cap_span_children node height span
      rcases List.mem_append.mp member with child | child
      · exact ih _ left child
      · exact ih _ right child
    · rw [List.mem_singleton] at member
      subst entry
      exact TwoPermutationPrototype.Opening.cap_span_node _ _ span

theorem proof_nodes_length (heap : Nat → Node) (nodes : List Nat) :
    (nodes.flatMap (fun node => proofDigestBytes true ((heap node).setWidth 256))).length=30*nodes.length := by
  induction nodes with
  | nil => rfl
  | cons node nodes ih =>
    simp only [List.flatMap_cons,List.length_append,proof_digest_length,ite_true,ih,List.length_cons]
    omega

theorem checker_honest_footer_contents (oracle : Oracle) (message : Message) (key : Key) {input : CheckInput}
    {before state : MachineState}
    (decoded : CheckerDecodedInput input (cachedFooter (checkerInputFooterNodes input)
      (referenceHeap oracle (pinnedLeafNodes oracle (deliveredReady oracle message key)))) before)
    (boundary : CheckerRecordBoundary input (checkerCryptoRecordState before) input.positions.card 0 state) :
    CapFrontierContents (referenceHeap oracle (pinnedLeafNodes oracle (deliveredReady oracle message key)))
      (checkerInputFooterNodes input) (checkingRawBase+498*input.positions.card) state := by
  have small : ∀ node∈checkerInputFooterNodes input, node<512 := by
    intro node member
    exact (cap_frontier_node_bounds _ 1 8 TwoPermutationPrototype.Opening.cap_span_root node member).2
  have raw := checker_crypto_record_input_memory input _ before decoded
  rw [cached_footer_raw_bytes oracle _ _ small] at raw
  have ready := checker_decoded_cap_ready decoded boundary
  have endBound : checkingRawBase+498*input.positions.card+30*(checkerInputFooterNodes input).length≤2^36 := ready.endBound
  have above : 8*(754975239+32*LENGTH)≤checkingRawBase := by decide +kernel
  have cardinal := boundary.limit
  rw [CapFrontierContents]
  intro ordinal inside byte short
  have tiny : byte<30 := by simpa only [proof_digest_length,ite_true] using short
  have content := raw (498*input.positions.card+30*ordinal+byte) (by
    rw [List.length_append,checker_input_raw_records_length,proof_nodes_length]
    omega)
  rw [List.getD_append_right _ _ _ _ (by rw [checker_input_raw_records_length]; omega),
    checker_input_raw_records_length,
    show 498*input.positions.card+30*ordinal+byte-498*input.positions.card=30*ordinal+byte by omega,
    uniform_flat_map_byte _ _ 30 (by intro node; simp only [proof_digest_length,ite_true]) ordinal byte inside tiny] at content
  rw [←BitVec.ofNat_add] at content ⊢
  have address : checkingRawBase+(498*input.positions.card+30*ordinal+byte)=
      checkingRawBase+498*input.positions.card+30*ordinal+byte := by omega
  rw [address] at content
  have frame := TwoPermutationPrototype.Packed.Checker.byte_eq_of_word_frame (checkerCryptoRecordState before) state
    (checkingRawBase+498*input.positions.card+30*ordinal+byte)
    (boundary.unread _ (by omega) (by omega) (.inr (by omega)))
  exact frame.trans content

theorem cap_marked_frontier_contents (heap : Nat → Node) (nodes : List Nat) (pointer : Nat)
    (state : MachineState) (base : state.getReg .x26=4096#64) (above : 32768 ≤ pointer)
    (room : pointer+30*nodes.length ≤ MEMORY_BYTES) (raw : CapFrontierContents heap nodes pointer state) :
    CapFrontierContents heap nodes pointer (capMarkedState state) := by
  have bound : pointer+30*nodes.length≤2^36 := room
  rw [CapFrontierContents] at raw ⊢
  intro ordinal inside byte short
  have tiny : byte<30 := by simpa only [proof_digest_length,ite_true] using short
  have content := raw ordinal inside byte short
  rw [←BitVec.ofNat_add] at content ⊢
  have frame := TwoPermutationPrototype.Packed.Checker.byte_eq_of_word_frame state (capMarkedState state)
    (pointer+30*ordinal+byte) (cap_marked_memory_word state base ((pointer+30*ordinal+byte)/8) (by omega) (by omega))
  exact frame.trans content

theorem cap_marked_canonical_root (oracle : Oracle) (heap : Nat → Node) (tree : ChainedTree oracle heap)
    {groups : List Nat} {state : MachineState} {pointer finish : Nat} (ready : CapMarkReady groups state pointer finish)
    (selected : ∀ group, group∈groups → 256≤group ∧ group<512 →
      readBuffer state (16384+32*group) 32=(heap group).setWidth 256)
    (raw : CapFrontierContents heap (capFrontierNodes groups 1 8) pointer state) :
    readBuffer (capDfsObservation oracle groups (capMarkedState state)).1.1 (16384+32*1) 32=(heap 1).setWidth 256 := by
  have marked := cap_mark_ready ready
  have start := cap_start_position marked
  have endReg := (cap_start_register (capMarkedState state) .x22 (by decide) (by decide) (by decide)).trans marked.endReg
  have data := cap_frontier_contents_memory heap _ pointer (capStart (capMarkedState state)) (capMarkedState state)
    start.2.2 (cap_marked_frontier_contents heap _ pointer state ready.markBase ready.above
      (Nat.le_trans ready.room ready.endBound) raw)
  have leaves : ∀ group, group∈groups → group/2^8=1 →
      readBuffer (capStart (capMarkedState state)) (16384+32*group) 32=(heap group).setWidth 256 := by
    intro group member atRoot
    have bounds := cap_leaf_bounds group 1 8 TwoPermutationPrototype.Opening.cap_span_root atRoot
    exact (read_buffer_memory_congr _ _ start.2.2 _ _).trans
      ((cap_marked_heap_buffer state ready.markBase group bounds.2.1).trans (selected group member ⟨bounds.1,bounds.2.1⟩))
  have recovered := cap_tree_canonical oracle groups heap tree 8 finish ready.endBound (by decide) 1 pointer
    (capStart (capMarkedState state)) start.2.1 TwoPermutationPrototype.Opening.cap_span_root start.1 endReg ready.room leaves data
  have correct := cap_tree_correct groups 8 finish ready.endBound (by decide) 1 pointer (capStart (capMarkedState state))
    start.2.1 TwoPermutationPrototype.Opening.cap_span_root start.1 endReg ready.room
  have post := correct.post _ (cap_tree_observation_support oracle groups 8 (by decide) 1 (capStart (capMarkedState state)))
  have root := cap_root_position post.2.1 post.1
  rw [cap_dfs_observation_map]
  exact (read_buffer_memory_congr _ _ root.2.2.2 _ _).trans recovered

theorem checker_honest_cap_root (oracle : Oracle) (message : Message) (key : Key) {input : CheckInput}
    {before state : MachineState}
    (decoded : CheckerDecodedInput input (cachedFooter (checkerInputFooterNodes input)
      (referenceHeap oracle (pinnedLeafNodes oracle (deliveredReady oracle message key)))) before)
    (boundary : CheckerRecordBoundary input (checkerCryptoRecordState before) input.positions.card 0 state)
    (stored : CanonicalMarkedGroups (referenceHeap oracle (pinnedLeafNodes oracle (deliveredReady oracle message key))) state) :
    readBuffer (capDfsObservation oracle ((input.positions.sort (·≤·)).map TwoPermutationPrototype.Sampling.capGroup)
      (capMarkedState state)).1.1 (16384+32*1) 32=
      ((referenceHeap oracle (pinnedLeafNodes oracle (deliveredReady oracle message key))) 1).setWidth 256 := by
  apply cap_marked_canonical_root oracle _ (reference_heap_tree oracle _) (checker_decoded_cap_ready decoded boundary)
  · intro group member bounds
    rw [CanonicalMarkedGroups] at stored
    apply stored group bounds.1 bounds.2
    have flag := boundary.marked group bounds.1 bounds.2
    rw [checker_processed_groups_all,if_pos member] at flag
    rw [flag]
    decide
  · exact checker_honest_footer_contents oracle message key decoded boundary

theorem checker_honest_root_execution (oracle : Oracle) (message : Message) (key : Key) {input : CheckInput}
    {before state : MachineState}
    (decoded : CheckerDecodedInput input (cachedFooter (checkerInputFooterNodes input)
      (referenceHeap oracle (pinnedLeafNodes oracle (deliveredReady oracle message key)))) before)
    (boundary : CheckerRecordBoundary input (checkerCryptoRecordState before) input.positions.card 0 state)
    (stored : CanonicalMarkedGroups (referenceHeap oracle (pinnedLeafNodes oracle (deliveredReady oracle message key))) state)
    (commitment : input.commitment=(Artifact.submission.readCommit (deliveredSeedOutput oracle message key)).1) (fuel : Nat) :
    let cap := capDfsObservation oracle ((input.positions.sort (·≤·)).map TwoPermutationPrototype.Sampling.capGroup) (capMarkedState state)
    ∃ finished : Execution, finished.exit=.success ∧ execute (Artifact.submission.image .check) (16+fuel) cap.1.1 false=pure finished := by
  have reached : (capDfsObservation oracle ((input.positions.sort (·≤·)).map TwoPermutationPrototype.Sampling.capGroup)
      (capMarkedState state)).1.1∈support (capDfsEntryTrace
        ((input.positions.sort (·≤·)).map TwoPermutationPrototype.Sampling.capGroup) (capMarkedState state)) := by
    rw [capDfsObservation]
    exact recorded_evaluation_support oracle _
  have post := checker_decoded_cap_post decoded boundary reached
  have same : TwoPermutationPrototype.Checker.capRootAt
      (capDfsObservation oracle ((input.positions.sort (·≤·)).map TwoPermutationPrototype.Sampling.capGroup) (capMarkedState state)).1.1 1=
      readBuffer (capDfsObservation oracle ((input.positions.sort (·≤·)).map TwoPermutationPrototype.Sampling.capGroup)
        (capMarkedState state)).1.1 (8*536871424) 32 := by
    change readBuffer _ (16384+32*1) 32=_
    rw [checker_honest_cap_root oracle message key decoded boundary stored,cap_boundary_commitment oracle decoded boundary,
      commitment,(delivered_physical_results oracle message key).1]
  obtain ⟨finished,success,calls,done,cycles,run⟩ := execute_root_check _ 536871424 fuel
    post.1 post.2.2.1 post.2.2.2 (by decide)
  refine ⟨finished,success.mpr ⟨post.2.1,same⟩,?_⟩
  rw [checking_manifest_image]
  exact run

theorem checker_honest_cap_finish (oracle : Oracle) (message : Message) (key : Key) {input : CheckInput}
    {before state : MachineState}
    (decoded : CheckerDecodedInput input (cachedFooter (checkerInputFooterNodes input)
      (referenceHeap oracle (pinnedLeafNodes oracle (deliveredReady oracle message key)))) before)
    (boundary : CheckerRecordBoundary input (checkerCryptoRecordState before) input.positions.card 0 state)
    (stored : CanonicalMarkedGroups (referenceHeap oracle (pinnedLeafNodes oracle (deliveredReady oracle message key))) state)
    (commitment : input.commitment=(Artifact.submission.readCommit (deliveredSeedOutput oracle message key)).1) (fuel : Nat) :
    (capFinishObservation oracle input state fuel).1.1.exit=.success := by
  obtain ⟨finished,success,run⟩ := checker_honest_root_execution oracle message key decoded boundary stored commitment fuel
  rw [capFinishObservation,checkerCapFinish,recorded_bind_evaluation]
  have observed : checkEvaluation oracle (recordRows (capDfsEntryTrace
      ((input.positions.sort (·≤·)).map TwoPermutationPrototype.Sampling.capGroup) (capMarkedState state)))=
      capDfsObservation oracle ((input.positions.sort (·≤·)).map TwoPermutationPrototype.Sampling.capGroup) (capMarkedState state) := by
    rw [capDfsObservation]
  rw [observed]
  dsimp only
  simp only [run,pure_bind,record_rows_pure,check_evaluation_pure]
  exact success

theorem checker_honest_decoded_accepts (oracle : Oracle) (message : Message) (key : Key) {input : CheckInput}
    {before : MachineState}
    (decoded : CheckerDecodedInput input (cachedFooter (checkerInputFooterNodes input)
      (referenceHeap oracle (pinnedLeafNodes oracle (deliveredReady oracle message key)))) before)
    (nonempty : input.positions.card≠0) (values : ∀ item, input.values item=message item.val)
    (proof : input.proof=cachedEncodedPacket
      (referenceHeap oracle (pinnedLeafNodes oracle (deliveredReady oracle message key)))
      (deliveredSalts oracle key) input.positions)
    (commitment : input.commitment=(Artifact.submission.readCommit (deliveredSeedOutput oracle message key)).1) (fuel : Nat) :
    (decodedObservation oracle input before fuel).1.1.exit=.success := by
  let records := recordPrefixObservation oracle input input.positions.card 0 (checkerRecordEntryState before)
  have honest := checker_honest_all_records oracle message key decoded nonempty values proof
  have flag : records.1.1.rejected=false := honest.1
  have good := checker_record_prefix_good (checker_record_boundary_initial nonempty decoded) (Nat.le_refl _)
    (record_prefix_observation_support oracle input input.positions.card 0 (checkerRecordEntryState before))
  have boundary : CheckerRecordBoundary input (checkerCryptoRecordState before) input.positions.card 0 records.1.1.state := by
    simpa only [Nat.zero_add,Nat.sub_self] using (good.continuation honest.1).2
  let extra := 3725*input.positions.card-records.1.1.instructions+
    (61246-(2556+capTreeSteps ((input.positions.sort (·≤·)).map TwoPermutationPrototype.Sampling.capGroup) 1 8))+fuel
  have success := checker_honest_cap_finish oracle message key decoded boundary honest.2 commitment extra
  rw [capFinishObservation] at success
  rw [decoded_observation_step]
  change (decodedTailObservation oracle input records.1.1 fuel).1.1.exit=.success
  rw [decodedTailObservation,checkerDecodedTail]
  dsimp only
  simp only [flag,Bool.false_eq_true,ite_false,observed_execution_charge]
  exact success

theorem checker_honest_initial_accepts (oracle : Oracle) (message : Message) (key : Key) (input : CheckInput)
    (nonempty : input.positions.card≠0) (values : ∀ item, input.values item=message item.val)
    (proof : input.proof=cachedEncodedPacket
      (referenceHeap oracle (pinnedLeafNodes oracle (deliveredReady oracle message key)))
      (deliveredSalts oracle key) input.positions)
    (commitment : input.commitment=(Artifact.submission.readCommit (deliveredSeedOutput oracle message key)).1)
    (fuel : Nat) (room : 110987+6112*input.positions.card≤fuel) :
    (checkEvaluation oracle (recordRows (execute (Artifact.submission.image .check) fuel
      (Artifact.submission.initialState .check input) false))).1.1.exit=.success := by
  obtain ⟨before,cycles,ran,bound,decoded⟩ := checker_cached_input_decodes input _ _ nonempty proof
  let extra := fuel-cycles-(2073+3725*input.positions.card+61262)
  rw [show fuel=cycles+(2073+3725*input.positions.card+61262+extra) by dsimp only [extra];omega,
    ran,checker_decoded_execution nonempty decoded extra,observed_execution_charge]
  have success := checker_honest_decoded_accepts oracle message key decoded nonempty values proof commitment extra
  rw [decodedObservation] at success
  exact success

theorem checker_honest_run_accepts (oracle : Oracle) (message : Message) (key : Key) (input : CheckInput)
    (nonempty : input.positions.card≠0) (values : ∀ item, input.values item=message item.val)
    (proof : input.proof=cachedEncodedPacket
      (referenceHeap oracle (pinnedLeafNodes oracle (deliveredReady oracle message key)))
      (deliveredSalts oracle key) input.positions)
    (commitment : input.commitment=(Artifact.submission.readCommit (deliveredSeedOutput oracle message key)).1) :
    (TwoPermutationPrototype.Checker.checkObservation Artifact.submission oracle input).1.1.exit=.success := by
  have valid := cached_packet_capacity
    (referenceHeap oracle (pinnedLeafNodes oracle (deliveredReady oracle message key))) (deliveredSalts oracle key) input.positions
  rw [←proof] at valid
  have run : Artifact.submission.run .check input=execute (Artifact.submission.image .check)
      (Artifact.submission.steps .check) (Artifact.submission.initialState .check input) false := by
    simp [Submission.run,valid]
  rw [TwoPermutationPrototype.Checker.checkObservation,run]
  exact checker_honest_initial_accepts oracle message key input nonempty values proof commitment _ (checker_initial_budgets input).1

theorem checker_honest_check_eval (oracle : Oracle) (message : Message) (key : Key) (input : CheckInput)
    (values : ∀ item, input.values item=message item.val)
    (proof : input.proof=cachedEncodedPacket
      (referenceHeap oracle (pinnedLeafNodes oracle (deliveredReady oracle message key)))
      (deliveredSalts oracle key) input.positions)
    (commitment : input.commitment=(Artifact.submission.readCommit (deliveredSeedOutput oracle message key)).1) :
    (oracle.eval (Artifact.submission.scheme.check input.commitment input.positions input.values input.proof)).1=true := by
  by_cases empty : input.positions.card=0
  · have zero : input.proof.length=0 := by rw [proof,cached_encoded_empty _ _ _ empty];rfl
    rw [checker_empty_input_accepts input empty zero]
    rfl
  · rw [scheme_check_evaluation]
    have erase := TwoPermutationPrototype.Checker.check_record_erase oracle (Artifact.submission.run .check input)
    change ((TwoPermutationPrototype.Checker.checkObservation Artifact.submission oracle input).1.1,
      (TwoPermutationPrototype.Checker.checkObservation Artifact.submission oracle input).2)=_ at erase
    rw [←erase,checker_honest_run_accepts oracle message key input empty values proof commitment]
    rfl

theorem honest_acceptance_event (scheme : Scheme) (oracle : Oracle) (message : Message) (positions : Positions) :
    (fun result : Scheme.HonestResult => result.accepted=true) <$> scheme.honest oracle message positions=
      (fun view : Commitment × Proof =>
        (oracle.eval (scheme.check view.1 positions (message.restrict positions) view.2)).1=true) <$>
        fixedOracleRun oracle (executableTranscript scheme message positions) := by
  simp only [Scheme.honest,executableTranscript,fixed_oracle_run_bind,
    fixed_oracle_run_pure,map_bind,map_pure]
  simp only [fixedOracleRun,bind_map_left]

end Refinement

open Refinement in
theorem delivered_scheme_completeness : Artifact.submission.scheme.Completeness := by
  intro oracle message positions
  rw [honest_acceptance_event,delivered_transcript_fixed]
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro view reached
  simp only [mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
  obtain ⟨key,_,rfl⟩ := reached
  exact checker_honest_check_eval oracle message key
    ⟨(Artifact.submission.readCommit (deliveredSeedOutput oracle message key)).1,positions,message.restrict positions,
      cachedEncodedPacket (referenceHeap oracle (pinnedLeafNodes oracle (deliveredReady oracle message key)))
        (deliveredSalts oracle key) positions⟩ (by intro item;rfl) rfl rfl

theorem delivered_admission : Artifact.submission.Admission := by
  intro program
  cases program <;>
    simp only [Artifact.submission,Image.Valid,Image.byteSize,LayoutValid,dataBase,ArtifactEncoding.length_decode] <;> decide

private theorem delivered_run_support (impl : QueryImpl World (AddWriterT Nat ProbComp))
    {α : Type} (computation : OracleComp World α) (result : α × Multiplicative Nat)
    (reachable : result∈support (simulateQ impl computation).run) : result.1∈support computation := by
  induction computation using OracleComp.inductionOn generalizing result with
  | pure value =>
    simp only [simulateQ_pure,WriterT.run_pure,support_pure,Set.mem_singleton_iff] at reachable
    subst result
    simp
  | query_bind query continuation ih =>
    simp only [simulateQ_bind,simulateQ_spec_query,WriterT.run_bind,
      support_bind,support_map,Set.mem_iUnion,exists_prop,Set.mem_image] at reachable
    obtain ⟨⟨answer,cost⟩,_,⟨value,extra⟩,reached,rfl⟩ := reachable
    exact (mem_support_bind_iff _ _ _).mpr
      ⟨answer,mem_support_query query answer,ih answer (value,extra) reached⟩

theorem delivered_termination : Artifact.submission.Termination := by
  intro oracle program input
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro result reached
  have execution := delivered_run_support (oracle.world.withAddCost Oracle.callCost) _ result reached
  cases program with
  | commit => rw [(artifact_commit_supported input result.1 execution).1]; decide
  | opening => rw [artifact_opening_terminates input.1 input.2 execution]; decide
  | check => exact (RecordTail.checker_run_limits input execution).1

theorem delivered_machine_resources (oracle : Oracle) (message : Message) (positions : Positions)
    (result : MachineResult) (reached : result∈support (fixedOracleRun oracle (Artifact.submission.honestMachine message positions))) :
    result.success=true ∧ (positions.card=BATCH → result.commitCycles≤2353177256 ∧ result.openingCycles≤444579) := by
  have seeded : fixedOracleRun oracle (Artifact.submission.run .commit message)=
      (do let key ← $ᵗ Key; pure (deliveredSeedOutput oracle message key)) := by
    unfold fixedOracleRun
    rw [delivered_counted_run]
    simp only [map_bind,map_pure]
  unfold Submission.honestMachine at reached
  rw [fixed_oracle_run_bind,seeded] at reached
  simp only [bind_assoc,pure_bind,mem_support_bind_iff] at reached
  obtain ⟨key,_,reached⟩ := reached
  obtain ⟨opened,ran,success,_,scored⟩ := artifact_honest_opening_resources oracle message key positions
  rw [fixed_oracle_run_bind,ran,fixed_oracle_run_pure,pure_bind,fixed_oracle_run_pure] at reached
  simp only [support_pure,Set.mem_singleton_iff] at reached
  subst result
  constructor
  · simp only [deliveredSeedOutput,beq_self_eq_true,success,Bool.and_true]
  · intro batch
    exact ⟨Nat.le_refl _,(scored batch).1⟩

private theorem fixed_machine_support (oracle : Oracle) (message : Message) (positions : Positions)
    (result : MachineResult × Nat) (reached : result∈support (oracle.run (Artifact.submission.honestMachine message positions))) :
    result.1∈support (fixedOracleRun oracle (Artifact.submission.honestMachine message positions)) := by
  unfold fixedOracleRun
  rw [support_map]
  exact ⟨result,reached,rfl⟩

theorem delivered_machine_success : Artifact.submission.MachineSuccess := by
  intro oracle message positions
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro result reached
  exact (delivered_machine_resources oracle message positions result.1
    (fixed_machine_support oracle message positions result reached)).1

theorem delivered_prover_cycles : Artifact.submission.ProverCycles 2353177256 444579 := by
  intro oracle message positions batch
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro result reached
  exact (delivered_machine_resources oracle message positions result.1
    (fixed_machine_support oracle message positions result reached)).2 batch

private theorem delivered_check_observation (oracle : Oracle) (input : CheckInput) :
    oracle.eval (Artifact.submission.scheme.check input.commitment input.positions input.values input.proof)=
      let observed := TwoPermutationPrototype.Checker.checkObservation Artifact.submission oracle input
      (observed.1.1.exit==.success,observed.2) := by
  rw [scheme_check_evaluation]
  have erase := TwoPermutationPrototype.Checker.check_record_erase oracle (Artifact.submission.run .check input)
  rw [←erase]
  rfl

theorem delivered_honest_budgets : Artifact.submission.scheme.HonestBudgets := by
  intro oracle message positions
  have committed : oracle.run (Artifact.submission.scheme.commit message)=
      (do let key ← $ᵗ Key; pure (Artifact.submission.readCommit (deliveredSeedOutput oracle message key),102382335)) := by
    change oracle.run (Artifact.submission.readCommit <$> Artifact.submission.run .commit message)=_
    rw [oracle_run_map,delivered_counted_run]
    simp only [map_bind,map_pure]
    rfl
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro result reached
  simp only [Scheme.honest,committed,bind_assoc,pure_bind,mem_support_bind_iff] at reached
  obtain ⟨key,_,reached⟩ := reached
  rw [delivered_opening_reference,oracle_run_pure] at reached
  simp only [support_pure,Set.mem_singleton_iff] at reached
  obtain ⟨opened,rfl,reached⟩ := reached
  subst result
  refine ⟨(by change 102382335≤COMMIT_BUDGET; decide),Nat.zero_le _,?_⟩
  let input : CheckInput := ⟨(Artifact.submission.readCommit (deliveredSeedOutput oracle message key)).1,
    positions,message.restrict positions,
    cachedEncodedPacket (referenceHeap oracle (pinnedLeafNodes oracle (deliveredReady oracle message key)))
      (deliveredSalts oracle key) positions⟩
  change (oracle.eval (Artifact.submission.scheme.check input.commitment input.positions input.values input.proof)).2≤
    CHECK_BUDGET input.positions.card
  rw [delivered_check_observation oracle input]
  exact Refinement.checker_observation_adaptive_budget oracle _

theorem delivered_proof_size : Artifact.submission.scheme.ProofSize 65472 := by
  intro oracle message positions batch
  have event : (fun result : Scheme.HonestResult => result.proofBytes≤65472) <$>
      Artifact.submission.scheme.honest oracle message positions=
      (fun view : Commitment × Proof => view.2.length≤65472) <$>
        fixedOracleRun oracle (executableTranscript Artifact.submission.scheme message positions) := by
    simp only [Scheme.honest,executableTranscript,fixed_oracle_run_bind,fixed_oracle_run_pure,map_bind,map_pure]
    simp only [fixedOracleRun,bind_map_left]
  rw [event,delivered_transcript_fixed]
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro view reached
  simp only [mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
  obtain ⟨key,_,rfl⟩ := reached
  rw [cached_encoded_length]
  exact InteriorCodec.proof_length_bound positions (by change positions.card≤128; rw [batch]; rfl)

theorem delivered_certificate : Certificate Artifact.submission 65472 2353177256 444579 where
  admission := delivered_admission
  machineSuccess := delivered_machine_success
  termination := delivered_termination
  completeness := delivered_scheme_completeness
  honestBudgets := delivered_honest_budgets
  proofSize := delivered_proof_size
  proverCycles := delivered_prover_cycles
  binding := Refinement.delivered_checker_binding
  hidingProperty := delivered_scheme_hiding

end CommitGolfCandidate.Chained.Native
