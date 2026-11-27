import CommitGolfCandidate.R1bOpenFinish
import CommitGolfCandidate.TwoPermutationPackedOpeningABI
import CommitGolfCandidate.TwoPermutationPackedOpeningModel

namespace TwoPermutationPrototype.PackedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp Sampling
open Opening (OpeningLayout trapdoorHeap trapdoorSalt sortedIndex lowerNode proofBase openingNodes groupsBefore)

private def bytesAt (state : MachineState) (address count : Nat) : List Byte :=
  (List.range count).map fun j => state.getByte (BitVec.ofNat 64 (address+j))

private theorem bytes_at_append (state : MachineState) (address left right : Nat) :
    bytesAt state address (left+right) =
      bytesAt state address left ++ bytesAt state (address+left) right := by
  simp [bytesAt, List.range_add, List.map_append, List.map_map, Function.comp_def, Nat.add_assoc]

private theorem bytes_at_serialized (state : MachineState) (address count : Nat)
    (value : BitVec (8*count)) (serialization : readBuffer state address count = value) :
    bytesAt state address count = List.ofFn (fun i : Fin count => value.extractLsb' (8*i.val) 8) := by
  apply List.ext_getElem
  · simp [bytesAt]
  · intro i left right
    have inside : i < count := by simpa [bytesAt] using left
    simp only [bytesAt, List.getElem_map, List.getElem_range, List.getElem_ofFn]
    rw [← serialization, read_buffer_byte state address count i inside]

private theorem bytes_at_chunks {α : Type} (state : MachineState) (address width : Nat) (items : List α)
    (itemBytes : α → List Byte)
    (reads : ∀ j (inside : j < items.length),
      bytesAt state (address+width*j) width = itemBytes items[j]) :
    bytesAt state address (width*items.length) = items.flatMap itemBytes := by
  induction items generalizing address with
  | nil => simp [bytesAt]
  | cons first rest ih =>
    have head := reads 0 (by simp)
    have tail : ∀ j (inside : j < rest.length),
        bytesAt state (address + width + width*j) width = itemBytes rest[j] := by
      intro j inside
      have same := reads (j+1) (by simpa)
      simpa only [List.getElem_cons_succ, Nat.mul_succ, Nat.add_left_comm, Nat.add_comm, Nat.add_assoc] using same
    rw [List.length_cons, Nat.mul_succ, Nat.add_comm (width*rest.length) width, bytes_at_append,
      List.flatMap_cons, ih (address+width) tail]
    simpa using head

private theorem proof_digest_byte (packed : Bool) (digest : BitVec 256) (i : Nat)
    (bound : i < (proofDigestBytes packed digest).length) :
    (proofDigestBytes packed digest)[i] = digest.extractLsb' (8*i) 8 := by
  cases packed <;> simp only [proofDigestBytes, Bool.false_eq_true, ite_false, ite_true,
    digestBytes, List.getElem_ofFn, List.getElem_take]

private theorem lower_record_bytes (s : Submission) (layout : OpeningLayout s)
    (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions) (state : MachineState)
    (ordinal : Nat) (present : ordinal < positions.card)
    (contents : CompletedRecords s trapdoor positions state (ordinal+1)) :
    bytesAt state (recordBase ordinal) 500 =
      Hybrid.record (trapdoorHeap (s := s) trapdoor) (sortedIndex positions ordinal present)
        (trapdoorSalt (s := s) trapdoor (sortedIndex positions ordinal present)) := by
  let initial := s.initialState .opening (trapdoor, positions)
  let index := sortedIndex positions ordinal present
  let hash := trapdoorHeap (s := s) trapdoor
  let salt := trapdoorSalt (s := s) trapdoor index
  obtain ⟨nonce, path⟩ := contents ordinal present (by omega)
  have serialized : readBuffer state (recordBase ordinal) 16 = salt := by
    have copied : readBuffer state (recordBase ordinal) 16 = readBuffer initial (nonceAddress index) 16 := by
      unfold readBuffer
      apply congrArg (BitVec.ofNat 128)
      apply Finset.sum_congr rfl
      intro i hi
      rw [nonce i (Finset.mem_range.mp hi)]
    rw [copied]
    exact Opening.input_nonce s layout trapdoor positions index
  have nonceBytes : bytesAt state (recordBase ordinal) 16 = saltBytes salt :=
    bytes_at_serialized state (recordBase ordinal) 16 salt serialized
  have digest (level : Nat) (live : level < 16) :
      bytesAt state (siblingDestination ordinal level) (siblingWidth level) =
      proofDigestBytes (decide (2 ≤ level)) (hash (lowerNode index level ^^^ 1)) := by
    have source : readBuffer initial (siblingAddress index level) 32 =
        hash (lowerNode index level ^^^ 1) :=
      Opening.input_digest s layout trapdoor positions _ (Opening.lower_swap_bound index level)
    have width : (proofDigestBytes (decide (2 ≤ level)) (hash (lowerNode index level ^^^ 1))).length =
        siblingWidth level := by
      rw [proof_digest_length]
      by_cases first : level < 2 <;> simp [siblingWidth,first,show (2 ≤ level) ↔ ¬level < 2 by omega]
    apply List.ext_getElem
    · simp [bytesAt, width]
    · intro i inside outBound
      have bound : i < siblingWidth level := by simpa [bytesAt] using inside
      have under : i < 32 := by unfold siblingWidth at bound; split at bound <;> omega
      simp only [bytesAt, List.getElem_map, List.getElem_range]
      rw [path level live i bound, ← read_buffer_byte initial (siblingAddress index level) 32 i under, source]
      exact (proof_digest_byte (decide (2 ≤ level)) _ i outBound).symm
  have later : bytesAt state (recordBase ordinal+80) (30*(List.range 14).length) =
      (List.range 14).flatMap (fun j => proofDigestBytes true (hash (lowerNode index (j+2) ^^^ 1))) := by
    apply bytes_at_chunks
    intro j inside
    have bound : j < 14 := by simpa using inside
    rw [List.getElem_range]
    have here := digest (j+2) (by omega)
    simpa [siblingDestination,siblingOffset,siblingWidth,Nat.add_assoc] using here
  change bytesAt state (recordBase ordinal) (16+(32+(32+30*14))) = Hybrid.record hash index salt
  rw [bytes_at_append,nonceBytes,bytes_at_append,bytes_at_append]
  have one := digest 0 (by decide)
  have two := digest 1 (by decide)
  have off₁ : siblingDestination ordinal 0 = recordBase ordinal+16 := rfl
  have off₂ : siblingDestination ordinal 1 = recordBase ordinal+16+32 := by
    simp [siblingDestination,siblingOffset,Nat.add_assoc]
  have off₃ : recordBase ordinal+16+32+32 = recordBase ordinal+80 := by omega
  rw [off₁] at one
  rw [off₂] at two
  rw [show siblingWidth 0=32 by rfl] at one
  rw [show siblingWidth 1=32 by rfl] at two
  rw [one,two,off₃]
  rw [show (14:Nat)=(List.range 14).length by decide,later]
  unfold Hybrid.record
  rw [show List.range 16=0::1::(List.range 14).map (fun j => j+2) by decide,List.flatMap_cons,List.flatMap_cons,List.flatMap_map]
  simp [lowerNode,Function.comp_def]


/-- The decoded ABI output is the exact lower records and canonical cap footer. -/
theorem read_opening_proof (s : Submission) (abi : OpeningABI s)
    (trapdoor : BitVec (8 * s.sizes.trapdoor)) (positions : Positions) (result : Execution)
    (succeeded : result.exit = .success) (physical : RestPhysical s trapdoor positions result.state) :
    s.readProof result = proofFromTrapdoor (s := s) trapdoor positions := by
  have fit : (result.state.getReg .x11).toNat ≤ s.sizes.proof := by
    rw [physical.length]
    exact (proof_fits_every_cardinality positions).trans abi.capacity
  have success : s.openingSucceeded result = true := by
    simp [Submission.openingSucceeded, succeeded, fit]
  simp only [Submission.readProof, success, ite_true, physical.length, abi.toOpeningLayout.proof]
  change bytesAt result.state proofBase (proofLength positions) = _
  rw [proofLength, bytes_at_append, proofFromTrapdoor]
  congr 1
  · have length : (positions.sort (· ≤ ·)).length = positions.card := Finset.length_sort _
    rw [← length]
    apply bytes_at_chunks
    intro j inside
    have present : j < positions.card := by simpa using inside
    have lower : CompletedRecords s trapdoor positions result.state (j+1) := by
      intro prior live earlier
      exact physical.lower prior live (by omega)
    exact lower_record_bytes s abi.toOpeningLayout trapdoor positions result.state j present lower
  · apply bytes_at_chunks
    intro j inside
    have footer := physical.footer j inside
    apply List.ext_getElem
    · simp [bytesAt, proof_digest_length]
    · intro i left right
      have byte : i < 30 := by simpa [bytesAt] using left
      let node := (openingNodes positions)[j]
      let initial := s.initialState .opening (trapdoor, positions)
      let source := Opening.capDigestAddress node
      have nodeBound : node < 512 := by
        have nonempty : positions.card ≠ 0 := by intro empty; simp [openingNodes, empty] at inside
        apply Opening.cap_frontier_nodes_small (groupsBefore positions positions.card) 1 8 Opening.cap_span_root
        have member : node ∈ openingNodes positions := List.getElem_mem inside
        simpa [openingNodes, nonempty] using member
      have whole : readBuffer initial source 32 = trapdoorHeap (s := s) trapdoor node := by
        exact Opening.input_digest s abi.toOpeningLayout trapdoor positions node
          (nodeBound.trans_le (by decide : 512 ≤ 2*LENGTH))
      have slice : readBuffer initial source 30 =
          (trapdoorHeap (s := s) trapdoor node).extractLsb' 0 240 := by
        have low := read_buffer_slice initial source 32 0 30 (by decide)
        simpa only [whole, Nat.add_zero, Nat.mul_zero] using low.symm
      simp only [bytesAt, List.getElem_map, List.getElem_range]
      change result.state.getByte (BitVec.ofNat 64 (recordBase positions.card+30*j+i)) = _
      have footerValue : readBuffer result.state (recordBase positions.card+30*j) 30 =
          (trapdoorHeap (s := s) trapdoor node).extractLsb' 0 240 := footer
      rw [← read_buffer_byte result.state _ 30 i byte, footerValue, ← slice, read_buffer_byte initial source 30 i byte]
      rw [← read_buffer_byte initial source 32 i (by omega), whole]
      simp only [proofDigestBytes, ite_true, List.getElem_take, digestBytes, List.getElem_ofFn]
      rfl

structure WireResult (s : Submission) (trapdoor : BitVec (8*s.sizes.trapdoor)) (ps : Positions) (result : Execution) : Prop where
  exit : result.exit=.success
  success : s.openingSucceeded result=true
  bytes : s.readProof result=Hybrid.wireProof ps (proofFromTrapdoor (s:=s) trapdoor ps)
  scored : ps.card=BATCH → result.cycles≤80959 ∧ (s.readProof result).length≤67489
  calls : result.oracleCalls=0

theorem opening_physical_empty (s : Submission) (abi : OpeningABI s)
    (trapdoor : BitVec (8*s.sizes.trapdoor)) (ps : Positions) (empty : ps.card = 0) :
    ∃ result : Execution,s.run .opening (trapdoor,ps)=pure result ∧ WireResult s trapdoor ps result := by
  obtain ⟨pre,wide⟩:=wide_prefix_empty s abi trapdoor ps empty
  let xs:=proofFromTrapdoor (s:=s) trapdoor ps
  let virtual : Execution:=⟨.success,pre,scheduledCycles ps,0⟩
  have physical : OpenPhysical s trapdoor ps virtual :=wide.bytes
  have raw : s.readProof virtual=xs :=read_opening_proof s abi trapdoor ps _ physical.success
    ⟨physical.length, physical.lower, physical.footer⟩
  have good:=opening_success s abi trapdoor ps virtual physical
  have count : pre.getReg .x16=R1b.Machine.W ps.card := wide.run.count
  have card : ps.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ ps
  have len : xs.length=proofLength ps := by
    rw [←raw,Submission.readProof,if_pos good,List.length_map,List.length_range];exact physical.length
  have wid : (pre.getReg .x11).toNat=xs.length:=physical.length.trans len.symm
  have bytes (i : Nat) (inside : i < xs.length) :
      R1b.Machine.byte pre (R1b.Machine.proofBase+i)=R1b.Carry.read xs i := by
    rw [←raw,Submission.readProof,if_pos good,R1b.Carry.read_range _ _ _ (by change _<(pre.getReg .x11).toNat;omega)]
    rw [abi.proof];rfl
  have fits := (proof_fits_every_cardinality ps).trans abi.capacity
  have lb : xs.length<2^64 := by
    rw [len];have:=proof_fits_every_cardinality ps;unfold capacity recordBytes LENGTH LOG_LENGTH at this;omega
  have lreg : pre.getReg .x11=R1b.Machine.W xs.length := by rw [←wid];simp [R1b.Machine.W,BitVec.ofNat_toNat]
  have max (batch : ps.card=128) : xs.length≤67840 := by rw [len];exact (scheduled_scored_limits ps batch).2
  obtain ⟨t,done⟩:=R1b.Opening.finish ps xs pre wide.atCodec count (by change _≤16777216 at card;omega) lreg lb
    wide.proofPtr (fun i h=>by
      by_cases inside : i < xs.length
      · exact bytes i inside
      · have small : i<67840:=h.resolve_left inside
        have z:=wide.padding (Opening.proofBase+i) (by omega) (by change 12616474720+i<68719476736;omega)
        rw [R1b.Carry.read,List.getElem?_eq_none (Nat.le_of_not_gt inside),Option.getD_none]
        exact z) max
  let wire:=Hybrid.wireProof ps xs
  let result : Execution:=⟨.success,t,scheduledCycles ps+R1b.Opening.extra ps.card xs.length,0⟩
  have wireFit : wire.length ≤ s.sizes.proof := by
    by_cases batch : ps.card=BATCH
    · exact (Hybrid.wireBound ps xs batch).trans ((by decide : 67489 ≤ capacity).trans abi.capacity)
    · simpa [wire,Hybrid.wireProof,batch,len] using fits
  have wire64 : wire.length<2^64 := by
    by_cases batch : ps.card=BATCH
    · have b:=Hybrid.wireBound ps xs batch;dsimp [wire];omega
    · simpa [wire,Hybrid.wireProof,batch] using lb
  have actualLen : (t.getReg .x11).toNat=wire.length := by rw [done.len,BitVec.toNat_ofNat,Nat.mod_eq_of_lt wire64]
  have success : s.openingSucceeded result=true := by simp [Submission.openingSucceeded,result,actualLen,wireFit]
  have serialized : s.readProof result=wire := by
    rw [Submission.readProof,if_pos success]
    apply List.ext_getElem
    · simpa [result] using actualLen
    · intro i _ inside
      rw [List.getElem_map,List.getElem_range,abi.proof]
      have out : R1b.Machine.byte t (R1b.Machine.proofBase+i)=R1b.Carry.read wire i := done.bytes i inside
      rw [R1b.Carry.read,List.getElem?_eq_getElem inside] at out
      exact out
  refine ⟨result,?_,⟨rfl,success,serialized,?_,rfl⟩⟩
  · let steps:=R1b.Opening.tailSteps ps.card xs.length
    have small : steps≤11192 := by dsimp [steps,R1b.Opening.tailSteps];split_ifs <;> decide
    have enough : scheduledCycles ps-3+steps ≤ s.steps .opening := by
      apply Nat.le_trans _ abi.fuel
      have b:=opening_cap_cycles_bound (Opening.groupsBefore ps ps.card)
      change ps.card≤16777216 at card
      unfold scheduledCycles;split <;> omega
    let spare:=s.steps .opening-(scheduledCycles ps-3+steps)
    have total : s.steps .opening=scheduledCycles ps-3+(steps+spare) := by dsimp only [spare];omega
    change execute (s.image .opening) (s.steps .opening) _ true=_
    rw [abi.image,total,wide.run]
    have final:=done.run spare true
    change execute (Artifact.submission.image .opening) (steps+spare) pre true=_ at final
    rw [delivered_opening_image] at final
    rw [final]
    have enough : 3 ≤ scheduledCycles ps := by unfold scheduledCycles;split <;> omega
    simp [Execution.charge,result,Nat.add_assoc] <;> omega
  · intro batch;rw [serialized]
    have hi:=(scheduled_scored_limits ps batch).1
    refine ⟨?_,Hybrid.wireBound ps xs batch⟩
    change scheduledCycles ps+R1b.Opening.extra ps.card xs.length≤80959
    unfold R1b.Opening.extra;split_ifs <;> omega

/-- R1b's tail (records, cap, root exit, codec) from the first record boundary, run in `restSteps`. -/
def restSteps (ps : Positions) (len : Nat) : Nat := restCycles ps+R1b.Opening.tailSteps ps.card len

def restCost (ps : Positions) (len : Nat) : Nat := restCycles ps+(3+R1b.Opening.extra ps.card len)

structure RestWire (s : Submission) (trapdoor : BitVec (8*s.sizes.trapdoor)) (ps : Positions) (final : MachineState) :
    Prop where
  proof : ∀ c k, s.readProof ⟨.success,final,c,k⟩=Hybrid.wireProof ps (proofFromTrapdoor (s:=s) trapdoor ps)
  succeeded : ∀ c k, s.openingSucceeded ⟨.success,final,c,k⟩=true

/-- **From the paired pre-pass to HALT.** Any state at word 13 with the record cursor's registers, untouched
input words (for `trapdoor`), empty marks, zero bytes past the proof buffer and the count in x16 runs R1b's
records, cap, root exit and long-batch codec, and leaves the wire form of `proofFromTrapdoor trapdoor`. -/
theorem opening_rest_run (records : RecordsExecute) (s : Submission) (abi : OpeningABI s)
    (trapdoor : BitVec (8*s.sizes.trapdoor)) (ps : Positions) (positive : 0 < ps.card)
    (begin : MachineState) (ready : RecordBoundary s trapdoor ps begin 0)
    (marks : Opening.RecordMarks ps begin 0)
    (pad : ∀ a, Opening.proofBase ≤ a → a < MEMORY_BYTES → begin.getByte (BitVec.ofNat 64 a) = 0)
    (count0 : begin.getReg .x16 = R1b.Machine.W ps.card) :
    ∃ final : MachineState,
      (∀ surplus coins, execute openingImage
          (restSteps ps (proofFromTrapdoor (s:=s) trapdoor ps).length+surplus) begin coins =
        pure ⟨.success,final,restCost ps (proofFromTrapdoor (s:=s) trapdoor ps).length,0⟩) ∧
      RestWire s trapdoor ps final := by
  obtain ⟨pre,wide⟩:=wide_prefix_from records s abi trapdoor ps positive begin ready marks pad
  let xs:=proofFromTrapdoor (s:=s) trapdoor ps
  let virtual : Execution:=⟨.success,pre,0,0⟩
  have raw : s.readProof virtual=xs :=read_opening_proof s abi trapdoor ps virtual rfl wide.bytes
  have fits0 : (pre.getReg .x11).toNat ≤ s.sizes.proof := by
    rw [wide.bytes.length];exact (proof_fits_every_cardinality ps).trans abi.capacity
  have good : s.openingSucceeded virtual=true := by simp [Submission.openingSucceeded,virtual,fits0]
  have count : pre.getReg .x16=R1b.Machine.W ps.card := (RunsOpeningBlock.count wide.run).trans count0
  have card : ps.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ ps
  have len : xs.length=proofLength ps := by
    rw [←raw,Submission.readProof,if_pos good,List.length_map,List.length_range];exact wide.bytes.length
  have wid : (pre.getReg .x11).toNat=xs.length:=wide.bytes.length.trans len.symm
  have bytes (i : Nat) (inside : i < xs.length) :
      R1b.Machine.byte pre (R1b.Machine.proofBase+i)=R1b.Carry.read xs i := by
    rw [←raw,Submission.readProof,if_pos good,R1b.Carry.read_range _ _ _ (by change _<(pre.getReg .x11).toNat;omega)]
    rw [abi.proof];rfl
  have fits := (proof_fits_every_cardinality ps).trans abi.capacity
  have lb : xs.length<2^64 := by
    rw [len];have:=proof_fits_every_cardinality ps;unfold capacity recordBytes LENGTH LOG_LENGTH at this;omega
  have lreg : pre.getReg .x11=R1b.Machine.W xs.length := by rw [←wid];simp [R1b.Machine.W,BitVec.ofNat_toNat]
  have max (batch : ps.card=128) : xs.length≤67840 := by rw [len];exact (scheduled_scored_limits ps batch).2
  obtain ⟨t,done⟩:=R1b.Opening.finish ps xs pre wide.atCodec count (by change _≤16777216 at card;omega) lreg lb
    wide.proofPtr (fun i h=>by
      by_cases inside : i < xs.length
      · exact bytes i inside
      · have small : i<67840:=h.resolve_left inside
        have z:=wide.padding (Opening.proofBase+i) (by omega) (by change 12616474720+i<68719476736;omega)
        rw [R1b.Carry.read,List.getElem?_eq_none (Nat.le_of_not_gt inside),Option.getD_none]
        exact z) max
  let wire:=Hybrid.wireProof ps xs
  let result : Execution:=⟨.success,t,0,0⟩
  have wireFit : wire.length ≤ s.sizes.proof := by
    by_cases batch : ps.card=BATCH
    · exact (Hybrid.wireBound ps xs batch).trans ((by decide : 67489 ≤ capacity).trans abi.capacity)
    · simpa [wire,Hybrid.wireProof,batch,len] using fits
  have wire64 : wire.length<2^64 := by
    by_cases batch : ps.card=BATCH
    · have b:=Hybrid.wireBound ps xs batch;dsimp [wire];omega
    · simpa [wire,Hybrid.wireProof,batch] using lb
  have actualLen : (t.getReg .x11).toNat=wire.length := by rw [done.len,BitVec.toNat_ofNat,Nat.mod_eq_of_lt wire64]
  have success : s.openingSucceeded result=true := by simp [Submission.openingSucceeded,result,actualLen,wireFit]
  have serialized : s.readProof result=wire := by
    rw [Submission.readProof,if_pos success]
    apply List.ext_getElem
    · simpa [result] using actualLen
    · intro i _ inside
      rw [List.getElem_map,List.getElem_range,abi.proof]
      have out : R1b.Machine.byte t (R1b.Machine.proofBase+i)=R1b.Carry.read wire i := done.bytes i inside
      rw [R1b.Carry.read,List.getElem?_eq_getElem inside] at out
      exact out
  refine ⟨t,?_,⟨fun c k=>serialized,fun c k=>success⟩⟩
  intro surplus coins
  have final:=done.run surplus coins
  change execute (Artifact.submission.image .opening) (R1b.Opening.tailSteps ps.card xs.length+surplus) pre coins=_ at final
  rw [delivered_opening_image] at final
  have eqSteps : restSteps ps xs.length+surplus=restCycles ps+(R1b.Opening.tailSteps ps.card xs.length+surplus) := by
    unfold restSteps;omega
  show execute openingImage (restSteps ps xs.length+surplus) begin coins=pure ⟨.success,t,restCost ps xs.length,0⟩
  rw [eqSteps,wide.run,final]
  simp [Execution.charge,restCost,Nat.add_assoc,Nat.add_comm]

end TwoPermutationPrototype.PackedOpening
