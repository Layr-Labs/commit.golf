import CommitGolfCandidate.GroupOpenRecordsAPI
import CommitGolfCandidate.GroupOpenModel
import CommitGolfCandidate.K3OpenCapBytes
import CommitGolfCandidate.GroupOpenSiblingRun

/-! # One T238 opening record, byte for byte (S9-L21)

A record the writer has completed (`CompletedRecords`: the nonce and mate bytes, the plain sibling bytes, and the
folded halfwords of levels 6..12) reads back as `physicalRecord`: salt 16 | mates 96 | levels 0, 1 (32 bytes each) |
levels 2..5 (30 bytes each) | the packed block `foldPack8` of levels 6..13 (seven 30-byte slots of 28 plain bytes and
a folded halfword, then 28 bytes of level 13). -/
namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp Sampling
open Opening (trapdoorHeap sortedIndex)
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000

private theorem rb_serialized (state : MachineState) (address count : Nat)
    (value : BitVec (8*count)) (serialization : readBuffer state address count = value) :
    bytesAt state address count = List.ofFn (fun i : Fin count => value.extractLsb' (8*i.val) 8) := by
  apply List.ext_getElem
  · simp [bytesAt]
  · intro i left right
    have inside : i < count := by simpa [bytesAt] using left
    simp only [bytesAt, List.getElem_map, List.getElem_range, List.getElem_ofFn]
    rw [← serialization, read_buffer_byte state address count i inside]

private theorem rb_chunks {α : Type} (state : MachineState) (address width : Nat) (items : List α)
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

private theorem byte_of_byte (v : BitVec 256) (i : Nat) (small : i < 2) :
    (v.extractLsb' 224 16).extractLsb' (8*i) 8 = v.extractLsb' (8*(28+i)) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  have a : 8*i+j < 16 := by omega
  have b : 224+(8*i+j) = 8*(28+i)+j := by omega
  simp [hj, a, b]

/-- The halfword at byte 28 of a 32-byte digest is the digest's bits 224..239. -/
private theorem half_of_digest (initial : MachineState) (address : Nat) (value : BitVec 256)
    (aligned : address % 2 = 0) (fit : address+48 ≤ 2^64) (whole : readBuffer initial address 32 = value) :
    initial.getHalfword (BitVec.ofNat 64 (address+28)) = value.extractLsb' 224 16 := by
  have hb := halfword_bytes initial (address+28) (by omega) (by omega)
  apply half_ext
  · rw [hb.1, ← read_buffer_byte initial address 32 28 (by decide), whole]
    exact (byte_of_byte value 0 (by decide)).symm
  · rw [hb.2, show address+28+1 = address+(28+1) by omega, ← read_buffer_byte initial address 32 (28+1) (by decide),
      whole]
    exact (byte_of_byte value 1 (by decide)).symm

/-- Bytes of a heap copy: the first `count` bytes of a 32-byte digest copied byte by byte. -/
private theorem copied_bytes (state initial : MachineState) (dest source count : Nat) (value : BitVec 256)
    (small : count ≤ 32) (whole : readBuffer initial source 32 = value)
    (copied : ∀ byte < count,
      state.getByte (BitVec.ofNat 64 (dest+byte)) = initial.getByte (BitVec.ofNat 64 (source+byte))) :
    bytesAt state dest count = (digestBytes value).take count := by
  apply List.ext_getElem
  · simp [bytesAt, digestBytes, small]
  · intro i left right
    have bound : i < count := by simpa [bytesAt] using left
    simp only [bytesAt, List.getElem_map, List.getElem_range, List.getElem_take, digestBytes, List.getElem_ofFn]
    rw [copied i bound, ← read_buffer_byte initial source 32 i (by omega), whole]

theorem record_bytes (s : Submission) (layout : OpeningLayout s)
    (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions) (state : MachineState)
    (ordinal : Nat) (present : ordinal < positions.card)
    (contents : CompletedRecords s trapdoor positions state (ordinal+1)) :
    bytesAt state (recordBase ordinal) 534 =
      physicalRecord (trapdoorLeaf (s:=s) trapdoor) (Opening.trapdoorHeap (s:=s) trapdoor)
        (trapdoorQuad (s:=s) trapdoor (sortedIndex positions ordinal present)) (sortedIndex positions ordinal present)
        (trapdoorSalt (s:=s) trapdoor (sortedIndex positions ordinal present)) := by
  let initial := s.initialState .opening (trapdoor, positions)
  let index := sortedIndex positions ordinal present
  let leaf := trapdoorLeaf (s:=s) trapdoor
  let hash := trapdoorHeap (s := s) trapdoor
  let salt := trapdoorSalt (s := s) trapdoor index
  let quad := trapdoorQuad (s := s) trapdoor index
  obtain ⟨nonce, path, folds⟩ := contents ordinal present (by omega)
  have serialized : readBuffer state (recordBase ordinal) 16 = salt := by
    have copied : readBuffer state (recordBase ordinal) 16 = readBuffer initial (nonceAddress index) 16 := by
      unfold readBuffer
      apply congrArg (BitVec.ofNat 128)
      apply Finset.sum_congr rfl
      intro i hi
      have hb := Finset.mem_range.mp hi
      have value := nonce i (by omega)
      simp only [firstSource,ite_eq_left hb] at value
      rw [value]
    rw [copied]
    exact input_nonce s layout trapdoor positions index
  have nonceBytes : bytesAt state (recordBase ordinal) 16 = saltBytes salt :=
    rb_serialized state (recordBase ordinal) 16 salt serialized
  have source (level : Nat) : readBuffer initial (siblingAddress index level) 32 =
      (if level = 0 then quad else hash (upperNode index level ^^^ 1)) := by
    by_cases zero : level = 0
    · subst zero
      rw [if_pos rfl]
      unfold siblingAddress; rw [if_pos rfl]
      exact input_quad s layout trapdoor positions _ index.isLt
    · rw [if_neg zero, sibling_address_upper index level zero]
      exact input_digest s layout trapdoor positions _ (upper_swap_bound index level)
  have upper (level : Nat) (nz : level ≠ 0) :
      (if level = 0 then quad else hash (upperNode index level ^^^ 1)) = hash (upperNode index level ^^^ 1) := by
    rw [if_neg nz]
  have sourceAligned (level : Nat) : siblingAddress index level % 2 = 0 := by
    have := (sibling_address_inside index level).1
    omega
  have sourceFit (level : Nat) : siblingAddress index level+48 ≤ 2^64 := by
    have bound := (sibling_address_inside index level).2.2
    have base : nonceBase < 2^40 := by decide
    omega
  -- levels 0..5: whole 32-byte (levels 0, 1) or 30-byte (levels 2..5) copies
  have digest (level : Nat) (live : level < 6) :
      bytesAt state (siblingDestination ordinal level) (siblingWidth level) =
      proofDigestBytes (decide (2 ≤ level)) (if level = 0 then quad else hash (upperNode index level ^^^ 1)) := by
    have plain : plainWidth level = siblingWidth level := by
      unfold plainWidth folded
      rw [if_neg (by omega)]
    have width : siblingWidth level ≤ 32 := sibling_width_le level
    have copied := copied_bytes state initial (siblingDestination ordinal level) (siblingAddress index level)
      (siblingWidth level) _ width (source level)
      (fun byte inside => path level (by omega) byte (by rw [plain]; exact inside))
    rw [copied]
    by_cases low : level < 2
    · have w : siblingWidth level = 32 := by unfold siblingWidth; rw [if_pos low]
      rw [w, List.take_of_length_le (by simp [digestBytes])]
      simp [proofDigestBytes, show ¬ 2 ≤ level by omega]
    · have w : siblingWidth level = 30 := by unfold siblingWidth; rw [if_neg low, if_pos (by omega)]
      rw [w]
      simp [proofDigestBytes, show 2 ≤ level by omega]
  -- levels 6..13: the folded block
  have plainCopy (level : Nat) (live : level < 14) (late : 6 ≤ level) :
      bytesAt state (siblingDestination ordinal level) 28 = (digestBytes (hash (upperNode index level ^^^ 1))).take 28 := by
    have plain : plainWidth level = 28 := by
      unfold plainWidth folded siblingWidth
      by_cases f : level < 13
      · rw [if_pos ⟨late, f⟩]
      · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    rw [← upper level (by omega)]
    exact copied_bytes state initial (siblingDestination ordinal level) (siblingAddress index level) 28 _
      (by decide) (source level) (fun byte inside => path level live byte (by rw [plain]; exact inside))
  let block := fun k => hash (upperNode index (6+k) ^^^ 1)
  have foldPair (k : Nat) (small : k < 7) :
      bytesAt state (siblingDestination ordinal (6+k)+28) 2 =
        [(foldHalf (block k) (block 7) k).extractLsb' 0 8, (foldHalf (block k) (block 7) k).extractLsb' 8 8] := by
    have halfK := half_of_digest initial (siblingAddress index (6+k)) _ (sourceAligned (6+k))
      (sourceFit (6+k)) ((source (6+k)).trans (upper (6+k) (by omega)))
    have half13 := half_of_digest initial (siblingAddress index 13) _ (sourceAligned 13)
      (sourceFit 13) ((source 13).trans (upper 13 (by omega)))
    have value : foldValue (initial.getHalfword (BitVec.ofNat 64 (siblingAddress index (6+k)+28)))
        ((initial.getHalfword (BitVec.ofNat 64 (siblingAddress index 13+28))).zeroExtend 64 >>> (2*k)) =
        foldHalf (block k) (block 7) k := by
      rw [halfK, half13]
      unfold foldValue foldHalf
      rw [fold_half_bytes]
    have byte (b : Nat) (two : b < 2) :
        state.getByte (BitVec.ofNat 64 (siblingDestination ordinal (6+k)+28+b)) =
          (foldHalf (block k) (block 7) k).extractLsb' (8*b) 8 := by
      rw [folds k small b two]
      exact congrArg (fun h : BitVec 16 => h.extractLsb' (8*b) 8) value
    apply List.ext_getElem
    · simp [bytesAt]
    · intro i left right
      have bound : i < 2 := by simpa [bytesAt] using left
      simp only [bytesAt, List.getElem_map, List.getElem_range]
      rw [byte i bound]
      interval_cases i <;> rfl
  have slot (k : Nat) (small : k < 7) :
      bytesAt state (siblingDestination ordinal (6+k)) 30 = foldSlot (block k) (block 7) k := by
    rw [show (30:Nat) = 28+2 from rfl, bytes_at_append, plainCopy (6+k) (by omega) (by omega), foldPair k small]
    rfl
  have slotAt (k : Nat) (small : k < 8) : siblingDestination ordinal (6+k) = recordBase ordinal+296+30*k := by
    unfold siblingDestination siblingOffset
    rw [if_neg (by omega), if_pos (by omega)]
    omega
  have folded : bytesAt state (recordBase ordinal+296) 238 = foldPack8 block := by
    rw [show (238:Nat) = 30*(List.range 7).length+28 by decide, bytes_at_append]
    unfold foldPack8
    congr 1
    · apply rb_chunks
      intro j inside
      have small : j < 7 := by simpa using inside
      rw [List.getElem_range, ← slotAt j (by omega)]
      exact slot j small
    · have last := plainCopy 13 (by decide) (by decide)
      rw [show siblingDestination ordinal 13 = recordBase ordinal+296+30*7 from by
        unfold siblingDestination siblingOffset; rw [if_neg (by decide), if_pos (by decide)]; try omega] at last
      simpa [block] using last
  have quartetBytes (j : Fin 3) :
      bytesAt state (recordBase ordinal+16+32*j.val) 32 = digestBytes (leaf (index.val ^^^ (j.val+1))) := by
    apply rb_serialized
    have copied : readBuffer state (recordBase ordinal+16+32*j.val) 32 =
        readBuffer initial (leafAddress (index.val ^^^ (j.val+1))) 32 := by
      unfold readBuffer
      apply congrArg (BitVec.ofNat 256)
      apply Finset.sum_congr rfl
      intro b hb
      have inside : b<32 := Finset.mem_range.mp hb
      have here := nonce (16+32*j.val+b) (by have := j.isLt; omega)
      rw [source_quartet index j b inside] at here
      have whereAt : state.getByte (BitVec.ofNat 64 (recordBase ordinal+16+32*j.val+b)) =
          initial.getByte (BitVec.ofNat 64 (leafAddress (index.val ^^^ (j.val+1))+b)) := by
        simpa only [Nat.add_assoc] using here
      rw [whereAt]
    rw [copied]
    exact input_leaf s layout trapdoor positions _ (sibling_in_message index j)
  have quartet : bytesAt state (recordBase ordinal+16) 96 =
        ([1,2,3] : List Nat).flatMap (fun j => digestBytes (leaf (index.val ^^^ j))) := by
    rw [show ([1,2,3] : List Nat) = (List.range 3).map (fun j => j+1) by decide,List.flatMap_map]
    change bytesAt state (recordBase ordinal+16) (32*(List.range 3).length) = _
    apply rb_chunks
    intro j inside
    rw [List.getElem_range]
    exact quartetBytes ⟨j,by simpa using inside⟩
  have at01 (l : Nat) (small : l < 2) : siblingDestination ordinal l = recordBase ordinal+112+32*l := by
    unfold siblingDestination siblingOffset
    rw [if_pos small]
    omega
  have at25 (l : Nat) (lo : 2 ≤ l) (hi : l < 14) : siblingDestination ordinal l = recordBase ordinal+176+30*(l-2) := by
    unfold siblingDestination siblingOffset
    rw [if_neg (by omega), if_pos hi]
    omega
  have w01 (l : Nat) (small : l < 2) : siblingWidth l = 32 := by unfold siblingWidth; rw [if_pos small]
  have w25 (l : Nat) (lo : 2 ≤ l) (hi : l < 13) : siblingWidth l = 30 := by
    unfold siblingWidth; rw [if_neg (by omega), if_pos hi]
  have lower6 : bytesAt state (recordBase ordinal+112) 184 =
      (List.range 6).flatMap (fun l => proofDigestBytes (decide (2 ≤ l))
        (if l = 0 then quad else hash (upperNode index l ^^^ 1))) := by
    rw [show List.range 6 = [0,1] ++ (List.range 4).map (fun j => j+2) by decide, List.flatMap_append,
      List.flatMap_map]
    rw [show (184:Nat) = 64+30*(List.range 4).length by decide, bytes_at_append]
    refine congrArg₂ (· ++ ·) ?_ ?_
    · have d0 := digest 0 (by decide)
      have d1 := digest 1 (by decide)
      rw [at01 0 (by decide), w01 0 (by decide)] at d0
      rw [at01 1 (by decide), w01 1 (by decide)] at d1
      rw [show (64:Nat) = 32+32 from rfl, bytes_at_append]
      rw [List.flatMap_cons, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [show recordBase ordinal+112 = recordBase ordinal+112+32*0 by omega, d0,
        show recordBase ordinal+112+32*0+32 = recordBase ordinal+112+32*1 by omega, d1]
    · apply rb_chunks
      intro j inside
      have small : j < 4 := by simpa using inside
      rw [List.getElem_range]
      have dj := digest (j+2) (by omega)
      rw [at25 (j+2) (by omega) (by omega), w25 (j+2) (by omega) (by omega)] at dj
      rw [show recordBase ordinal+112+64+30*j = recordBase ordinal+176+30*(j+2-2) by omega]
      exact dj
  change bytesAt state (recordBase ordinal) (16+(96+(184+238))) = physicalRecord leaf hash quad index salt
  rw [bytes_at_append state _ 16 _, nonceBytes, bytes_at_append state _ 96 _, quartet, bytes_at_append state _ 184 _,
    show recordBase ordinal+16+96 = recordBase ordinal+112 by omega, lower6,
    show recordBase ordinal+112+184 = recordBase ordinal+296 by omega, folded]
  unfold physicalRecord
  simp only [List.append_assoc]
  rfl

end TwoPermutationPrototype.GroupedOpening
