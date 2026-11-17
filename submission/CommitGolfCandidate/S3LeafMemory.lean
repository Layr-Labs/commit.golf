import CommitGolfCandidate.S3LeafBytes

/-! Stage-3 leaf: fixed-oracle memory refinement of one twelve-instruction leaf.
The leaf permutes its first 200 bytes with the reply 32 bytes below them, copies its
nonce over reply bytes 88..112, and aims the second reply at its heap slot. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option exponentiation.threshold 4096

/-- The first permutation input is the leaf's first 200 bytes, read in place. -/
theorem s3_first_input (state : MachineState) (u base nonces slots : Nat) (value : Entry)
    (frame : S3LeafFrame state u base nonces slots)
    (data : readBuffer state base 256 = value) :
    s3PermInput (s3LeafHead state) = s3First value := by
  obtain ⟨input, source, heap, unit, low, inputAligned, sourceAligned, inputBound, sourceBound,
    heapBound, separate⟩ := frame
  have pointer : ((s3LeafHead state).getReg .x10).toNat = base := by
    rw [s3_head_register state .x10 (by decide), input, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]
  have same : readBuffer (s3LeafHead state) base 200 = readBuffer state base 200 :=
    s3_read_memory _ _ (s3_head_memory state) _ _
  have valueNat : value.toNat = (readBuffer state base 200).toNat +
      2^1600 * (readBuffer state (base+200) 56).toNat := by
    subst data
    exact s3_read_append state base 200 56 256 (base+200) rfl rfl
  have small : (readBuffer state base 200).toNat < 2^1600 :=
    (readBuffer state base 200).isLt
  unfold s3PermInput
  rw [pointer, same]
  apply BitVec.eq_of_toNat_eq
  unfold s3First
  refine Eq.trans ?_ (BitVec.toNat_ofNat _ _).symm
  rw [valueNat, s3_split_low _ _ _ small]
  exact (Nat.mod_eq_of_lt small).symm

/-- The second permutation input is nonce, chaining value and the leaf's last 88 bytes. -/
theorem s3_second_input (oracle : Oracle) (state : MachineState) (u base nonces slots : Nat)
    (salt : BitVec 256) (value : Entry)
    (frame : S3LeafFrame state u base nonces slots)
    (nonce : readNonce state (nonces+24*u) = salt)
    (data : readBuffer state base 256 = value) :
    s3PermInput (s3MidState oracle u state) =
      s3Second salt (s3FirstReply oracle state) value := by
  have bytes (q : Nat) (hq : q < 2^64) :=
    s3_mid_state_byte oracle u state base nonces slots q frame hq
  obtain ⟨input, source, heap, unit, low, inputAligned, sourceAligned, inputBound, sourceBound,
    heapBound, separate⟩ := frame
  have pointer : ((s3MidState oracle u state).getReg .x10).toNat = base+56 := by
    unfold s3MidState
    rw [s3_mid_input, s3_reply_register, s3_head_register state .x10 (by decide),
      s3_address _ base 56 56 input rfl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have copied : readBuffer (s3MidState oracle u state) (base+56) 24 =
      readBuffer state (nonces+24*u) 24 :=
    s3_read_congr _ _ _ _ 24 (fun i hi => by
      rw [bytes _ (by omega), if_pos (by omega)]
      exact s3_byte_address state _ _ (by omega))
  have chained : readBuffer (s3MidState oracle u state) (base+80) 88 =
      (s3FirstReply oracle state).extractLsb' (8*112) (8*88) :=
    read_serialized_slice _ _ (base+80) 112 88 (fun j hj => by
      rw [bytes _ (by omega), if_neg (by omega), if_pos (by omega),
        show base+80+j-(base-32) = 112+j by omega])
  have tail : readBuffer (s3MidState oracle u state) (base+168) 88 =
      readBuffer state (base+168) 88 :=
    s3_read_congr _ _ _ _ 88 (fun i hi => by
      rw [bytes _ (by omega), if_neg (by omega), if_neg (by omega)])
  have window : (readBuffer (s3MidState oracle u state) (base+56) 200).toNat =
      (readBuffer (s3MidState oracle u state) (base+56) 24).toNat +
        2^192 * (readBuffer (s3MidState oracle u state) (base+80) 176).toNat :=
    s3_read_append _ (base+56) 24 176 200 (base+80) rfl (by omega)
  have rest : (readBuffer (s3MidState oracle u state) (base+80) 176).toNat =
      (readBuffer (s3MidState oracle u state) (base+80) 88).toNat +
        2^704 * (readBuffer (s3MidState oracle u state) (base+168) 88).toNat :=
    s3_read_append _ (base+80) 88 88 176 (base+168) rfl (by omega)
  have valueNat : value.toNat = (readBuffer state base 168).toNat +
      2^1344 * (readBuffer state (base+168) 88).toNat := by
    subst data
    exact s3_read_append state base 168 88 256 (base+168) rfl rfl
  have small : (readBuffer state base 168).toNat < 2^1344 :=
    (readBuffer state base 168).isLt
  have saltNat : salt.toNat = (readBuffer state (nonces+24*u) 24).toNat := by
    rw [← nonce, read_nonce_buffer]
    exact s3_expand_nat _
  have nonceSmall : (readBuffer state (nonces+24*u) 24).toNat < 2^192 :=
    (readBuffer state (nonces+24*u) 24).isLt
  have replySmall : (s3FirstReply oracle state).toNat < 2^896 * 2^704 :=
    lt_of_lt_of_eq (s3FirstReply oracle state).isLt (by norm_num [PERMUTATION_WIDTH])
  have chainedNat : (readBuffer (s3MidState oracle u state) (base+80) 88).toNat =
      (s3FirstReply oracle state).toNat / 2^896 := by
    rw [chained, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
    exact Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul replySmall)
  have total : (readBuffer (s3MidState oracle u state) (base+56) 200).toNat < 2^(8*200) :=
    (readBuffer (s3MidState oracle u state) (base+56) 200).isLt
  have assembled : (readBuffer state (nonces+24*u) 24).toNat +
      (s3FirstReply oracle state).toNat / 2^896 * 2^192 +
      (readBuffer state (base+168) 88).toNat * 2^896 =
      (readBuffer (s3MidState oracle u state) (base+56) 200).toNat := by
    rw [window, rest, copied, chainedNat, tail]
    have power : (2:Nat)^896 = 2^192 * 2^704 := by norm_num
    rw [power]
    generalize (2:Nat)^192 = p
    generalize (2:Nat)^704 = r
    ring
  unfold s3PermInput
  rw [pointer]
  apply BitVec.eq_of_toNat_eq
  unfold s3Second
  refine Eq.trans ?_ (BitVec.toNat_ofNat _ _).symm
  rw [saltNat, Nat.mod_eq_of_lt nonceSmall, valueNat,
    s3_split_high _ _ _ small, assembled]
  exact (Nat.mod_eq_of_lt total).symm

/-- Bytes after one leaf: the second reply at the slot, otherwise the state at the second call. -/
theorem s3_leaf_state_byte (oracle : Oracle) (u : Nat) (state : MachineState)
    (base nonces slots query : Nat) (frame : S3LeafFrame state u base nonces slots)
    (queryBound : query < 2^64) :
    (checkEvaluation oracle (s3Leaf u state)).1.getByte (BitVec.ofNat 64 query) =
      if slots+32*u ≤ query ∧ query < slots+32*u+200 then
        (s3SecondReply oracle u state).extractLsb' (8*(query-(slots+32*u))) 8
      else (s3MidState oracle u state).getByte (BitVec.ofNat 64 query) := by
  have output : (s3MidState oracle u state).getReg .x12 = BitVec.ofNat 64 (slots+32*u) := by
    unfold s3MidState
    rw [s3_mid_output, s3_reply_register, s3_head_register state .x23 (by decide)]
    exact s3_address _ slots (32*u) _ frame.heap (s3_unit_offset u frame.unit).2.2.2
  rw [s3_leaf_evaluation]
  change (s3LeafTail (s3PermReply (s3MidState oracle u state)
    (s3SecondReply oracle u state))).getByte _ = _
  rw [s3_tail_byte]
  exact s3_reply_byte (s3MidState oracle u state) (slots+32*u) query _ output frame.heapBound
    queryBound

/-- The heap slot receives the stage-3 digest of the leaf under its nonce. -/
theorem s3_leaf_digest (oracle : Oracle) (u : Nat) (state : MachineState)
    (base nonces slots : Nat) (salt : BitVec 256) (value : Entry)
    (frame : S3LeafFrame state u base nonces slots)
    (nonce : readNonce state (nonces+24*u) = salt)
    (data : readBuffer state base 256 = value) :
    readBuffer (checkEvaluation oracle (s3Leaf u state)).1 (slots+32*u) 32 =
      s3LeafDigest oracle.permutation salt value := by
  have reply : s3SecondReply oracle u state =
      oracle.permutation (s3Second salt (oracle.permutation (s3First value)) value) := by
    unfold s3SecondReply
    rw [s3_second_input oracle state u base nonces slots salt value frame nonce data]
    unfold s3FirstReply
    rw [s3_first_input state u base nonces slots value frame data]
  have heapBound := frame.heapBound
  have read := read_serialized_slice (checkEvaluation oracle (s3Leaf u state)).1
    (s3SecondReply oracle u state) (slots+32*u) 0 32 (fun j hj => by
      rw [s3_leaf_state_byte oracle u state base nonces slots _ frame (by omega),
        if_pos (by omega), show slots+32*u+j-(slots+32*u) = 0+j by omega])
  rw [read, reply]
  unfold s3LeafDigest
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.extractLsb'_toNat]

/-- A leaf changes only `[base-32, base+168)` and `[slot, slot+200)`. -/
theorem s3_leaf_preserves (oracle : Oracle) (u : Nat) (state : MachineState)
    (base nonces slots address count : Nat) (frame : S3LeafFrame state u base nonces slots)
    (bound : address+count ≤ 2^64)
    (input : address+count+32 ≤ base ∨ base+168 ≤ address)
    (output : address+count ≤ slots+32*u ∨ slots+32*u+200 ≤ address) :
    readBuffer (checkEvaluation oracle (s3Leaf u state)).1 address count =
      readBuffer state address count :=
  s3_read_congr _ _ _ _ count (fun i hi => by
    rw [s3_leaf_state_byte oracle u state base nonces slots _ frame (by omega),
      if_neg (by omega),
      s3_mid_state_byte oracle u state base nonces slots _ frame (by omega),
      if_neg (by omega), if_neg (by omega)])

/-- The nonce copy stays in the consumed message window at `[base+56, base+80)`. -/
theorem s3_leaf_nonce_copy (oracle : Oracle) (u : Nat) (state : MachineState)
    (base nonces slots : Nat) (frame : S3LeafFrame state u base nonces slots)
    (output : base+80 ≤ slots+32*u ∨ slots+32*u+200 ≤ base+56) :
    readBuffer (checkEvaluation oracle (s3Leaf u state)).1 (base+56) 24 =
      readBuffer state (nonces+24*u) 24 := by
  have inputBound := frame.inputBound
  exact s3_read_congr _ _ _ _ 24 (fun i hi => by
    rw [s3_leaf_state_byte oracle u state base nonces slots _ frame (by omega),
      if_neg (by omega),
      s3_mid_state_byte oracle u state base nonces slots _ frame (by omega),
      if_pos (by omega)]
    exact s3_byte_address state _ _ (by omega))

/-- Registers other than the scratch word, the input pointer and the output pointer are kept. -/
theorem s3_leaf_register (oracle : Oracle) (u : Nat) (state : MachineState) (reg : Reg)
    (notScratch : reg ≠ .x6) (notInput : reg ≠ .x10) (notOutput : reg ≠ .x12) :
    (checkEvaluation oracle (s3Leaf u state)).1.getReg reg = state.getReg reg := by
  rw [s3_leaf_evaluation]
  change (s3LeafTail (s3PermReply (s3MidState oracle u state)
    (s3SecondReply oracle u state))).getReg reg = _
  rw [s3_tail_register _ reg notInput, s3_reply_register]
  unfold s3MidState
  rw [s3_mid_register u _ reg notScratch notInput notOutput, s3_reply_register,
    s3_head_register state reg notOutput]

/-- The input pointer advances by one leaf. -/
theorem s3_leaf_input (oracle : Oracle) (u : Nat) (state : MachineState) (base : Nat)
    (pointer : state.getReg .x10 = BitVec.ofNat 64 base) :
    (checkEvaluation oracle (s3Leaf u state)).1.getReg .x10 = BitVec.ofNat 64 (base+256) := by
  rw [show base+256 = base+56+200 by omega, s3_leaf_evaluation]
  change (s3PermReply (s3MidState oracle u state) (s3SecondReply oracle u state)).getReg .x10 +
    signExtend12 200 = _
  rw [s3_reply_register]
  unfold s3MidState
  rw [s3_mid_input, s3_reply_register, s3_head_register state .x10 (by decide),
    s3_address _ base 56 56 pointer rfl, s3_address _ (base+56) 200 200 rfl rfl]

end CommitGolfCandidate
