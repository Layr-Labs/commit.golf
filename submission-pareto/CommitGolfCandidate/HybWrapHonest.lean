import CommitGolfCandidate.HybWrapSpec
import CommitGolfCandidate.QuadHonestInput

/-! The wrapper's expansion of an honest compact proof is the donor's honest proof: the
compact records carry the 5-ary blocks in rotation order and one binary sibling per level, the
table recomputes the 5-ary level 14-17 nodes, and the virtual index is the record's. -/

namespace TwoPermutationPrototype.HybWrap
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Quad.Checker (honestCheckInput)
open TwoPermutationPrototype.Quad.Honest (honestLeaves honestPenta honestOrder honestIndex honest_order_length
  honest_record_byte nonce_byte virt_byte sibling_byte honest_proof_parts honest_proof_length)

set_option maxHeartbeats 2000000

/-- An honest checker input in the submitted compact format. -/
def capCheckInput (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) : CheckInput :=
  let view := pentaHonestView capTranscriptBuilder
    (BiPermutation.equiv Block oracle.permutation) message positions salts
  ⟨view.1, positions, message.restrict positions, view.2⟩

theorem cap_proof_parts (oracle : Oracle) (message : Message) (positions : Positions) (salts : CompleteSaltTape) :
    (capCheckInput oracle message positions salts).proof =
      (honestOrder positions).flatMap (fun i => capRecord (honestPenta oracle) (honestLeaves oracle message salts)
        i.val (salts i.val)) ++
      (if positions.card = 0 then [] else capLevel (honestPenta oracle) (honestLeaves oracle message salts) CAP_LEVEL) :=
  rfl

theorem honest_index_sorted (positions : Positions) (o : Nat) (present : o < positions.card) :
    (honestIndex positions o present).val.val = sortedIndex positions o := by
  have mapped := Finset.map_sort (r := fun i j : {i // i ∈ positions} => i.val ≤ j.val)
    (r' := fun i j : Index => i ≤ j) (f := Function.Embedding.subtype (· ∈ positions))
    (s := positions.attach) (by intro a _ b _; rfl)
  simp only [Finset.attach_map_val, Function.Embedding.coe_subtype] at mapped
  unfold sortedIndex honestIndex honestOrder
  have lo : o < (positions.sort (· ≤ ·)).length := by rw [Finset.length_sort]; exact present
  rw [List.getElem?_eq_getElem lo]
  simp only [Option.map_some, Option.getD_some]
  have := congrArg (fun l : List Index => l[o]?) mapped
  simp only [List.getElem?_map] at this
  rw [List.getElem?_eq_getElem (by rw [Finset.length_sort, Finset.card_attach]; exact present),
    List.getElem?_eq_getElem lo] at this
  simpa using congrArg Fin.val (Option.some_inj.mp this)

/-! ### Bytes of the compact honest proof -/

theorem cap_record_length' (penta : PentaFunction) (leaves : DigestTape) (index : Index) (salt : BitVec 128) :
    (capRecord penta leaves index salt).length = 752 := cap_record_length penta leaves index salt

theorem cap_record_byte (oracle : Oracle) (message : Message) (positions : Positions) (salts : CompleteSaltTape)
    (o off : Nat) (present : o < positions.card) (inside : off < 752) :
    (capCheckInput oracle message positions salts).proof[752*o+off]? =
      (capRecord (honestPenta oracle) (honestLeaves oracle message salts) (honestIndex positions o present).val
        (salts (honestIndex positions o present).val))[off]? := by
  rw [cap_proof_parts, List.getElem?_append_left]
  · rw [flat_map_chunk _ 752 _ (fun _ _ => cap_record_length' _ _ _ _) o off inside,
      List.getElem?_eq_getElem (by rw [honest_order_length]; exact present)]
    rfl
  · rw [flat_map_length _ 752 _ (fun _ _ => cap_record_length' _ _ _ _), honest_order_length]
    omega

theorem cap_table_byte (oracle : Oracle) (message : Message) (positions : Positions) (salts : CompleteSaltTape)
    (nonempty : positions.card ≠ 0) (j t : Nat) (hj : j < 210) (ht : t < 32) :
    (capCheckInput oracle message positions salts).proof[752*positions.card+(32*j+t)]? =
      (digestBytes (pentaNode (honestPenta oracle) (honestLeaves oracle message salts) CAP_LEVEL j))[t]? := by
  rw [cap_proof_parts, if_neg nonempty, List.getElem?_append_right]
  · rw [flat_map_length _ 752 _ (fun _ _ => cap_record_length' _ _ _ _), honest_order_length,
      Nat.add_sub_cancel_left]
    unfold capLevel
    rw [flat_map_chunk _ 32 _ (fun _ _ => digestBytes_length _) j t ht,
      List.getElem?_range (by rw [cap_count_value]; exact hj)]
    rfl
  · rw [flat_map_length _ 752 _ (fun _ _ => cap_record_length' _ _ _ _), honest_order_length]
    omega

theorem cap_salt_byte (penta : PentaFunction) (leaves : DigestTape) (index : Index) (salt : BitVec 128)
    (off : Nat) (inside : off < 16) :
    (capRecord penta leaves index salt)[off]? = some (salt.extractLsb' (8*off) 8) := by
  unfold capRecord
  rw [List.append_assoc, List.getElem?_append_left (by simpa [saltBytes] using inside)]
  simp only [saltBytes, List.getElem?_ofFn, dite_eq_left inside]

private theorem block_len (penta : PentaFunction) (leaves : DigestTape) (index : Index) (k : Nat) :
    ((List.range 4).flatMap fun j =>
      digestBytes (pentaGroup penta leaves k (index.val / placeValue (k + 1)) (pentaRot index k j))).length = 128 := by
  rw [flat_map_length _ 32 _ (fun _ _ => digestBytes_length _)]; simp

theorem cap_penta_byte (penta : PentaFunction) (leaves : DigestTape) (index : Index) (salt : BitVec 128)
    (k j t : Nat) (hk : k < 4) (hj : j < 4) (ht : t < 32) :
    (capRecord penta leaves index salt)[16+(128*k+(32*j+t))]? =
      (digestBytes (pentaGroup penta leaves k (index.val / placeValue (k + 1)) (pentaRot index k j)))[t]? := by
  unfold capRecord
  have pl : ((List.range PENTA_LOW).flatMap fun k => (List.range 4).flatMap fun j =>
      digestBytes (pentaGroup penta leaves k (index.val / placeValue (k + 1)) (pentaRot index k j))).length = 512 := by
    rw [flat_map_length _ 128 _ (fun k _ => block_len penta leaves index k)]; simp [PENTA_LOW]
  rw [List.getElem?_append_left (by rw [List.length_append, pl]; simp [saltBytes]; omega),
    List.getElem?_append_right (by simp [saltBytes]), show (saltBytes salt).length = 16 by simp [saltBytes],
    Nat.add_sub_cancel_left,
    flat_map_chunk _ 128 _ (fun k _ => block_len penta leaves index k) k _ (by omega),
    List.getElem?_range (by simpa [PENTA_LOW] using hk)]
  simp only [Option.bind_some]
  rw [flat_map_chunk _ 32 _ (fun _ _ => digestBytes_length _) j t ht, List.getElem?_range hj]
  rfl

theorem cap_bin_byte (penta : PentaFunction) (leaves : DigestTape) (index : Index) (salt : BitVec 128)
    (m t : Nat) (hm : m < 7) (ht : t < 32) :
    (capRecord penta leaves index salt)[528+(32*m+t)]? =
      (digestBytes (pentaGroup penta leaves (PENTA_LOW+m) (index.val / placeValue (PENTA_LOW+m+1))
        (binSibling index (PENTA_LOW+m))))[t]? := by
  unfold capRecord
  have pl : (saltBytes salt ++ (List.range PENTA_LOW).flatMap fun k => (List.range 4).flatMap fun j =>
      digestBytes (pentaGroup penta leaves k (index.val / placeValue (k + 1)) (pentaRot index k j))).length = 528 := by
    rw [List.length_append, flat_map_length _ 128 _ (fun k _ => block_len penta leaves index k)]
    simp [PENTA_LOW, saltBytes]
  rw [List.getElem?_append_right (by rw [pl]; omega), pl, Nat.add_sub_cancel_left,
    flat_map_chunk _ 32 _ (fun _ _ => digestBytes_length _) m t ht,
    List.getElem?_range (by simpa [CAP_LEVEL, PENTA_LOW] using hm)]
  rfl

/-! ### Words from bytes -/

theorem pack_congr_bytes (A B : Proof) (u u' : Nat) (same : ∀ j < 8, A[8*u+j]? = B[8*u'+j]?) :
    packWord A u = packWord B u' := by
  unfold packWord
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [same j (Finset.mem_range.mp hj)]

theorem pack_of_word (A : Proof) (u : Nat) (w : Word) (h : ∀ j < 8, A[8*u+j]? = (wordBytes w)[j]?) :
    packWord A u = w := by
  unfold packWord
  rw [Finset.sum_congr rfl (fun j hj => by rw [h j (Finset.mem_range.mp hj)])]
  exact pack_word_bytes w

theorem digest_word (d : BitVec 256) (q j : Nat) (hq : q < 4) (hj : j < 8) :
    (digestBytes d)[8*q+j]? = (wordBytes (d.extractLsb' (64*q) 64))[j]? := by
  simp only [digestBytes, wordBytes, List.getElem?_ofFn, show 8*q+j < 32 by omega, hj, dite_true]
  congr 1
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp only [BitVec.getLsbD_extractLsb']
  simp only [show decide (b < 8) = true from decide_eq_true hb, Bool.true_and]
  rw [show decide (8*j+b < 64) = true from decide_eq_true (by omega), Bool.true_and]
  congr 1; omega

theorem digest_at_bytes (A : Proof) (off : Nat) (d : BitVec 256)
    (h : ∀ t < 32, A[off+t]? = (digestBytes d)[t]?) : digestAt A off = d := by
  unfold digestAt
  have term : ∀ t ∈ Finset.range 32, ((A[off+t]?).getD 0).toNat * 2^(8*t) =
      d.toNat / 2^(8*t) % 256 * 2^(8*t) := by
    intro t ht
    have t32 := Finset.mem_range.mp ht
    rw [h t t32]
    simp only [digestBytes, List.getElem?_ofFn, t32, dite_true, Option.getD_some, BitVec.extractLsb'_toNat]
    congr 1
    rw [Nat.shiftRight_eq_div_pow]
  apply BitVec.eq_of_toNat_eq
  rw [Finset.sum_congr rfl term]
  have digits : ∀ n, ∑ t ∈ Finset.range n, d.toNat / 2^(8*t) % 256 * 2^(8*t) = d.toNat % 2^(8*n) := by
    intro n
    induction n with
    | zero => simp [Nat.mod_one]
    | succ c ih =>
      rw [Finset.sum_range_succ, ih, show 8*(c+1) = 8*c+8 by ring, pow_add, Nat.mod_mul,
        Nat.mul_comm (2^(8*c)) (d.toNat / 2^(8*c) % 2^8), show (2:Nat)^8 = 256 by norm_num]
  rw [digits, BitVec.toNat_ofNat]
  have := d.isLt
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt this]

theorem zero_digest_word (q : Nat) : (0#256 : BitVec 256).extractLsb' (64*q) 64 = 0 := by simp

/-! ### The recomputed upper nodes -/

theorem up_honest (oracle : Oracle) (message : Message) (positions : Positions) (salts : CompleteSaltTape)
    (nonempty : positions.card ≠ 0) :
    ∀ m j, upNode oracle.permutation positions (capCheckInput oracle message positions salts).proof m j =
      pentaNode (honestPenta oracle) (honestLeaves oracle message salts) (11+m) j := by
  intro m
  induction m with
  | zero =>
    intro j
    unfold upNode
    split
    · rename_i hj
      have h164 : j < 210 := by rwa [show pentaCount 11 = 210 by decide] at hj
      unfold tableNode
      apply digest_at_bytes
      intro t ht
      rw [show 752*positions.card+32*j+t = 752*positions.card+(32*j+t) by omega,
        cap_table_byte oracle message positions salts nonempty j t h164 ht]
      rfl
    · rename_i hj
      rw [pentaNode, if_neg hj]
  | succ m ih =>
    intro j
    unfold upNode
    have sb : slotBase (11+m) = 0 := slot_base_high _ (by unfold PENTA_HIGH; omega)
    have rd : radix (11+m) = 5 := radix_high _ (by unfold PENTA_HIGH; omega)
    by_cases hj : j < pentaCount (11+m+1)
    · rw [if_pos hj, show 11+(m+1) = (11+m)+1 by omega, penta_node_succ _ _ _ _ hj]
      unfold honestPenta pentaGroup childIndex
      simp only [sb, rd, ih, Nat.zero_le, if_true, Nat.sub_zero]
      rfl
    · rw [if_neg hj, show 11+(m+1) = (11+m)+1 by omega, pentaNode, if_neg hj]

/-! ### The round trip -/

/-! ### The round trip -/

theorem bytes_word {n : Nat} (x : BitVec n) (a j : Nat) (hj : j < 8) :
    (wordBytes (x.extractLsb' a 64))[j]? = some (x.extractLsb' (a+8*j) 8) := by
  simp only [wordBytes, List.getElem?_ofFn, hj, dite_true]
  congr 1
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp only [BitVec.getLsbD_extractLsb']
  simp only [show decide (b < 8) = true from decide_eq_true hb, Bool.true_and]
  rw [show decide (8*j+b < 64) = true from decide_eq_true (by omega), Bool.true_and]
  congr 1; omega

theorem bytes_word' (w : Word) (j : Nat) (hj : j < 8) :
    (wordBytes w)[j]? = some (w.extractLsb' (8*j) 8) := by
  simp only [wordBytes, List.getElem?_ofFn, hj, dite_true]

theorem zero_bytes (j : Nat) (hj : j < 8) : (wordBytes (0 : Word))[j]? = some 0 := by
  simp only [wordBytes, List.getElem?_ofFn, hj, dite_true]
  simp

theorem rot_binary (index : Index) (k c : Nat) (hk : PENTA_LOW ≤ k) (hk' : k < PENTA_HIGH) :
    (pentaRot index k c).val = (4 + index.val / placeValue k % 2 + c) % 5 := by
  have h : hybridSlot index.val k = 3 + index.val / placeValue k % 2 := by
    unfold hybridSlot; rw [slot_base_mid k hk hk', radix_mid k hk hk']; try omega
  show (hybridSlot index.val k + c + 1) % 5 = _
  rw [h]; omega

theorem place_succ_binary (k : Nat) (hk : PENTA_LOW ≤ k) (hk' : k < PENTA_HIGH) : placeValue (k+1) = placeValue k * 2 := by
  rw [placeValue, radix_mid k hk hk']

theorem group_binary (penta : PentaFunction) (leaves : DigestTape) (k g : Nat) (t : Fin 5) (hk : PENTA_LOW ≤ k)
    (hk' : k < PENTA_HIGH) :
    pentaGroup penta leaves k g t = if 3 ≤ t.val then pentaNode penta leaves k (2*g + (t.val-3)) else 0 := by
  unfold pentaGroup childIndex
  rw [slot_base_mid k hk hk', radix_mid k hk hk']

theorem rot_high (index : Index) (k c : Nat) (hk : PENTA_HIGH ≤ k) :
    (pentaRot index k c).val = (index.val / placeValue k % 5 + c + 1) % 5 := by
  have h : hybridSlot index.val k = index.val / placeValue k % 5 := by
    unfold hybridSlot; rw [slot_base_high k hk, radix_high k hk]; omega
  show (hybridSlot index.val k + c + 1) % 5 = _
  rw [h]

theorem place_succ_high (k : Nat) (hk : PENTA_HIGH ≤ k) : placeValue (k+1) = placeValue k * 5 := by
  rw [placeValue, radix_high k hk]

theorem group_high (penta : PentaFunction) (leaves : DigestTape) (k g : Nat) (t : Fin 5) (hk : PENTA_HIGH ≤ k) :
    pentaGroup penta leaves k g t = pentaNode penta leaves k (5*g + t.val) := by
  unfold pentaGroup childIndex
  rw [slot_base_high k hk, radix_high k hk]
  simp

theorem honest_word (oracle : Oracle) (message : Message) (positions : Positions) (salts : CompleteSaltTape)
    (v : Nat) (inside : v < 243*positions.card) :
    packWord (honestCheckInput oracle message positions salts).proof v =
      expandedWord positions (capCheckInput oracle message positions salts).proof
        (upNode oracle.permutation positions (capCheckInput oracle message positions salts).proof) v := by
  have present : v/243 < positions.card := by omega
  have nonempty : positions.card ≠ 0 := by omega
  have hsort := honest_index_sorted positions (v/243) present
  generalize hP : honestPenta oracle = P at *
  generalize hL : honestLeaves oracle message salts = L at *
  have hbyte : ∀ j < 8, (honestCheckInput oracle message positions salts).proof[8*v+j]? =
      (pentaRecord P L (honestIndex positions (v/243) present).val
        (salts (honestIndex positions (v/243) present).val))[8*(v%243)+j]? := by
    intro j hj
    rw [show 8*v+j = 1944*(v/243)+(8*(v%243)+j) by omega, honest_record_byte _ _ _ _ _ _ present (by omega), hP, hL]
  have cbyte : ∀ b < 752, (capCheckInput oracle message positions salts).proof[752*(v/243)+b]? =
      (capRecord P L (honestIndex positions (v/243) present).val
        (salts (honestIndex positions (v/243) present).val))[b]? := by
    intro b hb
    rw [cap_record_byte _ _ _ _ _ _ present hb, hP, hL]
  generalize (honestIndex positions (v/243) present).val = idx at *
  generalize hr : v/243 = r at *
  generalize he : v%243 = e at *
  have hv : v = 243*r+e := by omega
  have e339 : e < 243 := by omega
  unfold expandedWord
  simp only [hr, he, ← hsort]
  by_cases salt : e < 2
  · rw [if_pos salt]
    have W : ∀ (A : Proof) (u : Nat), (∀ j < 8, A[8*u+j]? = some ((salts idx).extractLsb' (64*e+8*j) 8)) →
        packWord A u = (salts idx).extractLsb' (64*e) 64 :=
      fun A u h => pack_of_word A u _ (fun j hj => by rw [h j hj, bytes_word _ _ _ hj])
    rw [W _ v (fun j hj => by rw [hbyte j hj, nonce_byte _ _ _ _ _ (by omega), show 8*(8*e+j) = 64*e+8*j by ring]),
      W _ (94*r+e) (fun j hj => by
        rw [show 8*(94*r+e)+j = 752*r+(8*e+j) by ring, cbyte _ (by omega), cap_salt_byte _ _ _ _ _ (by omega),
          show 8*(8*e+j) = 64*e+8*j by ring])]
  rw [if_neg salt]
  by_cases virt : e = 2
  · rw [if_pos virt]
    subst virt
    exact pack_of_word _ v _ (fun j hj => by
      rw [hbyte j hj, show 8*2+j = 16+j by ring, virt_byte _ _ _ _ _ hj]
      simp only [wordBytes, List.getElem?_ofFn, hj, dite_true])
  rw [if_neg virt]
  -- donor block words: level k, child c, quarter q
  obtain ⟨k, c, q, hk, hc, hq, rfl⟩ : ∃ k c q, k < 15 ∧ c < 4 ∧ q < 4 ∧ e = 3+16*k+4*c+q :=
    ⟨(e-3)/16, (e-3)%16/4, (e-3)%4, by omega, by omega, by omega, by omega⟩
  have ek : (3+16*k+4*c+q-3)/16 = k := by omega
  have em : (3+16*k+4*c+q-3)%16 = 4*c+q := by omega
  simp only [ek, em, show (4*c+q)/4 = c by omega, show (4*c+q)%4 = q by omega]
  have honest : packWord (honestCheckInput oracle message positions salts).proof v =
      (pentaGroup P L k (idx.val / placeValue (k+1)) (pentaRot idx k c)).extractLsb' (64*q) 64 := by
    apply pack_of_word _ v _ (fun j hj => ?_)
    rw [hbyte j hj, show 8*(3+16*k+4*c+q)+j = 24+128*k+32*c+(8*q+j) by ring,
      sibling_byte _ _ _ _ _ _ _ (by unfold PENTA_LEVELS; omega) hc (by omega), bytes_word _ _ _ hj,
      show 8*(8*q+j) = 64*q+8*j by ring]
  rw [honest]
  by_cases low : k < 4
  · rw [if_pos low]
    symm
    apply pack_of_word _ _ _ (fun j hj => ?_)
    rw [show 8*(94*r+2+16*k+(4*c+q))+j = 752*r+(16+(128*k+(32*c+(8*q+j)))) by ring, cbyte _ (by omega),
      cap_penta_byte _ _ _ _ _ _ _ low hc (by omega), digest_word _ _ _ hq hj]
  rw [if_neg low]
  have hk3 : PENTA_LOW ≤ k := by unfold PENTA_LOW; omega
  by_cases mid : k < 11
  · rw [if_pos mid]
    have hk4 : k < PENTA_HIGH := by unfold PENTA_HIGH; omega
    have rot := rot_binary idx k c hk3 hk4
    have gdiv : idx.val / placeValue (k+1) = idx.val / placeValue k / 2 := by
      rw [place_succ_binary k hk3 hk4, Nat.div_div_eq_div_mul]
    generalize hn : idx.val / placeValue k = n at rot gdiv
    rw [gdiv, group_binary _ _ _ _ _ hk3 hk4]
    by_cases sib : c = 3*(n%2)
    · rw [if_pos sib]
      have hs : (pentaRot idx k c).val = 3 + (1 - n%2) := by rw [rot]; omega
      rw [if_pos (by omega), hs, show 2*(n/2) + (3+(1-n%2)-3) = n+1-2*(n%2) by omega]
      symm
      apply pack_of_word _ _ _ (fun j hj => ?_)
      have b := cap_bin_byte P L idx (salts idx) (k-4) (8*q+j) (by omega) (by omega)
      rw [show PENTA_LOW+(k-4) = k by unfold PENTA_LOW; omega, group_binary _ _ _ _ _ hk3 hk4] at b
      have bs : (binSibling idx k).val = 3+(1-n%2) := by unfold binSibling; simp only []; omega
      rw [gdiv, bs, if_pos (by omega), show 2*(n/2) + (3+(1-n%2)-3) = n+1-2*(n%2) by omega] at b
      rw [show 8*(94*r+66+4*(k-4)+q)+j = 752*r+(528+(32*(k-4)+(8*q+j))) by omega, cbyte _ (by omega), b,
        show 8*q+j = 8*q+j from rfl, digest_word _ _ _ hq hj]
    · rw [if_neg sib]
      rw [if_neg (by rw [rot]; omega)]
      simp
  · rw [if_neg mid]
    have hk4 : PENTA_HIGH ≤ k := by unfold PENTA_HIGH; omega
    have rot := rot_high idx k c hk4
    have gdiv : idx.val / placeValue (k+1) = idx.val / placeValue k / 5 := by
      rw [place_succ_high k hk4, Nat.div_div_eq_div_mul]
    generalize hn : idx.val / placeValue k = n at rot gdiv
    rw [gdiv, group_high _ _ _ _ _ hk4, rot]
    have up := up_honest oracle message positions salts nonempty (k-11) (5*(n/5)+(n%5+c+1)%5)
    rw [hP, hL, show 11+(k-11) = k by omega] at up
    rw [up]

theorem digits8 (b : Nat → Nat) (bnd' : ∀ i, b i < 2^8) (j : Nat) (hj : j < 8) :
    (∑ i ∈ Finset.range 8, b i * 2^(8*i)) % 2^64 / 2^(8*j) % 2^8 = b j := by
  have bnd : ∀ i, b i < 256 := fun i => by have := bnd' i; norm_num at this; exact this
  have b0 := bnd 0; have b1 := bnd 1; have b2 := bnd 2; have b3 := bnd 3
  have b4 := bnd 4; have b5 := bnd 5; have b6 := bnd 6; have b7 := bnd 7
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  interval_cases j <;> simp only [Nat.reducePow, Nat.reduceMul, Nat.zero_add, Nat.mul_one, Nat.pow_zero] <;> omega

theorem pack_byte (L : Proof) (u j : Nat) (hj : j < 8) :
    (packWord L u).extractLsb' (8*j) 8 = (L[8*u+j]?).getD 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat]
  unfold packWord
  rw [BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  exact digits8 (fun i => ((L[8*u+i]?).getD 0).toNat) (fun i => BitVec.isLt _) j hj

theorem list_words (L : List Byte) (n : Nat) (len : L.length = 8*n) :
    L = (List.range n).flatMap fun v => wordBytes (packWord L v) := by
  apply List.ext_getElem?
  intro b
  by_cases inside : b < 8*n
  · rw [show b = 8*(b/8)+b%8 by omega,
      flat_map_chunk _ 8 _ (fun _ _ => word_bytes_length _) _ _ (Nat.mod_lt _ (by decide)),
      List.getElem?_range (by omega)]
    simp only [Option.bind_some]
    rw [bytes_word' (packWord L (b/8)) (b%8) (Nat.mod_lt _ (by decide)), pack_byte _ _ _ (Nat.mod_lt _ (by decide)),
      List.getElem?_eq_getElem (by omega)]
    rfl
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none]
    rw [flat_map_length _ 8 _ (fun _ _ => word_bytes_length _)]; simp; omega

/-- The wrapper's expansion of an honest compact input is the donor's honest input. -/
theorem expand_honest (oracle : Oracle) (message : Message) (positions : Positions) (salts : CompleteSaltTape) :
    expandInput oracle (capCheckInput oracle message positions salts) = honestCheckInput oracle message positions salts := by
  have proofs : (expandInput oracle (capCheckInput oracle message positions salts)).proof =
      (honestCheckInput oracle message positions salts).proof := by
    show expandProof positions _ _ = _
    rw [list_words (honestCheckInput oracle message positions salts).proof (243*positions.card)
      (by rw [honest_proof_length]; ring)]
    unfold expandProof
    apply List.flatMap_congr
    intro v hv
    rw [honest_word oracle message positions salts v (List.mem_range.mp hv)]
    rfl
  calc expandInput oracle (capCheckInput oracle message positions salts)
      = { honestCheckInput oracle message positions salts with
          proof := (expandInput oracle (capCheckInput oracle message positions salts)).proof } := rfl
    _ = honestCheckInput oracle message positions salts := by rw [proofs]

end TwoPermutationPrototype.HybWrap
