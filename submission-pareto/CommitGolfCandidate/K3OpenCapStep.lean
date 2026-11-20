import CommitGolfCandidate.K3OpenCapBytes

/-! T238 cap bytes, one emitted node: if the cap bytes after `vs` are `foldNodes vs` and the emit block did what
`EmitCap238` states (slot bytes copied from the node, for the 8th node the halfword-14 fold of the previous seven
slots, nothing else touched), then the cap bytes after the node are `foldNodes (vs ++ [v])` for the node's value `v`.
Owner of the proof: S8-K3-OW3 (delegated by O); statement frozen by O. -/
namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open Opening (capDigestAddress proofBase)

private theorem plain30_length (x : BitVec 256) : (plain30 x).length=30 := by
  simp [plain30, digestBytes]

private theorem bytes_at_take (s : MachineState) (a n m : Nat) (h : m ≤ n) :
    (bytesAt s a n).take m=bytesAt s a m := by
  unfold bytesAt
  rw [← List.map_take, List.take_range, Nat.min_eq_left h]

private theorem bytes_at_copy (s t : MachineState) (a b n : Nat)
    (same : ∀ j<n, t.getByte (BitVec.ofNat 64 (a+j))=s.getByte (BitVec.ofNat 64 (b+j))) :
    bytesAt t a n=bytesAt s b n := by
  unfold bytesAt
  apply List.map_congr_left; intro j hj; exact same j (List.mem_range.1 hj)

private theorem bytes_at_two (s : MachineState) (a : Nat) :
    bytesAt s a 2=[s.getByte (BitVec.ofNat 64 a), s.getByte (BitVec.ofNat 64 (a+1))] := by
  unfold bytesAt; rfl

private theorem bytes_at_slots (s : MachineState) (a w : Nat) : ∀ k : Nat,
    bytesAt s a (w*k)=(List.range k).flatMap (fun i => bytesAt s (a+w*i) w)
  | 0 => by simp [bytesAt]
  | k+1 => by
    rw [Nat.mul_succ, bytes_at_append, bytes_at_slots s a w k, List.range_succ, List.flatMap_append]
    simp [List.flatMap_cons]

/-- Plain slots read back one by one. -/
private theorem slots_of_flat (s : MachineState) (Q : List (BitVec 256)) : ∀ a : Nat,
    bytesAt s a (30*Q.length)=Q.flatMap plain30 →
      ∀ k<Q.length, bytesAt s (a+30*k) 30=plain30 (Q.getD k 0) := by
  induction Q with
  | nil => intro a _ k hk; simp at hk
  | cons q Q ih =>
    intro a h k hk
    have len : 30*(q::Q).length=30+30*Q.length := by rw [List.length_cons]; omega
    rw [len, bytes_at_append, List.flatMap_cons] at h
    obtain ⟨head, tail⟩ := List.append_inj h (by rw [bytes_at_length, plain30_length])
    cases k with
    | zero => simpa using head
    | succ k =>
      have small : k<Q.length := by rw [List.length_cons] at hk; omega
      have shift : a+30*(k+1)=a+30+30*k := by omega
      rw [shift, List.getD_cons_succ]
      exact ih (a+30) tail k small

private theorem byte_of_slot (s : MachineState) (a : Nat) (x : BitVec 256) (h : bytesAt s a 30=plain30 x)
    (j : Nat) (hj : j<30) : s.getByte (BitVec.ofNat 64 (a+j))=x.extractLsb' (8*j) 8 := by
  have hj' : j<(bytesAt s a 30).length := by rw [bytes_at_length]; exact hj
  have e := List.getElem_of_eq h hj'
  rw [bytes_at_getElem s a 30 j hj] at e
  rw [e]
  simp only [plain30, digestBytes, List.getElem_take, List.getElem_ofFn]

private theorem cat_bytes (x : BitVec 256) :
    x.extractLsb' 232 8 ++ x.extractLsb' 224 8=x.extractLsb' 224 16 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_append]
  by_cases low : i<8
  · rw [if_pos low, BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb']
    simp [low, show i<16 by omega]
  · have high : i-8<8 := by omega
    have bit : 232+(i-8)=224+i := by omega
    rw [if_neg low, BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb', bit]
    simp [high, show i<16 by omega]

/-- A plain slot's halfword 14 is bits `224..239` of its node. -/
private theorem half_of_slot (s : MachineState) (a : Nat) (x : BitVec 256) (h : bytesAt s a 30=plain30 x) :
    halfAt s (a+28)=x.extractLsb' 224 16 := by
  have b0 := byte_of_slot s a x h 28 (by decide)
  have b1 := byte_of_slot s a x h 29 (by decide)
  have next : a+28+1=a+29 := by omega
  unfold halfAt
  rw [next, b0, b1]
  exact cat_bytes x

theorem cap_bytes_step (before after : MachineState) (capStart node count : Nat) (vs : List (BitVec 256))
    (counter : count=7-vs.length%8) (even : capStart%2=0) (fit : capStart+capOffset (vs.length+1)+2 ≤ 2^64)
    (bytes : bytesAt before capStart (capOffset vs.length)=foldNodes vs)
    (copied : ∀ b<(if count=0 then 28 else 30),
      after.getByte (BitVec.ofNat 64 (capStart+capOffset vs.length+b))=
        before.getByte (BitVec.ofNat 64 (capDigestAddress node+b)))
    (folded : count=0 → ∀ k<7, halfAt after (capStart+capOffset vs.length-182+30*k)=
      (halfAt before (capStart+capOffset vs.length-182+30*k) |||
        ((halfAt before (capDigestAddress node+28) >>> (2*k)) <<< 14)))
    (frame : ∀ a<2^64, ¬EmitTouched (capStart+capOffset vs.length) count a →
      after.getByte (BitVec.ofNat 64 a)=before.getByte (BitVec.ofNat 64 a)) :
    bytesAt after capStart (capOffset (vs.length+1))=foldNodes (vs++[readBuffer before (capDigestAddress node) 32]) := by
  generalize hM : (2:Nat)^64=M at fit frame
  by_cases closes : vs.length%8=7
  · -- the eighth node of a group: one `foldPack8` over the group's seven plain slots and the node
    have hc : count=0 := by omega
    subst hc
    rw [if_pos rfl] at copied
    have folds := folded rfl
    obtain ⟨base, hbase⟩ : ∃ base, base=capStart+capOffset (vs.length-7) := ⟨_, rfl⟩
    obtain ⟨Q, hQ⟩ : ∃ Q, Q=vs.drop (vs.length-7) := ⟨_, rfl⟩
    have big : 7 ≤ vs.length := by omega
    have hQlen : Q.length=7 := by rw [hQ, List.length_drop]; omega
    have hoffn : capOffset vs.length=capOffset (vs.length-7)+210 := by unfold capOffset; omega
    have hoff : capOffset (vs.length+1)=capOffset (vs.length-7)+238 := by unfold capOffset; omega
    have hD : capStart+capOffset vs.length=base+210 := by omega
    rw [hD] at copied folds frame
    -- the cap bytes before: complete groups, then the group's seven plain slots
    have cut : vs.length-vs.length%8=vs.length-7 := by omega
    rw [fold_nodes_tail vs, cut, ← hQ, hoffn, bytes_at_append, ← hbase] at bytes
    have lenP : (bytesAt before capStart (capOffset (vs.length-7))).length=
        (foldNodes (vs.take (vs.length-7))).length := by
      rw [bytes_at_length, fold_nodes_length, List.length_take, Nat.min_eq_left (Nat.sub_le _ _)]
    obtain ⟨headBytes, groupBytes⟩ := List.append_inj bytes lenP
    have slots := slots_of_flat before Q base (by rw [hQlen]; exact groupBytes)
    -- the bytes after
    rw [fold_nodes_snoc_fold vs _ closes, ← hQ, hoff, bytes_at_append, ← hbase]
    have pre : bytesAt after capStart (capOffset (vs.length-7))=bytesAt before capStart (capOffset (vs.length-7)) :=
      bytes_at_congr before after _ _ (fun j hj => frame _ (by omega) (by
        unfold EmitTouched; rw [if_pos rfl]; rintro (⟨h1, h2⟩ | ⟨-, k, hk, h | h⟩) <;> omega))
    rw [pre, headBytes]
    congr 1
    have getLow : ∀ k<7, (Q++[readBuffer before (capDigestAddress node) 32]).getD k 0=Q.getD k 0 := by
      intro k hk
      have hk' : k<Q.length := by omega
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left hk']
    have getTop : (Q++[readBuffer before (capDigestAddress node) 32]).getD 7 0=
        readBuffer before (capDigestAddress node) 32 := by
      have h7 : Q.length ≤ 7 := by omega
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right h7, hQlen]; simp
    have split : bytesAt after base 238=
        (List.range 7).flatMap (fun k => bytesAt after (base+30*k) 30)++bytesAt after (base+210) 28 := by
      rw [← bytes_at_slots after base 30 7]
      exact bytes_at_append after base 210 28
    have slotAfter : ∀ k ∈ List.range 7, bytesAt after (base+30*k) 30=
        foldSlot ((Q++[readBuffer before (capDigestAddress node) 32]).getD k 0)
          ((Q++[readBuffer before (capDigestAddress node) 32]).getD 7 0) k := by
      intro k member
      have hk := List.mem_range.1 member
      rw [getLow k hk, getTop]
      have src := slots k (by omega)
      have oldHalf := half_of_slot before (base+30*k) _ src
      have newHalf := folds k hk
      have address : base+210-182+30*k=base+30*k+28 := by omega
      rw [address, oldHalf, half_of_read before (capDigestAddress node)] at newHalf
      have hb := half_bytes after (base+30*k+28)
      rw [newHalf] at hb
      unfold foldSlot
      refine (bytes_at_append after (base+30*k) 28 2).trans ?_
      have low : bytesAt after (base+30*k) 28=bytesAt before (base+30*k) 28 :=
        bytes_at_congr before after _ _ (fun j hj => frame _ (by omega) (by
          unfold EmitTouched; rw [if_pos rfl]; rintro (⟨h1, h2⟩ | ⟨-, k', hk', h | h⟩) <;> omega))
      rw [low, ← bytes_at_take before (base+30*k) 30 28 (by decide), src, bytes_at_two, ← hb.1, ← hb.2]
      simp only [plain30, List.take_take]
      rfl
    have lastAfter : bytesAt after (base+210) 28=
        (digestBytes ((Q++[readBuffer before (capDigestAddress node) 32]).getD 7 0)).take 28 := by
      rw [getTop, bytes_at_copy before after _ _ 28 copied, digest_bytes_read,
        bytes_at_take before _ 32 28 (by decide)]
    simp only [foldPack8]
    rw [split, List.flatMap_congr slotAfter, lastAfter]
  · -- a plain 30-byte slot
    have hc : count ≠ 0 := by omega
    rw [if_neg hc] at copied
    have hoff : capOffset (vs.length+1)=capOffset vs.length+30 := by unfold capOffset; omega
    rw [fold_nodes_snoc_plain vs _ closes, hoff, bytes_at_append]
    have pre : bytesAt after capStart (capOffset vs.length)=bytesAt before capStart (capOffset vs.length) :=
      bytes_at_congr before after _ _ (fun j hj => frame _ (by omega) (by
        unfold EmitTouched; rw [if_neg hc]; rintro (⟨h1, h2⟩ | ⟨h0, -⟩) <;> omega))
    rw [pre, bytes, bytes_at_copy before after _ _ 30 copied, plain_read]

end TwoPermutationPrototype.GroupedOpening
