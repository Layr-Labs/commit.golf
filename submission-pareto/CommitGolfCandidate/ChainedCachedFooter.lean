import CommitGolfCandidate.ChainedCachedRecords

/-! Canonical raw footer fields reconstructed from serialized cached nodes. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 SplitCodec
open TwoPermutationPrototype.Sampling TwoPermutationPrototype.Opening
set_option maxRecDepth 8192

def cachedFooterWords (nodes : List Nat) (heap : Nat → BitVec 238) (ordinal : Nat) : BitVec 256 :=
  (heap (nodes.getD ordinal 0)).setWidth 256

def cachedFooter (nodes : List Nat) (heap : Nat → BitVec 238) : Payload (InteriorCodec.footerSpec nodes) :=
  cachedPayload (InteriorCodec.footerSpec nodes) (cachedFooterWords nodes heap)

theorem cached_footer_widths (oracle : Oracle) (leaves : Nat → BitVec 238) (nodes : List Nat)
    (small : ∀ node ∈ nodes, node<512) :
    CachedWidths (InteriorCodec.footerSpec nodes) (cachedFooterWords nodes (referenceHeap oracle leaves)) := by
  apply cached_widths_of_getElem
  intro index inside
  have live : index<nodes.length := by simpa only [InteriorCodec.footerSpec,List.length_map] using inside
  have bound := cached_footer_width oracle leaves nodes[index] (small _ (List.getElem_mem live))
  have lower : 232≤InteriorCodec.footerWidth nodes[index] := by
    unfold InteriorCodec.footerWidth
    split <;> decide
  simp only [cachedFooterWords,InteriorCodec.footerSpec,List.getElem_map,List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem live,Option.getD_some,Nat.add_sub_of_le lower,BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt ((referenceHeap oracle leaves nodes[index]).isLt.trans_le
    (Nat.pow_le_pow_right (by decide) (by decide : 238≤256)))]
  exact bound

theorem cached_footer_source (nodes : List Nat) (heap : Nat → BitVec 238) :
    cachedSourceBytes (InteriorCodec.footerSpec nodes) [] (cachedFooterWords nodes heap)=
      nodes.flatMap (fun node => proofDigestBytes true ((heap node).setWidth 256)) := by
  induction nodes with
  | nil => rfl
  | cons node nodes ih =>
    change (List.ofFn (fun byte : Fin 30 => ((heap node).setWidth 256).extractLsb' (8*byte.val) 8))++
      cachedSourceBytes (InteriorCodec.footerSpec nodes) [] (cachedFooterWords nodes heap)=_
    rw [ih]
    rfl

theorem cached_footer_raw_bytes (oracle : Oracle) (leaves : Nat → BitVec 238) (nodes : List Nat)
    (small : ∀ node ∈ nodes, node<512) :
    rawFieldsBytes (footerRawFields nodes (cachedFooter nodes (referenceHeap oracle leaves)))=
      nodes.flatMap (fun node => proofDigestBytes true ((referenceHeap oracle leaves node).setWidth 256)) := by
  rw [←cached_footer_source]
  apply cached_payload_raw_bytes
  · intro field member
    obtain ⟨node,_,same⟩ := List.mem_map.mp member
    subst field
    change 232%8=0
    decide
  · simp
  · exact cached_footer_widths oracle leaves nodes small

end CommitGolfCandidate.Chained.Native
