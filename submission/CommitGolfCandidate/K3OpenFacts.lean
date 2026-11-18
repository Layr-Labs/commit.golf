import CommitGolfCandidate.GroupOpenResume
import CommitGolfCandidate.GroupOpenHeaderSpec
import CommitGolfCandidate.K3OpenReply

/-! K3-lite opener facts: what the virtual trapdoor (the memory after the prefix pass) holds, and the opened proof. -/
namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open TwoPermutationPrototype.Sampling
set_option maxRecDepth 20000
set_option maxHeartbeats 1400000

/-- The prefix pass's end state for a nonempty opening. -/
noncomputable def passEnd (o : Oracle) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) : MachineState :=
  fixedPass o p (keyOf td) p.card 0 (header (actual.initialState .opening (td,p)))

theorem pass_end_facts (hc : HeaderFacts) (o : Oracle) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions)
    (nz : 0<p.card) :
    Ready td p (keyOf td) (passEnd o td p) p.card ∧ Seen o (keyOf td) td p (passEnd o td p) p.card := by
  let s0:=header (actual.initialState .opening (td,p))
  have r0 := hc.ready td p nz
  have r := fixed_post o td p (keyOf td) s0 0 p.card (by omega) r0
  have seen := seen_pass o td p (keyOf td) s0 0 p.card (by omega) r0 (seen_zero o (keyOf td) td p s0)
  rw [Nat.zero_add] at r seen
  exact ⟨r,seen⟩

/-- The virtual trapdoor of a nonempty opening: heap below level 22 kept; the opened quartets' level-22 siblings
copied from the group nodes; their rebuilt blocks (`32 L + 512 + 1024 g`) hold the inverses of their group
replies; the opened salts are the linked salts. -/
theorem end_components (hc : HeaderFacts) (o : Oracle) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions)
    (nz : 0<p.card) :
    let t:=virtualTd (passEnd o td p)
    (∀ n, n<4194304 → Opening.trapdoorHeap (s:=actual) t n=Opening.trapdoorHeap (s:=actual) td n) ∧
    (∀ i∈p, Opening.trapdoorHeap (s:=actual) t (4194304+(i.val/4^^^1))=
      td.extractLsb' (8*(8*nodeWordOf (i.val/4^^^1)-trapdoorBase)) 256) ∧
    (∀ i∈p, t.extractLsb' (8*(32*LENGTH+512+1024*(i.val/4))) 1600=o.permutation.symm (groupReply td (i.val/4))) ∧
    (∀ i∈p, trapdoorSalt (s:=actual) t i=linkedSalts o (keyOf td) i) := by
  obtain ⟨r,seen⟩ := pass_end_facts hc o td p nz
  exact ⟨kept_heap td p _ _ r,placed_sibling o td p _ _ seen,placed_block o td p _ _ seen,
    selected_salt o _ td p _ seen⟩

/-- The opener's virtual trapdoor (the memory after the prefix pass; `td` itself for an empty opening). -/
noncomputable def virtualFor (o : Oracle) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) :=
  if p.card=0 then td else virtualTd (fixedPass o p (keyOf td) p.card 0 (header (actual.initialState .opening (td,p))))

theorem virtual_end (o : Oracle) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (nz : 0<p.card) :
    virtualFor o td p=virtualTd (passEnd o td p) := by
  simp [virtualFor,passEnd,Nat.ne_of_gt nz]

/-- The group node a level-22 sibling copy reads: the parity slice of the group reply. -/
theorem node_slice (td : BitVec (8*actual.sizes.trapdoor)) (h : Nat) (hh : h<4194304) :
    td.extractLsb' (8*(8*nodeWordOf h-trapdoorBase)) 256=quartetNode h (groupReply td h) := by
  have tb : trapdoorBase=4294971424 := rfl
  have wide (start : Nat) (x : BitVec 1600) :
      @BitVec.extractLsb' PERMUTATION_WIDTH start 256 x = @BitVec.extractLsb' 1600 start 256 x := rfl
  unfold quartetNode groupReply groupReplyOffset nodeWordOf blockWord
  by_cases ev : h%2=0
  · simp only [ev,ite_true]
    rw [wide, nested_slice _ (by omega : 0+256≤1600)]
    refine congrArg (fun k => BitVec.extractLsb' k 256 td) ?_
    rw [tb]; unfold LENGTH LOG_LENGTH; omega
  · simp only [ev,ite_false]
    rw [wide, nested_slice _ (by omega : 1344+256≤1600)]
    refine congrArg (fun k => BitVec.extractLsb' k 256 td) ?_
    rw [tb]; unfold LENGTH LOG_LENGTH; omega

/-- Leaf `j` of a quartet payload sits at bits `576 + 256 j` of its encoding (`0^72 ‖ d0 d1 d2 d3`). -/
theorem payload_leaf (leaves : DigestTape) (g j : Nat) (hj : j<4) :
    (quartetEncode (Quartet.quartetPayload leaves g)).extractLsb' (576+256*j) 256=Quartet.leafAt leaves (4*g+j) := by
  unfold quartetEncode Quartet.quartetPayload
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  change (@BitVec.extractLsb' 1600 (576+256*j) 256 _).getLsbD b = _
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hb, decide_true, Bool.true_and]
  have h0 : ¬ (576+256*j+b < 576) := by omega
  simp only [h0, ite_false]
  rcases (show j=0 ∨ j=1 ∨ j=2 ∨ j=3 by omega) with rfl|rfl|rfl|rfl
  · simp only [show 576+256*0+b-576 = b by omega, Nat.mul_zero, Nat.add_zero, hb, ite_true]
  · simp only [show ¬ (576+256*1+b-576 < 256) by omega, ite_false, show 576+256*1+b-576-256 < 256 by omega, ite_true,
      show 576+256*1+b-576-256 = b by omega, hb]
  · simp only [show ¬ (576+256*2+b-576 < 256) by omega, show ¬ (576+256*2+b-576-256 < 256) by omega, ite_false,
      show 576+256*2+b-576-256-256 < 256 by omega, ite_true, show 576+256*2+b-576-256-256 = b by omega, hb]
  · simp only [show ¬ (576+256*3+b-576 < 256) by omega, show ¬ (576+256*3+b-576-256 < 256) by omega,
      show ¬ (576+256*3+b-576-256-256 < 256) by omega, ite_false, show 576+256*3+b-576-256-256-256 = b by omega]

/-- The opener's proof from the commit's trapdoor is the builder's proof. The writer reads every leaf digest of
an opened quartet from its rebuilt block, so no hypothesis on the trapdoor's original leaf slots is needed. -/
theorem opened_proof (hc : HeaderFacts) (o : Oracle) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions)
    (leaves : DigestTape)
    (heap : ∀ n, 0<n → n<4194304 → Opening.trapdoorHeap (s:=actual) td n =
      Quartet.upperHeap (Quartet.quartetLookup (BiPermutation.equiv Block o.permutation)) o.compression leaves n)
    (replies : ∀ g<4194304, groupReply td g=o.permutation (quartetEncode (Quartet.quartetPayload leaves g))) :
    proofFromTrapdoor (s:=actual) (virtualFor o td p) p =
      (Quartet.builder (Quartet.quartetLookup (BiPermutation.equiv Block o.permutation)) o.compression p
        (fun i => Permutation.LinkedSalt.salts (Permutation.LinkedSalt.schedule Permutation.LinkedSalt.period)
          o.permutation (keyOf td) i.val) leaves).2 := by
  apply proof_from_trapdoor_matches_virtual actual (virtualFor o td p) p _ o.compression leaves
    (fun i => linkedSalts o (keyOf td) i)
  · intro n pos hn
    by_cases empty : p.card=0
    · simp only [virtualFor,empty,ite_true]; exact heap n pos hn
    · rw [virtual_end o td p (by omega),(end_components hc o td p (by omega)).1 n hn]; exact heap n pos hn
  · intro i member
    have nz : 0<p.card := Finset.card_pos.mpr ⟨i,member⟩
    have ix := i.isLt; change _<16777216 at ix
    have hx := xor_one_lt (i.val/4) 22 (by omega) (by decide)
    rw [virtual_end o td p nz,(end_components hc o td p nz).2.1 i member,node_slice td _ hx,
      Quartet.upper_heap_leaf _ _ _ _ (by omega : i.val/4<4194304),replies _ hx]
    rfl
  · intro i member j hj
    have nz : 0<p.card := Finset.card_pos.mpr ⟨i,member⟩
    have ix := i.isLt; change _<16777216 at ix
    have block := (end_components hc o td p nz).2.2.1 i member
    rw [virtual_end o td p nz]
    unfold trapdoorLeaf
    rw [show 8*(32*LENGTH+512+1024*((4*(i.val/4)+j)/4)+72+32*((4*(i.val/4)+j)%4))=
        8*(32*LENGTH+512+1024*(i.val/4))+(576+256*j) by unfold LENGTH LOG_LENGTH; omega,
      ← nested_slice (width := 1600) _ (show 576+256*j+256≤1600 by omega), block, replies _ (by omega)]
    simp only [Equiv.symm_apply_apply]
    exact payload_leaf leaves (i.val/4) j hj
  · intro i member
    have nz : 0<p.card := Finset.card_pos.mpr ⟨i,member⟩
    rw [virtual_end o td p nz]; exact (end_components hc o td p nz).2.2.2 i member

end TwoPermutationPrototype.GroupedOpening
