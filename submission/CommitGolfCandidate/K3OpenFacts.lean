import CommitGolfCandidate.GroupOpenResume
import CommitGolfCandidate.GroupOpenHeaderSpec
import CommitGolfCandidate.K3GRBridge

/-! K3-lite opener facts: what the virtual trapdoor (the memory after the prefix pass) holds. -/
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

/-- The virtual trapdoor of a nonempty opening: heap below level 22 and every non-d3 leaf kept; the opened quartets'
level-22 siblings and even d3s rebuilt from the group replies; the opened salts are the linked salts. -/
theorem end_components (hc : HeaderFacts) (o : Oracle) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions)
    (nz : 0<p.card) :
    let t:=virtualTd (passEnd o td p)
    (∀ n, n<4194304 → Opening.trapdoorHeap (s:=actual) t n=Opening.trapdoorHeap (s:=actual) td n) ∧
    (∀ i : Index, ¬(i.val/4%2=0 ∧ i.val%4=3) → trapdoorLeaf (s:=actual) t i.val=trapdoorLeaf (s:=actual) td i.val) ∧
    (∀ i∈p, Opening.trapdoorHeap (s:=actual) t (4194304+(i.val/4^^^1))=
      td.extractLsb' (8*(8*nodeWordOf (i.val/4^^^1)-trapdoorBase)) 256) ∧
    (∀ i∈p, i.val/4%2=0 → trapdoorLeaf (s:=actual) t (4*(i.val/4)+3)=
      (o.permutation.symm (td.extractLsb' (8*(32*LENGTH+1024*(i.val/4)+168)) 1600)).extractLsb' 1344 256) ∧
    (∀ i∈p, trapdoorSalt (s:=actual) t i=linkedSalts o (keyOf td) i) := by
  obtain ⟨r,seen⟩ := pass_end_facts hc o td p nz
  exact ⟨kept_heap td p _ _ r,kept_leaf td p _ _ r,placed_sibling o td p _ _ seen,placed_d3 o td p _ _ seen,
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
    rw [wide, nested_slice _ (by omega : 1344+256≤1600)]
    refine congrArg (fun k => BitVec.extractLsb' k 256 td) ?_
    rw [tb]; unfold LENGTH LOG_LENGTH; omega
  · simp only [ev,ite_false]
    rw [wide, nested_slice _ (by omega : 0+256≤1600)]
    refine congrArg (fun k => BitVec.extractLsb' k 256 td) ?_
    rw [tb]; unfold LENGTH LOG_LENGTH; omega

theorem payload_top (leaves : DigestTape) (g : Nat) :
    (quartetEncode (Quartet.quartetPayload leaves g)).extractLsb' 1344 256=Quartet.leafAt leaves (4*g+3) := by
  unfold quartetEncode Quartet.quartetPayload
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  change (@BitVec.extractLsb' 1600 1344 256 _).getLsbD b = _
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hb, decide_true, Bool.true_and]
  have h1 : ¬ (1344+b < 576) := by omega
  have h2 : ¬ (1344+b-576 < 256) := by omega
  have h3 : ¬ (1344+b-576-256 < 256) := by omega
  have h4 : ¬ (1344+b-576-256-256 < 256) := by omega
  simp only [h1, h2, h3, h4, ite_false, show 1344+b-576-256-256-256 = b by omega]

theorem opened_proof (hc : HeaderFacts) (o : Oracle) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions)
    (leaves : DigestTape)
    (heap : ∀ n, 0<n → n<4194304 → Opening.trapdoorHeap (s:=actual) td n =
      Quartet.upperHeap (Quartet.quartetLookup (BiPermutation.equiv Block o.permutation)) o.compression leaves n)
    (stored : ∀ i : Index, ¬ ((i.val/4)%2=0 ∧ i.val%4=3) → trapdoorLeaf (s:=actual) td i.val=leaves i)
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
    rw [virtual_end o td p nz,(end_components hc o td p nz).2.2.1 i member,node_slice td _ hx,
      Quartet.upper_heap_leaf _ _ _ _ hx,replies _ hx]
    rfl
  · intro i member j hj
    have nz : 0<p.card := Finset.card_pos.mpr ⟨i,member⟩
    have ix := i.isLt; change _<16777216 at ix
    have comps := end_components hc o td p nz
    rw [virtual_end o td p nz]
    by_cases d3 : i.val/4%2=0 ∧ j=3
    · obtain ⟨ev,rfl⟩ := d3
      rw [comps.2.2.2.1 i member ev,
        show td.extractLsb' (8*(32*LENGTH+1024*(i.val/4)+168)) 1600=groupReply td (i.val/4) by
          unfold groupReply groupReplyOffset; simp [ev],
        replies _ (by omega)]
      simp only [Equiv.symm_apply_apply]
      exact payload_top leaves (i.val/4)
    · let x : Index := ⟨4*(i.val/4)+j,by change _<16777216; omega⟩
      have keep : ¬(x.val/4%2=0 ∧ x.val%4=3) := by
        simp only [x]; intro h; apply d3; constructor <;> omega
      have kl := comps.2.1 x keep
      simp only [x] at kl
      rw [kl,stored x keep]
      unfold Quartet.leafAt; rw [dif_pos (by change _<16777216; omega)]
  · intro i member
    have nz : 0<p.card := Finset.card_pos.mpr ⟨i,member⟩
    rw [virtual_end o td p nz]; exact (end_components hc o td p nz).2.2.2.2 i member

end TwoPermutationPrototype.GroupedOpening
