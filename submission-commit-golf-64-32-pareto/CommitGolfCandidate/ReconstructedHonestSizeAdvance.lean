import CommitGolfCandidate.ReconstructedHonestScanBytes
import CommitGolfCandidate.ReconstructedHonestSizeRows
import CommitGolfCandidate.ReconstructedHonestSizeCursor

namespace CommitGolfCandidate.Reconstruction.HonestSizeAdvance
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 HonestCapPlan HonestCapStages HonestCapState
open HonestSizeSchedule HonestSizeRows HonestCapInvariant
open HonestFlagState (atByte code)
open HonestCapTables (w)
open HonestCapOperands (children)
open HonestCapRam (activeBase)

set_option maxRecDepth 32768
attribute [local irreducible] ArtifactEncoding.decode

private theorem pair {f : Nat→Bool} {s t : MachineState} {coins : Bool} {d j p : Nat}
    (known : Matches ⟨d,.scan j p⟩ s) (extra : Extra ⟨d,.scan j p⟩ s)
    (detail : HonestSizeCursor.detail d (.scan j p) s) (rows : Rows f d j s) (count : p=prefixCount f d j)
    (width : pairs d≤256) (next : j<pairs d) (le : p≤j) (path : Path coins s t) :
    t.getReg .x20=w (prefixCount f d (j+1)) ∧ Rows f d (j+1) t := by
  change holds s (children (pairs d+j)) at detail
  simp only [children,holds_cons,holds_nil,and_true] at detail
  let l := row f (9-d) (2*j)
  let r := row f (9-d) (2*j+1)
  have lo : s.getByte (s.getReg .x23)=code l := by
    rw [detail.1]
    change atByte s (2*(pairs d+j))=_
    rw [show 2*(pairs d+j)=2*pairs d+2*j by omega]
    exact rows.child _ (by omega)
  have hi : s.getByte (s.getReg .x16)=code r := by
    rw [detail.2]
    change atByte s (2*(pairs d+j)+1)=_
    rw [show 2*(pairs d+j)+1=2*pairs d+(2*j+1) by omega]
    exact rows.child _ (by omega)
  have common : Common d s := known.base
  have fields := known.fields
  simp only [localFacts,scanFacts,holds_cons,holds_nil,and_true] at fields
  have out := HonestScanBytes.execute _ _ _ known.atPc path ⟨p,by omega⟩ l r lo hi common.2.2 fields.2.1
    (extra.pointers (by simp)).1
  constructor
  · simpa only [count,prefixCount,tally,single,l,r] using out.1
  · apply scanned_pair rows width next
    intro k small
    have ptr : s.getReg .x24=HonestCapMetadata.scanPtr d j := extra.state
    have eq := out.2 _ (inSpan small)
    simp only [ptr,HonestCapMetadata.scanPtr,Nat.add_assoc,addr_eq small (show pairs d+j<1024 by omega)] at eq
    exact eq

private theorem ordinary {v w' : Node} {f : Nat→Bool} {s t : MachineState}
    (ok : legal v) (live : v.phase≠.returned) (other : pc v.phase≠1470)
    (rows : At f v s) (counts : rightCount f v.depth v.phase) (edge : w'∈next v.depth v.phase)
    (same : ∀ k, k<1024 → atByte t k=atByte s k) : At f w' t ∧ rightCount f w'.depth w'.phase := by
  obtain ⟨d,p⟩ := v
  have bits := bounds live ok
  have held := carry (rows live) bits.2.2.1 same
  cases p <;> simp only [next,List.mem_cons,List.not_mem_nil,or_false] at edge
  all_goals try contradiction
  case enter =>
    obtain rfl := edge
    have depth : d=9 := ok.2; subst d
    exact ⟨fun _ => held,trivial⟩
  case scanGuard k p =>
    obtain rfl := edge
    by_cases again : k<pairs d
    · simp only [ite_eq_left again]; exact ⟨fun _ => held,counts⟩
    · have upper : k≤pairs d := ok.2.2.1
      have done : k=pairs d := by omega
      simp only [ite_eq_right again]
      subst k; exact ⟨fun _ => held,counts⟩
  case finish =>
    obtain rfl := edge
    split
    · exact ⟨fun h => (h rfl).elim,trivial⟩
    · exact ⟨fun _ => descend held (by omega) bits.2.1,trivial⟩
  all_goals obtain rfl := edge
  all_goals try split
  all_goals exact ⟨fun _ => held,by first | exact counts | rfl | trivial⟩

theorem maintained {f : Nat→Bool} {v w' : Node} {s t : MachineState} {coins : Bool}
    (ok : legal v) (live : v.phase≠.returned) (known : Matches v s) (extra : Extra v s)
    (detail : HonestSizeCursor.detail v.depth v.phase s) (rows : At f v s)
    (counts : rightCount f v.depth v.phase) (path : Path coins s t)
    (edge : w'∈next v.depth v.phase) (matched : Matches w' t) :
    At f w' t ∧ rightCount f w'.depth w'.phase := by
  by_cases normal : pc v.phase≠1470
  · exact ordinary ok live normal rows counts edge (fun _ small =>
      HonestCapSpan.outsideScan v s t coins known extra ok live normal path _ (inSpan small))
  obtain ⟨d,phase⟩ := v
  cases phase <;> try (solve | norm_num [pc] at normal)
  case scan j p =>
    have bits := bounds live ok
    obtain ⟨_,_,width,idxBound,le⟩ := bits
    have out := pair known extra detail (rows live) counts width idxBound le path
    have size : prefixCount f d (j+1)<2^64 := by
      have upper := tally_le (single f (9-d)) (j+1)
      change j<pairs d at idxBound; unfold prefixCount; omega
    simp only [next,List.mem_cons,List.not_mem_nil,or_false] at edge
    rcases edge with rfl|rfl <;> refine ⟨fun _ => out.2,?_⟩
    all_goals
      have fields := matched.fields
      simp only [localFacts,scanFacts,holds_cons,holds_nil,and_true] at fields
      have eq := congrArg BitVec.toNat (fields.2.1.symm.trans out.1)
      simp only [W,w,BitVec.toNat_ofNat,Nat.mod_eq_of_lt size] at eq
      change j<pairs d at idxBound
      first | (change p=prefixCount f d (j+1); omega) | (change p+1=prefixCount f d (j+1); omega)

end CommitGolfCandidate.Reconstruction.HonestSizeAdvance
