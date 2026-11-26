import CommitGolfCandidate.ChainedEncoding
import CommitGolfCandidate.ChainedSchedule
namespace CommitGolfCandidate.Chained
set_option exponentiation.threshold 800

/-- Aligned binary-parent data. Its two children fill the low 512 bits of the query. -/
def plainInput (children : Seed) : Input := BitVec.ofNat 768 children.toNat

theorem plain_is_first (children : Seed) :
    plainInput children=canonicalEncoding.first ⟨0,by decide⟩ children := by
  change BitVec.ofNat 768 children.toNat=BitVec.ofNat 768 (2^512*firstTag ⟨0,by decide⟩+children.toNat)
  simp [firstTag]

theorem plain_disjoint_first (children other : Seed) (h : Height) (tagged : h.val≠0) :
    plainInput children≠canonicalEncoding.first h other := by
  rw [plain_is_first]
  intro e
  have t:=congrArg canonicalEncoding.tag e
  rw [canonicalEncoding.first_tag,canonicalEncoding.first_tag] at t
  exact tagged (congrArg Fin.val (congrArg Prod.fst (Option.some.inj t))).symm

theorem plain_disjoint_next (children : Seed) (h : Height) (j : Nat) (lo : 0<j) (hi : j<16) (digest : Output) :
    plainInput children≠canonicalEncoding.next h j digest := by
  rw [plain_is_first]
  intro e
  have t:=congrArg canonicalEncoding.tag e
  rw [canonicalEncoding.first_tag,canonicalEncoding.next_tag h j digest lo hi] at t
  have impossible:=congrArg Prod.snd (Option.some.inj t)
  exact (Nat.ne_of_gt lo) impossible.symm

theorem plain_class : calls ⟨0,by decide⟩=1 ∧ width ⟨0,by decide⟩=238 := by decide
end CommitGolfCandidate.Chained
