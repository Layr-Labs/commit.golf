import CommitGolf.Programs

namespace CommitGolfCandidate
open CommitGolf
abbrev Nonce192 := BitVec 192

def expandNonce192 (nonce : Nonce192) : BitVec 256 := nonce.zeroExtend 256

theorem expand_nonce_injective : Function.Injective expandNonce192 := by
  intro a b equal
  apply BitVec.eq_of_getLsbD_eq
  intro bit below
  have same := congrArg (fun value : BitVec 256 => value.getLsbD bit) equal
  simpa [expandNonce192,below,show bit<256 by omega] using same


def expandNonceVector (salt : Index → Nonce192) : Index → BitVec 256 :=
  fun index => expandNonce192 (salt index)

theorem expand_nonce_vector_update (salt : Index → Nonce192) (hidden : Index) (fresh : Nonce192) :
    expandNonceVector (Function.update salt hidden fresh)=
      Function.update (expandNonceVector salt) hidden (expandNonce192 fresh) := by
  funext index
  by_cases same : index=hidden
  · subst index
    simp [expandNonceVector]
  · simp [expandNonceVector,Function.update_of_ne same]


def nonceOffset (index : BitVec 64) : BitVec 64 := ((index<<<1)+index)<<<3

theorem nonce_offset_mul (index : BitVec 64) : nonceOffset index=index*24 := by
  unfold nonceOffset
  rw [BitVec.shiftLeft_add_distrib,←BitVec.shiftLeft_add,
    ←BitVec.mul_twoPow_eq_shiftLeft,←BitVec.mul_twoPow_eq_shiftLeft,←BitVec.mul_add]
  rfl

theorem nonce_offset_toNat (index : BitVec 64) (bounded : index.toNat<2^24) :
    (nonceOffset index).toNat=24*index.toNat := by
  rw [nonce_offset_mul,BitVec.toNat_mul]
  change (index.toNat*24)%2^64=24*index.toNat
  rw [Nat.mod_eq_of_lt (by omega : index.toNat*24<2^64)]
  omega

end CommitGolfCandidate
