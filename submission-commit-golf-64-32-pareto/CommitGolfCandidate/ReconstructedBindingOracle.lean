import CommitGolfCandidate.ReconstructedBindingHazard
import CommitGolfCandidate.JointOracle241Hazards

namespace CommitGolfCandidate.Reconstruction.Binding
open CommitGolf CommitGolfCandidate.JointOracle241
set_option maxRecDepth 8192
set_option maxHeartbeats 900000

def pack (x : Digest) : BitVec 256 := x.2 ++ x.1
def unpack (v : BitVec 256) : Digest := (v.extractLsb' 0 192, v.extractLsb' 192 64)

@[simp] theorem unpack_pack (d : Digest) : unpack (pack d) = d := by
  exact Prod.ext (BitVec.extractLsb'_append_eq_right (a := d.2) (b := d.1))
    (BitVec.extractLsb'_append_eq_left (a := d.2) (b := d.1))

@[simp] theorem pack_unpack (v : BitVec 256) : pack (unpack v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [pack,unpack,BitVec.getLsbD_append,BitVec.getLsbD_extractLsb']
  split <;> (simp_all <;> omega)

def encodeKey (k : Key) : BitVec 512 := pack k.2 ++ pack k.1
def decodeKey (v : BitVec 512) : Key := (unpack (v.extractLsb' 0 256), unpack (v.extractLsb' 256 256))

@[simp] theorem decode_encode (k : Key) : decodeKey (encodeKey k) = k := by
  apply Prod.ext
  · exact (congrArg unpack (BitVec.extractLsb'_append_eq_right (a := pack k.2) (b := pack k.1))).trans (unpack_pack _)
  · exact (congrArg unpack (BitVec.extractLsb'_append_eq_left (a := pack k.2) (b := pack k.1))).trans (unpack_pack _)

@[simp] theorem encode_decode (v : BitVec 512) : encodeKey (decodeKey v) = v := by
  unfold encodeKey decodeKey
  simp only [pack_unpack]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_append,BitVec.getLsbD_extractLsb']
  split <;> (simp_all <;> omega)

def cacheFn (s : State) (k : BitVec 512) : Option (BitVec 256) := s.cache k

def table (s : State) : Table := fun k => (cacheFn s (encodeKey k)).map unpack
noncomputable def keys (s : State) : Finset Key := s.keys.image decodeKey

theorem table_covered (s : State) : Covers (keys s) (table s) := by
  classical
  intro k v hv
  apply Finset.mem_image.2
  refine ⟨encodeKey k,s.covers _ ?_,decode_encode k⟩
  intro missing
  change (cacheFn s (encodeKey k)).map unpack = some v at hv
  change cacheFn s (encodeKey k) = none at missing
  rw [missing] at hv
  cases hv

theorem keys_le (s : State) : (keys s).card ≤ s.keys.card := Finset.card_image_le

theorem table_store (s : State) (k : BitVec 512) (y : BitVec 256) :
    table (s.store k y) = put (table s) (decodeKey k) (unpack y) := by
  funext j
  by_cases eq : j = decodeKey k
  · subst j
    have stored : cacheFn (s.store k y) k = some y := OracleSpec.QueryCache.cacheQuery_self _ _ _
    simp [table, put, stored]
  · have different : encodeKey j ≠ k := fun e => eq (by simpa using congrArg decodeKey e)
    have old : cacheFn (s.store k y) (encodeKey j) = cacheFn s (encodeKey j) :=
      OracleSpec.QueryCache.cacheQuery_of_ne _ _ different
    simp [table, put, eq, old]

theorem table_fresh (s : State) (k : BitVec 512) (none : s.cache k = none) :
    table s (decodeKey k) = Option.none := by
  change cacheFn s k = Option.none at none
  simp [table,none]

theorem distinct_put (m : Table) (k : Key) (y : Digest) (safe : DistinctAnswers m)
    (novel : ∀ j, m j ≠ some y) : DistinctAnswers (put m k y) := by
  intro a b v ha hb
  by_cases ea : a = k <;> by_cases eb : b = k
  · exact ea.trans eb.symm
  · simp [put,ea] at ha
    exact False.elim (novel b (ha ▸ (by simpa [put,eb] using hb)))
  · simp [put,eb] at hb
    exact False.elim (novel a (hb ▸ (by simpa [put,ea] using ha)))
  · exact safe a b v (by simpa [put,ea] using ha) (by simpa [put,eb] using hb)

def Good (s : State) : Prop :=
  DistinctAnswers (table s) ∧ ¬ EndpointCollision (table s) ∧
  (TwoPermutationPrototype.Sampling.s3PinCallW 240).badSpec.Good s.trace

noncomputable def used (s : State) := mass (table s) + s.trace.length

theorem used_le (s : State) (good : Good s) : used s ≤ s.count := by
  have m := mass_bound _ _ good.1 (table_covered s)
  have keys := keys_le s
  have count := s.size
  unfold used; omega

theorem store_good (s : State) (k : BitVec 512) (y : BitVec 256)
    (good : Good s) (fresh : s.cache k = none)
    (ok : ¬ Reject (table s) (decodeKey k) (unpack y)) :
    Good (s.store k y) ∧ used (s.store k y) = used s + weight (table s) (decodeKey k) := by
  have novel : ∀ j, table s j ≠ some (unpack y) := fun _ h => ok (Or.inl ⟨_,h⟩)
  have newUnary : table s (unary (unpack y)) = none := by
    by_contra hn; exact ok (Or.inr (Or.inl hn))
  have noSelf : unary (unpack y) ≠ decodeKey k := fun h => ok (Or.inr (Or.inr (Or.inl h)))
  have noPay : ¬ EndpointCollision (put (table s) (decodeKey k) (unpack y)) :=
    fun h => ok (Or.inr (Or.inr (Or.inr h)))
  constructor
  · unfold Good
    rw [table_store]
    exact ⟨distinct_put _ _ _ good.1 novel,noPay,good.2.2⟩
  · unfold used
    rw [table_store, mass_put _ _ _ good.1 (table_fresh s k fresh) newUnary noSelf]
    change _ + _ + s.trace.length = _; omega

end CommitGolfCandidate.Reconstruction.Binding
