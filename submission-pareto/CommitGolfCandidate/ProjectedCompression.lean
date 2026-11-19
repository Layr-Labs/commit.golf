import CommitGolfCandidate.ProjectedCollisionROM
import CommitGolfCandidate.Model

/-! Internal tree nodes store a zero-extended 238-bit digest in a 240-bit field. -/
namespace CommitGolfCandidate.ShortTree
open CommitGolf

def padLow (x : Digest) : Digest := (0 : BitVec 16) ++ low240 x

def parentCompression (compress : Compression) : Compression := fun input => padLow (compress input)

theorem low240_padLow (digest : Digest) : low240 (padLow digest) = low240 digest := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [low240, padLow, lowBits, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h : i < 238
  · have h' : i < 240 := by omega
    simp [h, h', hi]
  · simp [h]

def parentOracle (oracle : Oracle) : Oracle :=
  { oracle with compression := parentCompression oracle.compression }

end CommitGolfCandidate.ShortTree
