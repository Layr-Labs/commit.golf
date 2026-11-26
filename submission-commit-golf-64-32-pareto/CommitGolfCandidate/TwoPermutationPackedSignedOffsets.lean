import Init.Data.BitVec.Basic

namespace TwoPermutationPrototype.RV64

def packedNonceOffset (slot byte : Nat) : BitVec 12 := BitVec.ofNat 12 (16*(slot%256)+byte+2049)
def packedHeapOffset (slot : Nat) : BitVec 12 := BitVec.ofNat 12 (32*(slot%128)+2049)

end TwoPermutationPrototype.RV64
