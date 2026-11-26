import CommitGolfCandidate.ReconstructedOpeningHeaderRun
import CommitGolfCandidate.ReconstructedOpeningNodeStream

namespace CommitGolfCandidate.Reconstruction.OpeningHeader
open CommitGolf RiscvZkvm.Rv64 TwoPermutationPrototype.RV64 OpeningCursor OpeningPut
open OpeningWordFields
set_option maxRecDepth 16000

def fields (n : Nat) : List Wire.Field := [⟨n,64⟩,⟨n >>> 64,38⟩]

theorem serialized (x : Context) (q : LeafModel.Model) (ps : Positions) (trap : CommitStorage.Trapdoor)
    (ne : 0 < ps.card) (heap : Heap x.initial.mem trap ps) (o : Oracle) (k : Generator.Key) (msg : Message)
    (stored : CommitStorage.Stored o k msg trap) (fs : List Wire.Field) (bits : Wire.bits fs=x.cursor+120)
    (before : Serialized x.initial.mem (Wire.pack fs)) (room : (x.cursor+184)/64<capacity)
    (st : OpeningHeaderLow.Staged (s345 x) q (x.cursor+120)) :
    Serialized (to416 x q).mem (Wire.pack (fs++fields (Encoding.recordHeader (LeafTree.tree o k msg) x.index))) := by
  let n := partialHeader x 10
  let f : Wire.Field := ⟨n,64⟩
  let g : Wire.Field := ⟨n >>> 64,38⟩
  have same : Serialized (s345 x).mem (Wire.pack fs) := by
    intro j hj;rw [front_memory x _ (Or.inl (by dsimp [base,capacity] at *;omega))];exact before j hj
  have one := CapWriter.snoc (s345 x).mem fs f (W n) same rfl (Nat.le_refl 64)
    (by rw [bits];omega)
  have nb : Wire.bits (fs++[f])=x.cursor+184 := by rw [Wire.bits_append,bits];change _+64=_;omega
  have hi : (OpeningHeaderWrite.clip (W (n/2^64))).toNat=Wire.clipped g := by
    change ((n/2^64%2^64%2^38)%2^64)=(n >>> 64)%2^38
    rw [Nat.shiftRight_eq_div_pow];omega
  have two := CapWriter.snoc _ (fs++[f]) g _ one hi (by change 38≤64;decide) (by rwa [nb])
  rw [nb,bits] at two
  rw [memory x q room st,←prefix_tree x ps trap ne heap o k msg stored]
  simpa only [List.append_assoc,fields,List.cons_append,List.nil_append] using two

end CommitGolfCandidate.Reconstruction.OpeningHeader
