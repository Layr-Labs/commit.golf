import CommitGolfCandidate.ReconstructedOpeningRecordSalt
import CommitGolfCandidate.ReconstructedOpeningView

namespace CommitGolfCandidate.Reconstruction.OpeningSaltStream
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open Generator OpeningPut OpeningRecordSalt LeafContent

def firstFields (salt : BitVec 128) : List Wire.Field := [⟨salt.toNat,64⟩,⟨salt.toNat >>> 64,56⟩]

private theorem words (o : Oracle) (k : Key) (i : Index) :
    let a := tapeReply o k i
    let l := laneOf i
    let salt := HidingTape.actualTape o.permutation k i
    (replyWords a (LeafNonce.firstWord l)).toNat=salt.toNat%2^64 ∧
      (replyWords a (LeafNonce.nextWord l)).toNat%2^56=(salt.toNat >>> 64)%2^56 := by
  let a := tapeReply o k i
  let l := laneOf i
  let salt := HidingTape.actualTape o.permutation k i
  have h := LeafNonce.pair a l
  rw [LeafTape.salt o k i] at h
  have l0 := congrFun h (0:Fin 2)
  have l1 := congrFun h (1:Fin 2)
  change replyWords a (LeafNonce.firstWord l) = salt.extractLsb' 0 64 at l0
  change replyWords a (LeafNonce.nextWord l) &&& 0x00ffffffffffffff#64=salt.extractLsb' 64 64 at l1
  constructor
  · rw [l0,BitVec.extractLsb'_toNat];rfl
  · have v := congrArg BitVec.toNat l1
    rw [BitVec.toNat_and,BitVec.extractLsb'_toNat] at v
    change (replyWords a (LeafNonce.nextWord l)).toNat &&& (2^56-1) = (salt.toNat >>> 64)%2^64 at v
    rw [Nat.and_two_pow_sub_one_eq_mod] at v
    have low := congrArg (· % 2^56) v
    simpa only [Nat.mod_mod,Nat.mod_mod_of_dvd _ (by decide : 2^56 ∣ 2^64)] using low

theorem serialized (o : Oracle) (k : Key) (i : Index) (m t : LeafModel.Model) (ord : Nat) (fs : List Wire.Field)
    (pre : OpeningQuery.Entry m ord i) (memory : Serialized m.mem (Wire.pack fs))
    (fits : (Wire.bits fs+64)/64<capacity) (result : Result o m t k ord (Wire.bits fs) i) :
    Serialized t.mem (Wire.pack (fs++firstFields (HidingTape.actualTape o.permutation k i))) := by
  let c := Wire.bits fs
  let a := tapeReply o k i
  let l := laneOf i
  let v := replyWords a (LeafNonce.firstWord l)
  let w := replyWords a (LeafNonce.nextWord l)
  let salt := HidingTape.actualTape o.permutation k i
  let f : Wire.Field := ⟨salt.toNat,64⟩
  let g : Wire.Field := ⟨salt.toNat >>> 64,56⟩
  obtain ⟨lo,hi⟩ := words o k i
  have physical : Serialized (answer o m ord i).mem (Wire.pack fs) := by
    intro j hj;rw [preserved_output o m ord i pre j hj];exact memory j hj
  have enough : c/64<capacity := by change (c+64)/64<capacity at fits;omega
  have first := serial_put _ _ c 64 v physical (Wire.pack_bound fs) v.isLt (by decide) enough
  have low : v.toNat=Wire.clipped f := lo
  rw [low,append_field] at first
  have advance : Wire.bits (fs++[f])=c+64 := by rw [Wire.bits_append];rfl
  have bound := Wire.pack_bound (fs++[f]);rw [advance] at bound
  have v56 : (OpeningSaltHigh.clip w).toNat=w.toNat%2^56 := by
    change (w.toNat%2^56)%2^64=_
    exact Nat.mod_eq_of_lt (by omega)
  have small : (OpeningSaltHigh.clip w).toNat<2^56 := by rw [v56];omega
  have second := serial_put _ _ (c+64) 56 (OpeningSaltHigh.clip w) first bound small (by decide) fits
  have high : (OpeningSaltHigh.clip w).toNat=Wire.clipped g := v56.trans hi
  rw [high,←advance,append_field] at second
  rw [result.memory]
  simpa only [advance,List.append_assoc,firstFields,List.cons_append,List.nil_append] using second

end CommitGolfCandidate.Reconstruction.OpeningSaltStream
