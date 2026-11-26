import CommitGolfCandidate.ReconstructedCheckHonestWalk
import CommitGolfCandidate.ReconstructedOpeningDelivery
import CommitGolfCandidate.ReconstructedCheckLoader

namespace CommitGolfCandidate.Reconstruction.CheckHonestRecord
open CommitGolf RiscvZkvm.Rv64 Wire Encoding CheckWalkValues CheckHonestRadix CheckRecordSpec
open TwoPermutationPrototype TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open CommitBlocks (addr)
set_option maxRecDepth 18000
set_option maxHeartbeats 1600000

private theorem trim (x : BitVec 256) : Binding.unpack (truncDigestW 240 x)=Binding.project 24 (Binding.unpack x) := by
  apply Prod.ext <;> apply BitVec.eq_of_toNat_eq
  · change ((x.toNat%2^240)%2^256 >>> 0)%2^192=(x.toNat >>> 0)%2^192
    rw [Nat.shiftRight_zero,Nat.shiftRight_zero];omega
  · rw [Binding.project_hi,show Binding.radix 24=2^48 by decide]
    simp only [Binding.unpack,truncDigestW,BitVec.extractLsb'_toNat,BitVec.toNat_ofNat,Nat.shiftRight_eq_div_pow];omega

private theorem leaf (o : Oracle) (key : Generator.Key) (msg : Message) (idx : Index) (stream c : Nat)
    (salt : CheckRecordHeader.salt stream c=saltWords (HidingTape.actualTape o.permutation key idx)) :
    CheckRecordSpec.leaf o idx stream c (entryWords (msg idx))=LeafTree.tree o key msg 24 (heap idx 24) := by
  have leafIdx : LeafTree.leafNumber (heap idx 24)=idx := by
    apply Fin.ext;change ((2^24+idx.val)/1-2^24)%2^24=idx.val
    rw [Nat.div_one,Nat.add_sub_cancel_left,Nat.mod_eq_of_lt (show idx.val<2^24 from idx.isLt)]
  change Binding.unpack (truncDigestW 240 (outputDigest (o.permutation (CheckLeafCall.request o idx _ _ 1))))=
    LeafTree.digest (LeafContent.lastReply o key msg (LeafTree.leafNumber (heap idx 24)))
  rw [salt,leafIdx,trim,LeafProjection.projected_digest,LeafTape.digest]
  rfl

private theorem tapeBound (o : Oracle) (key : Generator.Key) (idx : Index) :
    (HidingTape.actualTape o.permutation key idx).toNat<2^120 := by
  let x := HidingTape.generatedSalts o.permutation key idx
  change (x.setWidth 128).toNat<2^120
  rw [BitVec.toNat_setWidth];exact Nat.lt_of_le_of_lt (Nat.mod_le ..) x.isLt

theorem localRecord (o : Oracle) (key : Generator.Key) (msg : Message) (idx : Index) (a b : List Field) :
    let t := LeafTree.tree o key msg
    let s := HidingTape.actualTape o.permutation key idx
    let bits := Wire.pack (a++(Encoding.record t idx s++b))
    let val := (lower o idx bits (Wire.bits a) (entryWords (msg idx))).1
    val.header=[0,0,0,0] ∧ val.node=t 9 (heap idx 9) := by
  let t := LeafTree.tree o key msg
  let salt := HidingTape.actualTape o.permutation key idx
  let hdr := recordHeader t idx
  let before : List Field := [⟨salt.toNat,64⟩,⟨salt.toNat >>> 64,56⟩,⟨hdr,64⟩,⟨hdr >>> 64,38⟩]
  let c := Wire.bits a
  let stream := Wire.pack (a++(Encoding.record t idx salt++b))
  have rowsEq : Encoding.record t idx salt=before++rows t idx 15 := rfl
  have value := CheckHonestFields.four a (rows t idx 15++b) ⟨salt.toNat,64⟩ ⟨salt.toNat >>> 64,56⟩
    ⟨hdr,64⟩ ⟨hdr >>> 64,38⟩ (by change 64≤64;decide) (by change 56≤64;decide)
    (by change 64≤64;decide) (by change 38≤64;decide)
  have ns : stream=Wire.pack (a++(before++(rows t idx 15++b))) := by dsimp only [stream];rw [rowsEq,List.append_assoc]
  let opened := Wire.pack (a++(before++(rows t idx 15++b)))
  change
    HonestStream.get opened c 64=salt.toNat%2^64 ∧
    HonestStream.get opened (c+64) 56=(salt.toNat >>> 64)%2^56 ∧
    HonestStream.get opened (c+120) 64=hdr%2^64 ∧ HonestStream.get opened (c+184) 38=(hdr >>> 64)%2^38 at value
  have openedEq : opened=stream := ns.symm
  rw [openedEq] at value
  obtain ⟨v0,v1,v2,v3⟩ := value
  have small : salt.toNat<2^120 := tapeBound o key idx
  have nonce : CheckRecordHeader.salt stream c=saltWords salt := by
    funext i;fin_cases i
    · change BitVec.ofNat 64 (HonestStream.get stream c 64)=salt.extractLsb' 0 64
      rw [v0];apply BitVec.eq_of_toNat_eq;simp [BitVec.extractLsb'_toNat]
    · change BitVec.ofNat 64 (HonestStream.get stream (c+64) 56)=salt.extractLsb' 64 64
      rw [v1];apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat,BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow];omega
  let start := CheckRecordSpec.start o idx stream c (entryWords (msg idx))
  have cur : start.cursor=Wire.bits (a++before) := by rw [Wire.bits_append];rfl
  have hg : hdr<2^102 := RecordDigits.header_bound t (CheckHonestWalk.canonical o key msg) idx
  have head : HonestDivision.assemble 0 start.header=number t idx 15 := by
    change HonestDivision.assemble 0 (HonestDivision.fromFields (HonestStream.get stream (c+120) 64) (HonestStream.get stream (c+184) 38))=_
    rw [v2,v3,header t (CheckHonestWalk.canonical o key msg) idx]
    change _=hdr
    simp only [HonestDivision.fromFields,HonestDivision.assemble,HonestDivision.limb,Nat.zero_mul,Nat.zero_add,Nat.shiftRight_eq_div_pow];omega
  have path : stream=Wire.pack ((a++before)++(rows t idx 15++b)) := by rw [List.append_assoc];exact ns
  exact CheckHonestWalk.run o key msg idx 15 (by decide) (a++before) b start stream path cur rfl
    (boundedHead stream c) head (leaf o key msg idx stream c nonce)

end CommitGolfCandidate.Reconstruction.CheckHonestRecord
