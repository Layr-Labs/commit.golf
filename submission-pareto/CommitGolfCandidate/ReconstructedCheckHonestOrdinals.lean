import CommitGolfCandidate.ReconstructedCheckHonestRecord

namespace CommitGolfCandidate.Reconstruction.CheckHonestOrdinals
open CommitGolf CheckRecordABI CheckRecordSpec TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
set_option maxRecDepth 16000
set_option maxHeartbeats 1400000

theorem project (o : Oracle) (key : Generator.Key) (msg : Message) (input : CheckInput) (i : Fin input.positions.card)
    (proof : input.proof=Wire.bytes (Encoding.fields (LeafTree.tree o key msg) input.positions (HonestDelivery.salts o key input.positions)))
    (values : ∀ p, input.values p=msg p.val) :
    let idx := position input i
    let got := (lower o idx.val (Wire.unpackBytes input.proof) (cursor i.val) (entryWords (input.values idx))).1
    got.header=[0,0,0,0] ∧ got.node=LeafTree.tree o key msg 9 (CheckWalkValues.heap idx.val 9) := by
  let ps := input.positions
  let xs := ps.sort (·≤·)
  let idx := (position input i).val
  let tree := LeafTree.tree o key msg
  let a := OpeningRecordList.fields o key msg ps i.val
  let extra := (xs.drop (i.val+1)).flatMap (OpeningRecordExecution.record o key msg)
  let cap := CapSchedule.rest tree (CapEntry.flags ps) 9
  have idEq : OpeningLoopRegs.sequence ps i.val i.isLt=idx := (CheckLoader.sorted input i).symm
  have aBits : Wire.bits a=cursor i.val := OpeningRecordList.bits o key msg ps i.val (Nat.le_of_lt i.isLt)
  have all := OpeningRecordList.complete o key msg ps
  have takeAll : xs.take ps.card=xs := by
    have len : xs.length=ps.card := by simp [xs]
    rw [←len,List.take_length]
  have splitAt := congrArg (List.flatMap (OpeningRecordExecution.record o key msg)) (List.take_append_drop (i.val+1) xs)
  rw [List.flatMap_append] at splitAt
  have records : OpeningRecordList.fields o key msg ps ps.card=OpeningRecordList.fields o key msg ps (i.val+1)++extra := by
    change (xs.take ps.card).flatMap _=_
    rw [takeAll];exact splitAt.symm
  have full : Encoding.fields tree ps (HonestDelivery.salts o key ps)=
      a++(OpeningRecordExecution.record o key msg idx++(extra++cap)) := by
    rw [←CapIterate.concat,←all,records,OpeningRecordList.next _ _ _ _ _ i.isLt,idEq]
    simp only [List.append_assoc,a,cap];rfl
  have h := CheckHonestRecord.localRecord o key msg idx a (extra++cap)
  change (lower o idx (Wire.unpackBytes input.proof) (cursor i.val) (entryWords (input.values (position input i)))).1.header=_ ∧
    (lower o idx (Wire.unpackBytes input.proof) (cursor i.val) (entryWords (input.values (position input i)))).1.node=_
  rw [proof,Wire.unpack_encoded,full,values,←aBits];exact h

end CommitGolfCandidate.Reconstruction.CheckHonestOrdinals
