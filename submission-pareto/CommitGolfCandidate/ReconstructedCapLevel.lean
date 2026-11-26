import CommitGolfCandidate.ReconstructedCapLevelContract
import CommitGolfCandidate.ReconstructedCapLevelSetup
import CommitGolfCandidate.ReconstructedCapHeaderLoop
import CommitGolfCandidate.ReconstructedCapDepthScan

namespace CommitGolfCandidate.Reconstruction.CapLevel
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 HonestCapPlan HonestCapState HonestCapStages
open OpeningPut OpeningCursor
open CommitBlocks (addr)
set_option maxRecDepth 22000
set_option maxHeartbeats 2500000

theorem run (o : Oracle) (key : Generator.Key) (msg : Message) (trap : CommitStorage.Trapdoor) (ps : Positions)
    (stored : CommitStorage.Stored o key msg trap) (nonempty : 0<ps.card) : Contract o key msg trap ps := by
  intro f d positive small s fs start global rows buf room
  let dep : Fin 10 := ⟨d,by omega⟩
  let tree := LeafTree.tree o key msg
  let xs := CapSchedule.pending f d
  let lo := xs.flatMap (CapSchedule.low tree d)
  let hi := CapSchedule.headers tree d xs
  have upper : xs.length≤pairs d := by
    change (CapOrder.ids _ _ 0 (pairs d)).length≤_
    rw [CapOrder.prefix_length];exact HonestSizeSchedule.tally_le _ _
  have size : xs.length≤256 := upper.trans (width_bound d small)
  have cells : ∀ i∈xs, CommitParents.Cell d i := fun i found => CapOrder.id_cell f d positive small i found
  have fitsLow : Wire.bits (fs++lo)+192<capacity*64 := by
    rw [CapSchedule.split _ _ _ small positive] at room
    simp only [Wire.bits_append] at room ⊢
    change Wire.bits fs+(Wire.bits lo+Wire.bits hi+_) +192<_ at room
    omega
  have fitsHeaders : Wire.bits ((fs++lo)++hi)+192<capacity*64 := by
    rw [CapSchedule.split _ _ _ small positive] at room
    simp only [Wire.bits_append] at room ⊢
    change Wire.bits fs+(Wire.bits lo+Wire.bits hi+_) +192<_ at room
    omega
  obtain ⟨a,u,ha,scanned,found,globU,rowsU,slots,bufU⟩ := CapDepthScan.run o f d positive small s trap ps fs start global rows buf
  have known : HonestCapState.Common d u := found.base
  have packed : CapLevelData.Packed u trap ps f d xs fs := ⟨globU,rowsU,slots,bufU,known.2.1,known.2.2⟩
  obtain ⟨b,v,hb,prepared,dataV,skip,emit⟩ := CapLevelSetup.collected o dep positive xs upper u trap ps f fs found packed
  by_cases empty : xs=[]
  · have noFields : fields tree f d=[] := by
      change xs.flatMap _ ++ CapSchedule.headers tree d xs=[]
      rw [empty];unfold CapSchedule.headers
      split <;> rfl
    refine ⟨a+b,v,?_,CommitExact.compose scanned prepared,skip empty,dataV.common,dataV.rows,?_⟩
    · unfold cost;omega
    · change CapEvidence.Buffer v (fs++fields tree f d);rw [noFields,List.append_nil];exact dataV.buffer
  obtain ⟨pcV,localV⟩ := emit empty
  have count : 0<xs.length := List.length_pos_iff.mpr empty
  obtain ⟨c,t,hc,lowRun,pcT,localT,dataT⟩ := CapLowLoop.loop o key msg trap ps stored nonempty f dep positive xs size cells xs []
    rfl v (by rw [ite_eq_right empty];exact pcV) fs dataV localV fitsLow
  obtain ⟨h,z,hz,headerStart,dataZ,cheap,paid⟩ := CapLevelSetup.doneLow o dep positive xs count upper t trap ps f (fs++lo) pcT localT dataT
  have prefixRun := CommitExact.compose (CommitExact.compose (CommitExact.compose scanned prepared) lowRun) headerStart
  by_cases ordinary : d<8
  · have noHeaders : hi=[] := by unfold hi CapSchedule.headers;rw [ite_eq_right (show ¬8≤d by omega)]
    refine ⟨a+b+c+h,z,?_,prefixRun,cheap ordinary,dataZ.common,dataZ.rows,?_⟩
    · change a+b+c+h≤14+18*pairs d+26+60*xs.length+16+43*xs.length;omega
    · change CapEvidence.Buffer z (fs++(lo++hi));rw [noHeaders,List.append_nil];exact dataZ.buffer
  · have paidDepth : 8≤d := by omega
    obtain ⟨pcZ,locZ⟩ := paid paidDepth
    have active : hi=Encoding.capHeaders (CapSchedule.digit tree d) xs := by unfold hi CapSchedule.headers;rw [ite_eq_left paidDepth]
    rw [active] at fitsHeaders
    obtain ⟨k,end_,hk,headers,pcEnd,two,done_⟩ := CapHeaderLoop.loop o key msg trap ps stored nonempty f dep paidDepth xs size cells xs [] empty rfl
      z pcZ (fs++lo) dataZ locZ fitsHeaders
    have matched : Matches ⟨d,.finish⟩ end_ := ⟨pcEnd,⟨done_.common.source.frame,done_.depth,done_.one⟩,
      by simp only [localFacts,holds_cons,holds_nil,and_true];exact two⟩
    refine ⟨a+b+c+h+k,end_,?_,CommitExact.compose prefixRun headers,matched,done_.common,done_.rows,?_⟩
    · change a+b+c+h+k≤14+18*pairs d+26+60*xs.length+16+43*xs.length;omega
    · change CapEvidence.Buffer end_ (fs++(lo++hi))
      rw [←List.append_assoc,active];exact done_.buffer

end CommitGolfCandidate.Reconstruction.CapLevel
