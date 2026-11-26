import CommitGolfCandidate.ReconstructedCheckCapLevelContract
import CommitGolfCandidate.ReconstructedCheckCapPhysical
import CommitGolfCandidate.ReconstructedCheckCapScan

namespace CommitGolfCandidate.Reconstruction.CheckCapFrames
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CheckCapLevel
open TwoPermutationPrototype TwoPermutationPrototype.RV64
open CheckCapScanData (W cap scratch active flag)
set_option maxRecDepth 16000
set_option maxHeartbeats 1300000

theorem trans {s t u : MachineState} (a : Frame s t) (b : Frame t u) : Frame s u :=
  fun q hq h=>(b q hq h).trans (a q hq h)

theorem readScan {s t : MachineState} (scan : CheckCapScanData.Frame s t) (q : Nat) (hq : q<2^33)
    (af : q<532480 ∨ 532608≤q) (as : q<8589934171 ∨ 8589934300≤q) : memoryView t q=memoryView s q := by
  have := word_address_value (by omega : q<2^61)
  apply scan (wordAddress q)
  · rw [this];unfold active;omega
  · rw [this];unfold scratch CheckCapScanData.fp;omega

theorem scan {s t : MachineState} (fr : CheckCapScanData.Frame s t) : Frame s t :=
  fun q hq h=>readScan fr q hq h.2.1 h.2.2.1

theorem bases {s t : MachineState} (fr : CheckCapScanData.Frame s t) : Bases (memoryView t) s := by
  constructor;intro id hi
  have eq : CheckCapPhysical.digest (memoryView t) id=CheckCapPhysical.digest (memoryView s) id := by
    apply CheckCapPhysical.congr;intro i
    have h:=i.isLt
    apply readScan fr <;> unfold CheckCapLowStore.cell cap <;> omega
  exact eq.trans (CheckCapPhysical.physical s id).symm

theorem parent {s t : MachineState} (lo hi : Nat) (small : hi≤1024)
    (fr : CheckParentHeap.Frame lo hi s t) : Frame s t := by
  intro q bound same
  refine fr q bound ?_ same.2.2.2.1 same.2.2.2.2
  have f:=same.1
  change q<524288 ∨ 528384≤q at f
  unfold CheckParentHeap.word;omega

theorem result (d w : Nat) (ids : List Nat) (m : Memory) (stream c : Nat) (valid : ∀ i∈ids,i<1024) :
    CheckCapLowMemory.Frame m (CheckCapRepair.result d w m ids stream c).data := by
  intro q small out
  have away (id : Nat) (member : id∈ids) : q≠CheckGroupRadix.top id:=by
    have b:=valid _ member
    change q≠524288+4*id+3
    change q<524288 ∨ 528384≤q at out;omega
  unfold CheckCapRepair.result
  rw [CheckCapRepair.result_frame _ _ _ _ _ _ away]
  exact CheckCapLowMemory.fill_frame m ids stream c w valid q small out

theorem parsed {s t : MachineState} {f : Nat→Bool} {d stream c : Nat}
    (valid : ∀ i∈CapSchedule.pending f d,i<1024)
    (out : LeafMemory.Agrees (memoryView t) (CheckCapLevel.parsed f d stream c (memoryView s)).data) :
    CheckCapLowMemory.Frame (memoryView s) (memoryView t) :=
  CheckCapLowMemory.trans (result _ _ _ _ _ _ valid) (CheckCapLowMemory.frame_of_agrees out)

theorem data {s t : MachineState} {stream : Nat} (fr : Frame s t) (src : Data s stream) : Data t stream := by
  constructor
  · intro d pos lim;apply Eq.trans _ (src.widths d pos lim)
    apply fr <;> simp only [clear,CheckCapLowMemory.Outside,CheckCapLowSetup.widthCell,cap] <;> omega
  · exact (fr CheckCapLowSetup.maskCell (by decide) (by unfold clear CheckCapLowMemory.Outside;decide)).trans src.mask
  · intro a v al stored
    have bounds : 2097560≤a ∧ a<2098152:=by unfold CheckParentRun.ro at stored;split_ifs at stored <;> simp_all <;> omega
    have val:=src.constants a v al stored
    have hit : wordAddress (a/8)=W a:=by unfold wordAddress;congr 1;omega
    change s.getMem (W a)=v at val
    change t.getMem (W a)=v
    rw [←hit] at val ⊢
    apply Eq.trans _ val
    exact fr (a/8) (by omega) (by simp only [clear,CheckCapLowMemory.Outside,cap];omega)
  · intro i hi;apply Eq.trans _ (src.proof i hi)
    apply fr <;> simp only [clear,CheckCapLowMemory.Outside,CheckCapLowMemory.proofBase,cap] <;> omega

theorem parsed_flag {s t : MachineState} (fr : CheckCapLowMemory.Frame (memoryView s) (memoryView t))
    (k : Nat) (hi : k<1024) : s.getByte (flag k)=t.getByte (flag k) := by
  have eq:=fr ((active+k)/8) (by unfold active;omega) (Or.inr (by unfold active cap;omega))
  unfold MachineState.getByte
  change extractByte (s.getMem (alignToDword (W (active+k)))) _=extractByte (t.getMem (alignToDword (W (active+k)))) _
  rw [OpeningCursor.aligned];exact congrArg (fun x=>extractByte x _) eq.symm

theorem parent_flag {s t : MachineState} {lo hi : Nat} (small : hi≤1024) (fr : CheckParentHeap.Frame lo hi s t)
    (k : Nat) (range : k<1024) : t.getByte (flag k)=s.getByte (flag k) := by
  let q:=(active+k)/8
  have a : 532480≤q ∧ q<532608:=by unfold q active;omega
  have eq:=fr q (by omega) (Or.inr (by unfold CheckParentHeap.word;omega)) (Or.inl (by change q<8589934144;omega))
    (Or.inl (by change q<8589934427;omega))
  change extractByte (t.getMem (alignToDword (W (active+k)))) _=extractByte (s.getMem (alignToDword (W (active+k)))) _
  rw [OpeningCursor.aligned];exact congrArg (fun x=>extractByte x _) eq

end CommitGolfCandidate.Reconstruction.CheckCapFrames
