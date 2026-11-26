import CommitGolfCandidate.ReconstructedCheckCapAcceptedData
import CommitGolfCandidate.ReconstructedCheckCapMembership
import CommitGolfCandidate.ReconstructedCommitParentsMemory

namespace CommitGolfCandidate.Reconstruction.CheckCapPhysical
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open TwoPermutationPrototype TwoPermutationPrototype.RV64
open CheckCapLowStore (cell)
open CheckGroupRadix (top)
open CheckCapScanData (W cap)
set_option maxRecDepth 15000
set_option maxHeartbeats 1250000

def digest (m : Memory) (id : Nat) : Binding.Digest := CheckEdge.digest (m (cell id)) (m (cell id+1))
  (m (cell id+2)) (m (cell id+3))
def address (id : Nat) := cap+32*id

theorem physical (s : MachineState) (id : Nat) : CommitParents.cell s (address id)=digest (memoryView s) id := by
  rw [CommitParents.cell_words _ _ (by unfold address cap;omega)]
  have word (i : Nat) : CommitParents.atWord s (address id+8*i)=memoryView s (cell id+i) := by
    change s.getMem (W (cap+32*id+8*i))=s.getMem (W (8*(cap/8+4*id+i)))
    congr 2;unfold cap;omega
  change ((CommitParents.atWord s (address id+8*2)++CommitParents.atWord s (address id+8*1))++CommitParents.atWord s (address id+8*0),
    CommitParents.atWord s (address id+8*3))=_
  rw [word 0,word 1,word 2,word 3];rfl

theorem congr (m n : Memory) (id : Nat) (same : ∀ i : Fin 4,m (cell id+i.val)=n (cell id+i.val)) :
    digest m id=digest n id := by
  unfold digest
  have a : m (cell id)=n (cell id):=same 0
  have b : m (cell id+1)=n (cell id+1):=same 1
  have c : m (cell id+2)=n (cell id+2):=same 2
  have e : m (cell id+3)=n (cell id+3):=same 3
  rw [a,b,c,e]

theorem agrees {m n : Memory} {id : Nat} (bounded : id<1024) (eq : LeafMemory.Agrees m n) :
    digest m id=digest n id :=
  congr _ _ _ (fun i=>eq _ (by unfold cell cap;have h:=i.isLt;omega))

theorem untouched (d w : Nat) (m : Memory) (xs : List Nat) (stream c id : Nat) (fresh : id∉xs) :
    digest (CheckCapRepair.result d w m xs stream c).data id=digest m id := by
  apply congr;intro i
  unfold CheckCapRepair.result
  have freshTop (j : Nat) (hj : j∈xs) : cell id+i.val≠top j := by
    have h : id≠j:=fun eq=>fresh (eq ▸ hj)
    change 524288+4*id+i.val≠524288+4*j+3;have hi:=i.isLt;omega
  rw [CheckCapRepair.result_frame _ _ _ _ _ _ freshTop]
  apply CheckCapAcceptedData.low_frame
  intro j hj k
  have h : id≠j:=fun eq=>fresh (eq ▸ hj)
  unfold cell cap;have ik:=i.isLt;have kk:=k.isLt;omega

private theorem tables (d : Nat) (pos : 0<d) (max : d≤9) :
    if d<8 then Encoding.lows d=240 ∧ Binding.radix d=2^48
      else Encoding.lows d=224 ∧ Binding.radix d=211*2^32 := by
  let x : Fin 9:=⟨d-1,by omega⟩
  have k:=(by decide : ∀ i : Fin 9,if i.val+1<8 then Encoding.lows (i.val+1)=240 ∧ Binding.radix (i.val+1)=2^48
    else Encoding.lows (i.val+1)=224 ∧ Binding.radix (i.val+1)=211*2^32) x
  rwa [show x.val+1=d by dsimp [x];omega] at k

theorem canonical (d : Nat) (m : Memory) (xs : List Nat) (stream c id : Nat) (pos : 0<d) (max : d≤9)
    (found : id∈xs) (unique : xs.Nodup) (ok : (CheckCapRepair.result d (Encoding.lows d) m xs stream c).valid=true) :
    Binding.Canonical d (digest (CheckCapRepair.result d (Encoding.lows d) m xs stream c).data id) := by
  let w:=Encoding.lows d
  let low:=CheckCapLowMemory.fill stream w xs c m
  let next:=c+w*xs.length
  have small : (low (top id)).toNat<2^(w-192):=CheckCapAcceptedData.low_top m xs stream c w id found
  have tt:=tables d pos max
  by_cases early : d<8
  · rw [ite_eq_left early] at tt
    change ((if d<8 then (⟨true,next,low⟩ : CheckGroupPlan.Result) else CheckGroupPlan.decode low xs stream next).data (top id)).toNat<Binding.radix d
    rw [ite_eq_left early,tt.2];change (low (top id)).toNat<2^48
    change (low (top id)).toNat<2^(Encoding.lows d-192) at small
    rw [tt.1] at small;exact small
  · rw [ite_eq_right early] at tt
    change (if d<8 then (⟨true,next,low⟩ : CheckGroupPlan.Result) else CheckGroupPlan.decode low xs stream next).valid=true at ok
    rw [ite_eq_right early] at ok
    obtain ⟨z,zsmall,high⟩:=CheckCapAcceptedData.decode_digit low xs stream next id unique ok
    change ((if d<8 then (⟨true,next,low⟩ : CheckGroupPlan.Result) else CheckGroupPlan.decode low xs stream next).data (top id)).toNat<Binding.radix d
    rw [ite_eq_right early,high,BitVec.or_comm]
    let depth : Fin 24:=⟨d-1,by omega⟩
    have equal : depth.val+1=d:=by dsimp [depth];omega
    have capLow : (low (top id)).toNat<2^32:=by change (low (top id)).toNat<2^(Encoding.lows d-192) at small;rw [tt.1] at small;exact small
    have zz : (W z).toNat<211:=by rw [BitVec.toNat_ofNat];omega
    have res:=CheckEdge.projected depth 0 0 0 (low (top id)) (W z) 32 211 (equal ▸ tt.2) capLow zz
    change (W z <<< (32:Nat) ||| low (top id)).toNat<Binding.radix (depth.val+1) at res
    rwa [equal] at res

end CommitGolfCandidate.Reconstruction.CheckCapPhysical
