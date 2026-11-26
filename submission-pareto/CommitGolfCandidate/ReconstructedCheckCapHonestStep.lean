import CommitGolfCandidate.ReconstructedCheckHonestCap
import CommitGolfCandidate.ReconstructedCheckCapPaths
import CommitGolfCandidate.ReconstructedCheckCapPhysical
import CommitGolfCandidate.ReconstructedCheckHonestWalk
import CommitGolfCandidate.ReconstructedCapIterate

namespace CommitGolfCandidate.Reconstruction.CheckCapHonestStep
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding CheckCapLevel CapSchedule
open TwoPermutationPrototype TwoPermutationPrototype.RV64
open CheckCapLowStore (cell)
set_option maxRecDepth 15000
set_option maxHeartbeats 1050000

def Known (tree : Encoding.Tree) (f : Nat→Bool) (d : Nat) (s : MachineState) :=
  ∀ id : Nat, 2^d ≤ id → id < 2^(d+1) → Live f d id=true→node s id=tree d id

private theorem join (m : Memory) (id : Nat) (x : Binding.Digest)
    (words : ∀ i : Fin 4,m (cell id+i.val)=CheckParentWords.digWord x i) : view m id=x := by
  have a : m (cell id)=CheckParentWords.digWord x 0:=words 0
  have b : m (cell id+1)=CheckParentWords.digWord x 1:=words 1
  have c : m (cell id+2)=CheckParentWords.digWord x 2:=words 2
  have d : m (cell id+3)=CheckParentWords.digWord x 3:=words 3
  rw [view,a,b,c,d,CheckParentWords.low _ _ (by decide),CheckParentWords.low _ _ (by decide),
    CheckParentWords.low _ _ (by decide),CheckParentWords.high]
  refine Prod.ext ?_ rfl
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [CheckEdge.digest,BitVec.getLsbD_append,BitVec.getLsbD_extractLsb']
  by_cases l : j<64 <;> by_cases n : j-64<64 <;>
    simp only [l,n,show j-64-64<64 by omega,decide_true,decide_false,ite_true,ite_false,
      Bool.true_and,Bool.false_and] <;> congr 1 <;> omega

theorem decode (tree : Encoding.Tree) (canon : RecordDigits.canonical tree) (f : Nat→Bool)
    (d stream : Nat) (pos : 0<d) (lim : d≤9) (m : Memory) (fs : List Wire.Field)
    (layout : stream=Wire.pack (fs++rest tree f d)) :
    let got:=parsed f d stream (Wire.bits fs) m
    got.valid=true ∧ got.cursor=Wire.bits (fs++CapLevel.fields tree f d) ∧
    ∀ id∈pending f d, view got.data id=tree d id := by
  let xs:=pending f d
  let w:=Encoding.lows d
  have no : xs.Nodup:=CheckCapMembership.nodup _ _ _ _
  have span : stream=Wire.pack (fs++(xs.flatMap (low tree d)++(headers tree d xs++rest tree f (d-1)))):=by
    rw [layout,split tree f d lim pos,List.append_assoc]
  have eval:=CheckHonestCap.recover tree canon d lim xs no fs (rest tree f (d-1)) m
  rw [←span] at eval
  let got:=parsed f d stream (Wire.bits fs) m
  have ok : got.valid=true:=eval.1
  have exactWords (id : Nat) (mem : id∈xs) : view got.data id=tree d id:=join _ _ _ (eval.2 id mem)
  have size : 192≤w:=by rcases CheckCapRepair.width d pos lim with a|a <;> change 192≤Encoding.lows d <;> omega
  have bits := Wire.flat_bits xs (low tree d) w (fun id=>by
    rw [low,Encoding.low_bits];change 192+(w-192)=w;omega)
  have hdr : Wire.bits (headers tree d xs)=(if 8≤d then 31*CheckGroupPlan.groups xs else 0):=by
    unfold headers;split
    · exact Encoding.cap_header_bits _ _
    · rfl
  refine ⟨ok,?_,exactWords⟩
  change (CheckCapHeaders.result d (CheckCapLowMemory.fill stream w xs (Wire.bits fs) m) xs stream _).cursor=_
  rw [CheckCapHeaders.cursor _ _ _ _ _ ok,Wire.bits_append,CapLevel.fields,Wire.bits_append]
  change _=Wire.bits fs+(Wire.bits (xs.flatMap (low tree d))+Wire.bits (headers tree d xs))
  rw [bits,hdr];exact Nat.add_assoc ..

theorem used_eq (f : Nat→Bool) (k p : Nat) (small : k<9) :
    CheckCapMembership.used f (k+1) p=Live f k p := by
  unfold CheckCapMembership.used CheckCapMembership.child Live
  rw [show 9-k=(9-(k+1))+1 by omega,HonestSizeSchedule.row];rfl

theorem select_eq (f : Nat→Bool) (k p : Nat) (lo : 2^k≤p) (side : Bool) :
    CheckCapMembership.child f (k+1) p side=Live f (k+1) (2*p+side.toNat) := by
  unfold CheckCapMembership.child Live HonestCapPlan.pairs
  congr 1
  simp only [Nat.add_sub_cancel,Nat.pow_succ];omega

theorem step (o : Oracle) (key : Generator.Key) (msg : Message) (f : Nat→Bool) (k stream : Nat) (lim : k<9)
    (s u : MachineState) (log : List TwoPermutationPrototype.Sampling.PublicRow) (m : Memory) (fs : List Wire.Field)
    (layout : stream=Wire.pack (fs++rest (LeafTree.tree o key msg) f (k+1)))
    (bases : Bases m s) (known : Known (LeafTree.tree o key msg) f (k+1) s)
    (good : Passed o f stream (k+1) (Wire.bits fs) s u log m) :
    Known (LeafTree.tree o key msg) f k u := by
  let tree:=LeafTree.tree o key msg
  let d:=k+1
  let xs:=pending f d
  let got:=parsed f d stream (Wire.bits fs) m
  have vals:=decode tree (CheckHonestWalk.canonical o key msg) f d stream (by omega) (by omega) m fs layout
  intro p lo hi live
  have on : CheckCapMembership.used f d p=true:=(used_eq f k p lim).trans live
  have pair : 2^d=2*2^k := by unfold d;rw [Nat.pow_succ,Nat.mul_comm]
  have tot : 2^(d+1)=2*2^d := by rw [Nat.pow_succ,Nat.mul_comm]
  have limit : 2^(d+1)≤1024:= Nat.pow_le_pow_right (n:=2) (by decide) (show d+1≤10 by omega)
  have ch (side : Bool) : view got.data (2*p+side.toNat)=tree d (2*p+side.toNat) := by
    let id:=2*p+side.toNat
    have pick:=CheckCapMembership.decision f d p (by omega) lo (by change p<2*2^k;omega) side
    by_cases mem : id∈xs
    · exact vals.2.2 _ mem
    · have usedChild : CheckCapMembership.child f d p side=true:=by
        cases h : CheckCapMembership.child f d p side with
        | false=>exact False.elim (mem (pick.mpr ⟨on,h⟩))
        | true=>rfl
      have yes : Live f d id=true:=(select_eq f k p lo side).symm.trans usedChild
      have bit : side.toNat≤1:=by cases side <;> decide
      have lower : 2^d ≤ id :=by dsimp [id];omega
      have upper : id < 2^(d+1) :=by dsimp [id];omega
      exact (CheckCapPhysical.untouched d (Encoding.lows d) m xs stream (Wire.bits fs) id mem).trans
        ((bases.same id (by omega)).trans (known id lower upper yes))
  have l : view got.data (2*p)=tree d (2*p):=ch false
  have r : view got.data (2*p+1)=tree d (2*p+1):=ch true
  have h:=good.stored p lo hi on
  change node u p=parent (oracleCompression o) k (view got.data (2*p)) (view got.data (2*p+1)) at h
  rw [l,r] at h
  exact h.trans (CommitParents.parent_eq _ _ k p (by omega)).symm

end CommitGolfCandidate.Reconstruction.CheckCapHonestStep

