import CommitGolfCandidate.ReconstructedCheckRecordFrontier
import CommitGolfCandidate.ReconstructedCheckCapHonestStep

namespace CommitGolfCandidate.Reconstruction.CheckRecordCap
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding CheckRecordABI CheckRecordSlots CheckRecordLedger CheckRecordFrontier
open CheckCapLevel TwoPermutationPrototype.Sampling
set_option maxRecDepth 12000
set_option maxHeartbeats 1100000

theorem source {o : Oracle} {input : CheckInput} {a : Slots} {rs : List PublicRow} {s : MachineState}
    (h : Ledger o input input.positions.card a rs) (sh : Holds s a)
    (id : Nat) (bottom : 2^9 ≤ id) (top : id<2^(9+1)) (live : Live (CapEntry.flags input.positions) 9 id=true) :
    ∃ i : Ordinal input,slot input i=id ∧ node s id=(CheckRecordLedger.view o input i).node ∧ Canonical 9 (CheckRecordLedger.view o input i).node := by
  let j:=id-512
  have lim : j<512:=by dsimp [j];omega
  have eq : 512+j=id:=by dsimp [j];omega
  have active : CapEntry.flags input.positions j=true:=live
  obtain ⟨i,key,known,canonical⟩:=cells h sh j lim active
  rw [eq] at key known
  exact ⟨i,key,known,canonical⟩

theorem canonical {o : Oracle} {input : CheckInput} {a : Slots} {rs : List PublicRow} {s : MachineState}
    (h : Ledger o input input.positions.card a rs) (sh : Holds s a) :
    ∀ id : Nat,2^9 ≤ id→id<2^(9+1)→Live (CapEntry.flags input.positions) 9 id=true→Canonical 9 (node s id) := by
  intro id lo hi live;obtain ⟨_,_,nodeEq,good⟩:=source h sh id lo hi live;exact nodeEq.symm ▸ good

theorem honestKnown {o : Oracle} {input : CheckInput} {a : Slots} {rs : List PublicRow} {s : MachineState}
    (h : Ledger o input input.positions.card a rs) (sh : Holds s a) (key : Generator.Key) (msg : Message)
    (proof : input.proof=Wire.bytes (Encoding.fields (LeafTree.tree o key msg) input.positions (HonestDelivery.salts o key input.positions)))
    (values : ∀ p,input.values p=msg p.val) : CheckCapHonestStep.Known (LeafTree.tree o key msg) (CapEntry.flags input.positions) 9 s := by
  intro id lo hi live
  obtain ⟨i,atId,stored,_⟩:=source h sh id lo hi live
  exact stored.trans ((CheckHonestOrdinals.project o key msg input i proof values).2.trans (congrArg (LeafTree.tree o key msg 9) atId))

end CommitGolfCandidate.Reconstruction.CheckRecordCap
