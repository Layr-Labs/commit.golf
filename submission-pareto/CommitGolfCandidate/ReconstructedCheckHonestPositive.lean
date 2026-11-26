import CommitGolfCandidate.ReconstructedCheckHonestEndpoint
import CommitGolfCandidate.ReconstructedCheckCapInitial
import CommitGolfCandidate.ReconstructedCheckReady
import CommitGolfCandidate.ReconstructedCheckRecords
import CommitGolfCandidate.ReconstructedCheckRecordCap
import CommitGolfCandidate.ReconstructedCheckEmptyTrace
import CommitGolfCandidate.ReconstructedCheckTail

namespace CommitGolfCandidate.Reconstruction.CheckHonestPositive
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CheckRecorded CheckCapLevel CheckCapHonestStep
open TwoPermutationPrototype.Checker TwoPermutationPrototype.Sampling
set_option maxRecDepth 13000
set_option maxHeartbeats 1200000
attribute [local irreducible] execute ArtifactEncoding.decode
abbrev W:=BitVec.ofNat 64

theorem run (o : Oracle) (key : Generator.Key) (msg : Message) (input : CheckInput)
    (positive : input.positions.Nonempty) (size : input.proof.length≤8355061248)
    (gate : input.proof.length%8=0 ∧ CheckLaunchGate.minimum input.positions.card ≤ input.proof.length)
    (proof : input.proof=Wire.bytes (Encoding.fields (LeafTree.tree o key msg) input.positions (HonestDelivery.salts o key input.positions)))
    (values : ∀ p,input.values p=msg p.val) (commitment : input.commitment=Binding.pack (LeafTree.tree o key msg 0 1))
    :
    (checkObservation Artifact.submission o input).1.1.exit=.success ∧
      (checkObservation Artifact.submission o input).2≤CHECK_BUDGET input.positions.card := by
  let ps:=input.positions
  let tree:=LeafTree.tree o key msg
  let salts:=HonestDelivery.salts o key ps
  let fs:=Encoding.fields tree ps salts
  let stream:=Wire.unpackBytes input.proof
  let c:=CheckRecordSpec.cursor ps.card
  let endC:=Wire.bits fs
  have pos:=Finset.card_pos.mpr positive
  have max:=CheckLoader.positions_card_bound ps
  have ready:=CheckReady.start o input pos size
  rw [ite_eq_left gate] at ready
  obtain ⟨s,start,regs,count⟩:=ready
  obtain ⟨v,n,low,limN,records,lowLim,bad|⟨⟨a,adv,ledger⟩,calls⟩⟩:=
    CheckRecords.positive o input s regs pos count
  · exact False.elim (bad.2 (CheckRecordFrontier.honest o key msg input proof values))
  have nodes:=CheckRecordCap.honestKnown ledger adv.slots key msg proof values
  have canon (j : Nat) (hj : j<512) (lit : CapEntry.flags ps j=true) :
      Binding.Canonical 9 (node v (512+j)):=by
    obtain ⟨i,_,val,can⟩:=CheckRecordFrontier.cells ledger adv.slots j hj lit
    change Binding.Canonical 9 (CommitParents.cell v (4194304+32*(512+j)))
    rw [val];exact can
  have room : c+630000≤70000000000:=by change 3633*ps.card+630000≤70000000000;omega
  obtain ⟨m,u,t,hi,out,limM,_,hiLim,upper,frame,mem,tr⟩:=CheckCapInitial.nine o input v c (by simpa using adv.pc) adv.fp adv.sp adv.cursor adv.kept
    (CheckRecordFrontier.initial ledger adv.slots) canon room
  have nodesU : Known tree (CapEntry.flags ps) 9 u:=by
    intro id lo hi on;apply Eq.trans _ (nodes id lo hi on)
    exact CommitParents.cell_congr mem _
  have packed : stream=Wire.pack fs:=by change Wire.unpackBytes input.proof=_;rw [proof,Wire.unpack_encoded]
  have finish:=CheckCapHonest.nine o key msg ps positive u t out hi c stream tr salts packed rfl nodesU
  have endAt := CheckCapIterate.endState tr
  rw [finish.1] at endAt
  change Boundary (CapEntry.flags ps) stream 0 endC t at endAt
  have info:=CheckHonestEndpoint.transfer frame adv.kept
  have entry : CheckTail.Entry t endC input.proof.length stream:=⟨endAt.ready.pc,endAt.ready.static.sp,
    endAt.ready.static.fp,endAt.ready.static.bits,info.ret,info.length,info.stream⟩
  have len : input.proof.length=alignedBytes endC:=by rw [proof];exact Wire.byte_count fs
  have bitsBound : endC≤70000000000:=by rw [len] at size;unfold alignedBytes at size;omega
  have accepts : CheckTail.Accepts t endC input.proof.length stream:=
    ⟨len.symm,CheckHonestEndpoint.comparisons info _ finish.2 commitment,packed ▸ CheckHonestEndpoint.padding fs⟩
  obtain ⟨p,limP,terminal⟩:=CheckTail.run o t endC input.proof.length stream bitsBound (by omega) entry
  rw [ite_eq_left accepts] at terminal
  let rows:=low++hi
  have allStages : Segment o (835+n+m) (CheckLoader.initial input) t rows:=compose (compose start records) upper
  have pay : rows.length≤CHECK_BUDGET ps.card:=by
    change (low++hi).length≤100*ps.card;rw [List.length_append];change hi.length≤16*ps.card at hiLim
    change low.length≤84*ps.card at lowLim;omega
  have used : 835+n+m+p≤274877906944:=by change n≤4895*ps.card at limN;omega
  let extra:=274877906944-(835+n+m+p)
  have split : 274877906944=(835+n+m)+(p+extra):=by dsimp [extra];omega
  have last:=terminal extra
  have x:=last.1.trans (CheckTail.nonnegative input.proof.length (by omega))
  obtain ⟨charge,replay⟩:=allStages
  rw [CheckEmptyTrace.within o input size,split,replay]
  exact ⟨x,by change rows.length+(Binding.Machine.observation o (p+extra) t).2≤_;rw [last.2.2.1,Nat.add_zero];exact pay⟩

end CommitGolfCandidate.Reconstruction.CheckHonestPositive

