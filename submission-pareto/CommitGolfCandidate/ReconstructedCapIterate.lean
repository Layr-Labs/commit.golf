import CommitGolfCandidate.ReconstructedHonestCapTurn
import CommitGolfCandidate.ReconstructedHonestReadProof

namespace CommitGolfCandidate.Reconstruction.CapIterate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp HonestCapPlan HonestCapState
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open HonestSizeRows (Rows)
open CommitBlocks (addr)
set_option maxRecDepth 16384
attribute [local irreducible] ArtifactEncoding.decode execute

def budget : Nat→Nat
  | 0 => 0
  | d+1 => 58+121*pairs (d+1)+budget d

private theorem fee (f : Nat→Bool) (d : Nat) : CapLevel.cost f d+2≤58+121*pairs d := by
  have len := CapOrder.prefix_length f d (pairs d)
  have few := HonestSizeSchedule.tally_le (HonestSizeSchedule.single f (9-d)) (pairs d)
  change (CapSchedule.pending f d).length=HonestSizeSchedule.prefixCount f d (pairs d) at len
  change HonestSizeSchedule.prefixCount f d (pairs d)≤pairs d at few
  unfold CapLevel.cost;omega

private theorem fields_sum (tree : Encoding.Tree) (f : Nat→Bool) (d : Nat) (pos : 0<d) (small : d≤9) (fs : List Wire.Field) :
    (fs++CapLevel.fields tree f d)++CapSchedule.rest tree f (d-1)=fs++CapSchedule.rest tree f d := by
  rw [CapSchedule.split tree f d small pos,CapLevel.fields]
  simp only [List.append_assoc]

theorem sweep (o : Oracle) (key : Generator.Key) (msg : Message) (trap : CommitStorage.Trapdoor) (ps : Positions)
    (level : CapLevel.Contract o key msg trap ps) (f : Nat→Bool) (d : Nat) (pos : 0<d) (small : d≤9)
    (s : MachineState) (fs : List Wire.Field) (known : Matches ⟨d,.level⟩ s) (common : CapGlobal.Common s trap ps)
    (rows : Rows f d 0 s) (buf : CapEvidence.Buffer s fs)
    (room : Wire.bits (fs++CapSchedule.rest (LeafTree.tree o key msg) f d)+192<OpeningPut.capacity*64) :
    ∃ n t, n≤budget d ∧ CommitExact.Segment o image n s t ∧ t.pc=addr 1641 ∧ CapGlobal.Common t trap ps ∧
      CapEvidence.Buffer t (fs++CapSchedule.rest (LeafTree.tree o key msg) f d) := by
  let tree := LeafTree.tree o key msg
  induction d generalizing s fs with
  | zero => omega
  | succ d ih =>
    obtain ⟨a,u,limA,runA,matchU,commonU,rowsU,bufU⟩ := level f (d+1) pos small s fs known common rows buf room
    obtain ⟨b,v,limB,runB,matchV,commonV,rowsV,bufV⟩ := HonestCapTurn.next_level o f (d+1) pos small u trap ps _ matchU commonU rowsU bufU
    have boundary := fields_sum tree f (d+1) pos small fs
    simp only [Nat.add_one_sub_one] at boundary
    have fees := fee f (d+1)
    have here := CommitExact.compose runA runB
    cases d with
    | zero =>
      simp only [Nat.zero_add,ite_true] at matchV
      change (fs++CapLevel.fields tree f 1)++[]=fs++CapSchedule.rest tree f 1 at boundary
      rw [List.append_nil] at boundary
      exact ⟨a+b,v,by change (CapLevel.cost f 1)+2≤58+121*pairs 1 at fees;change a≤CapLevel.cost f 1 at limA;change a+b≤58+121*pairs 1+0;omega,here,matchV.atPc,commonV,boundary ▸ bufV⟩
    | succ d =>
      have no : ¬d+1+1=1 := by omega
      simp only [ite_eq_right no,Nat.add_one_sub_one] at matchV
      have lower := HonestSizeRows.descend rowsV (by omega) small
      simp only [Nat.add_one_sub_one] at lower
      obtain ⟨c,t,limC,runC,exit,commonT,bufT⟩ := ih (by omega) (by omega) v _ matchV commonV lower bufV
        (by rw [boundary];exact room)
      exact ⟨a+b+c,t,by change a+b+c≤58+121*pairs (d+1+1)+budget (d+1);omega,
        CommitExact.compose here runC,exit,commonT,boundary ▸ bufT⟩

def records (tree : Encoding.Tree) (ps : Positions) (salts : OpenedSalts ps) :=
  (ps.sort (·≤·)).flatMap (fun i => Encoding.record tree i (publicOpenedSalts salts i))

theorem concat (tree : Encoding.Tree) (ps : Positions) (salts : OpenedSalts ps) :
    records tree ps salts++CapSchedule.rest tree (CapEntry.flags ps) 9=Encoding.fields tree ps salts := by
  unfold CapSchedule.rest;rw [CapSchedule.start];rfl

/-- From the real cap entry, the fixed oracle produces the complete returned wire
proof in at most 62,395 further machine steps, including HALT. -/
theorem complete (o : Oracle) (key : Generator.Key) (msg : Message) (trap : CommitStorage.Trapdoor) (ps : Positions)
    (level : CapLevel.Contract o key msg trap ps) (salts : OpenedSalts ps) (s : MachineState)
    (ready : CapEntry.Ready s trap ps (records (LeafTree.tree o key msg) ps salts)) :
    ∃ n t c q, n≤62395 ∧
      (∀ fuel, fixedOracleRun o (execute image (n+fuel) s true)=pure (⟨.success,t,c,q⟩ : Execution)) ∧
      ∀ c' q', Artifact.submission.openingSucceeded ⟨.success,t,c',q'⟩=true ∧
        Artifact.submission.readProof ⟨.success,t,c',q'⟩=Wire.bytes (Encoding.fields (LeafTree.tree o key msg) ps salts) := by
  let tree := LeafTree.tree o key msg
  let fs := records tree ps salts
  have eq := concat tree ps salts
  have room := CapSchedule.span ps tree salts
  obtain ⟨a,u,limA,runA,matchU,commonU,rowsU,bufU⟩ := HonestCapTurn.entry o s trap ps fs ready
  obtain ⟨b,v,limB,runB,exit,commonV,bufV⟩ := sweep o key msg trap ps level (CapEntry.flags ps) 9 (by decide) (by decide)
    u fs matchU commonU rowsU bufU (by rw [←eq] at room;exact room)
  change CapEvidence.Buffer v (records tree ps salts++CapSchedule.rest tree (CapEntry.flags ps) 9) at bufV
  rw [eq] at bufV
  have width : (v.getReg .x7).toNat=Wire.bits (Encoding.fields tree ps salts) := by
    rw [bufV.cursor,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by unfold OpeningPut.capacity at room;omega)]
  obtain ⟨t,finish,_,out⟩ := HonestReadProof.profile o v tree ps salts exit commonV.source.stack commonV.source.saved width bufV.output
  obtain ⟨c,q,walk⟩ := CommitExact.compose runA runB
  refine ⟨a+b+23,t,c+23,q,?_,?_,out⟩
  · change b≤62353 at limB;omega
  · intro fuel
    rw [Nat.add_assoc (a+b) 23 fuel,walk,finish,map_pure]
    simp only [Execution.charge,Nat.add_zero]

end CommitGolfCandidate.Reconstruction.CapIterate
