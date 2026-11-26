import CommitGolfCandidate.ReconstructedHonestRecordCheck
import CommitGolfCandidate.ReconstructedHonestNested
import CommitGolfCandidate.ReconstructedHonestBudget

namespace CommitGolfCandidate.Reconstruction.HonestRecordIteration
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp HonestProtected HonestRecordMemory HonestRecordShapes
open HonestCapPrices (Budget)
open CommitBlocks (addr)

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
attribute [local irreducible] ArtifactEncoding.decode

abbrev image := Artifact.submission.image .opening
def ValidChecks := ∀ (i : Fin 128) (k : Nat), HonestRecordCheck.checked i.val k=true

def ExitShape (i : Nat) := if i+1<128 then start (i+1) else capStart 128
def ExitPC (i : Nat) := if i+1<128 then addr 143 else addr 1429

private theorem finer (pc : Word) (h : HonestRecordCost.cut pc=true) : stopAt pc=true := by
  simp only [HonestRecordCost.cut,Bool.or_eq_true,beq_iff_eq] at h
  rcases h with rfl|rfl <;> decide

private theorem checkpoint_index (i : Nat) {pc : Word} {a : Shape} (h : nextShape i pc=some a) :
    pc=addr (HonestBinaryRank.index pc) := by
  by_contra no
  simp only [nextShape,ite_eq_left no,reduceCtorEq] at h

/-- One call of the actual unrolled encoder either starts its next record or enters the cap
exactly on record 128. Its count and cursor updates are certified alongside all protected RAM. -/
theorem record_step (checked : ValidChecks) (i : Fin 128) (s t : MachineState)
    (coins : Bool) (pc0 : s.pc=addr 143) (ready : Holds context (start i.val) s)
    (walk : HonestCuts.Reaches image coins HonestRecordCost.cut s t) :
    t.pc=ExitPC i.val ∧ Holds context (ExitShape i.val) t := by
  let Mid (s : MachineState) := ∃ k a, s.pc=addr k ∧ current i.val k=some a ∧ Holds context a s
  apply HonestNested.carry finer Mid (fun u => u.pc=ExitPC i.val ∧ Holds context (ExitShape i.val) u)
    (s := s) (t := t) _ ⟨143,start i.val,pc0,rfl,ready⟩ walk
  intro u v marked path
  obtain ⟨k,a,loc,shape,given⟩ := marked
  have cert := checked i k
  simp only [HonestRecordCheck.checked,shape] at cert
  obtain ⟨b,target,facts⟩ := HonestRegionBlocks.from_shape context Artifact.openingCode image
    (Eq.refl (ArtifactEncoding.decode 32 _)) (by decide) stopAt (nextShape i.val) 64 (addr k) a
    cert u v coins loc given path
  let j := HonestBinaryRank.index v.pc
  have aligned : v.pc=addr j := checkpoint_index _ target
  have equiv : (v.pc≠addr j)=False := propext (iff_false_intro (not_not_intro aligned))
  simp only [nextShape,show HonestBinaryRank.index v.pc=j from rfl,equiv,ite_false] at target
  constructor
  · intro finished
    simp only [HonestRecordCost.cut,Bool.or_eq_true,beq_iff_eq] at finished
    rcases finished with record | cap
    · have key : j=143 := by change HonestBinaryRank.index v.pc=143; rw [record]; rfl
      simp only [key,ite_true] at target
      split at target
      · rename_i more
        obtain rfl := Option.some.inj target
        exact ⟨by simpa only [ExitPC,ite_eq_left more] using record,by simpa only [ExitShape,ite_eq_left more] using facts⟩
      · cases target
    · have key : j=1429 := by change HonestBinaryRank.index v.pc=1429; rw [cap]; rfl
      simp only [key,show ¬(1429:Nat)=143 by decide,ite_false,ite_true] at target
      split at target
      · rename_i last
        obtain rfl := Option.some.inj target
        have done : ¬i.val+1<128 := by omega
        exact ⟨by simpa only [ExitPC,ite_eq_right done] using cap,by simpa only [ExitShape,last,show ¬(128:Nat)<128 by decide,ite_false] using facts⟩
      · cases target
  · intro inner
    have noRecord : j≠143 := by rintro he; rw [aligned,he] at inner; cases inner
    have noCap : j≠1429 := by rintro he; rw [aligned,he] at inner; cases inner
    simp only [ite_eq_right noRecord,ite_eq_right noCap] at target
    exact ⟨j,b,aligned,target,facts⟩

/-- Composition uses all reachable record endpoints and the exact ABI cardinality. -/
theorem score_from_record (checked : ValidChecks) (i : Fin 128) (s : MachineState)
    (pc0 : s.pc=addr 143) (ready : Holds context (start i.val) s) (tail : Nat)
    (cap : ∀ t, t.pc=addr 1429 → Holds context (capStart 128) t → Budget t true tail) :
    Budget s true ((128-i.val)*1190+tail) := by
  suffices loop : ∀ n (i : Fin 128), 128-i.val=n → ∀ s : MachineState,
      s.pc=addr 143 → Holds context (start i.val) s → Budget s true (n*1190+tail) from loop _ i rfl s pc0 ready
  intro n
  induction n with
  | zero => intro i impossible; have := i.isLt; omega
  | succ n ih =>
    intro i remaining s loc given
    have one := HonestRecordCost.record_path (n*1190+tail) s loc true (by
      intro t path
      have ⟨pcOut,memory⟩ := record_step checked i s t true loc given path
      by_cases more : i.val+1<128
      · simp only [ExitPC,ExitShape,ite_eq_left more] at pcOut memory
        exact ih ⟨i.val+1,more⟩ (show 128-(i.val+1)=n by omega) t pcOut memory
      · simp only [ExitPC,ExitShape,ite_eq_right more] at pcOut memory
        have finish := cap t pcOut memory
        exact HonestCapPrices.mono (by omega) finish)
    intro f r run
    have charge := one f r run
    omega

/-- Every supported ABI opening of a 128-position set spends at most 152,718
cycles through the complete lower-record loop, before cap processing. -/
theorem abi_records (checked : ValidChecks) (trap : HonestInputs.Trapdoor) (ps : Positions) (batch : ps.card=128)
    (tail : Nat) (cap : ∀ t, t.pc=addr 1429 → Holds context (capStart 128) t → Budget t true tail) :
    Budget (HonestInputs.initial trap ps) true (152718+tail) := by
  intro f r run
  obtain ⟨out,extended,less⟩ := HonestBudget.extend _ _ _ f 398 r run
  have front := HonestInputs.first_record trap ps (by omega) f
  rw [Nat.add_comm f 398,front.1,mem_support_bind_iff] at extended
  obtain ⟨next,inside,charge⟩ := extended
  rw [support_pure,Set.mem_singleton_iff] at charge
  have rest := score_from_record checked ⟨0,by decide⟩ _ front.2.1 (first_shape trap ps batch) tail cap f next inside
  rw [charge] at less
  change r.cycles≤398+next.cycles at less
  change next.cycles≤152320+tail at rest
  omega

end CommitGolfCandidate.Reconstruction.HonestRecordIteration
