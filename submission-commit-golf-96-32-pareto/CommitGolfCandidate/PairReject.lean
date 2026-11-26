import CommitGolfCandidate.PairAccess
import CommitGolfCandidate.PairRowRegs
import CommitGolfCandidate.PairRowLogic
namespace CommitGolfCandidate.PairCap.Batch
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 6000
set_option maxHeartbeats 250000
attribute [local irreducible] execute Late.Check.Normal.checkEvaluation readBuffer storedAt lowerHash

def Rejects (o : Oracle) (s : MachineState) (steps calls : Nat) := ∀ fuel, obs o (steps+fuel) s=(.failure,calls)

theorem runs_rejects {o : Oracle} {s t : MachineState} {a b q r : Nat} (run : Runs o s t a q)
    (reject : Rejects o t b r) : Rejects o s (a+b) (q+r) := by
  intro fuel;rw [Nat.add_assoc,run,reject]

def equalWords (s : MachineState) : Prop :=
  ∀ j<4, s.getMem (s.getReg .x21+BitVec.ofNat 64 (8*j))=s.getMem (s.getReg .x23+BitVec.ofNat 64 (8*j))

theorem comparedWords (o : Oracle) (input : CheckInput) (n : Nat) (s : MachineState)
    (h : HashedFrame o input n s) :
    equalWords (tested s) ↔ lowerHash o.compression input n = readBuffer s (cell (rowBucket input n).val) 32 := by
  let u := rowBucket input n
  have t := testInfo _ h.pc u h.index
  have ca : ∀ v : Fin 256, cell v.val % 8=0 := by decide
  rw [← h.digest,read_digest_eq_iff s s 256 _ (by decide) (ca u)]
  unfold equalWords
  simp only [t.2.1,t.2.2.1,h.scratch,MachineState.getMem,t.2.2.2,BitVec.ofNat_add]
  rfl

theorem compareAccess (o : Oracle) (input : CheckInput) (n : Nat) (s : MachineState)
    (h : HashedFrame o input n s) :
    (∀ j<4,accessValid ((tested s).getReg .x21+BitVec.ofNat 64 (8*j)) 8) ∧
    (∀ j<4,accessValid ((tested s).getReg .x23+BitVec.ofNat 64 (8*j)) 8) := by
  let u := rowBucket input n
  have t := testInfo _ h.pc u h.index
  rw [t.2.1,t.2.2.1,h.scratch]
  constructor
  · intro j hj;exact (show ∀ w : Fin 4,accessValid (256+BitVec.ofNat 64 (8*w.val)) 8 by decide) ⟨j,hj⟩
  · intro j hj;exact (show ∀ v : Fin 256, ∀ w : Fin 4,
      accessValid (BitVec.ofNat 64 (cell v.val)+BitVec.ofNat 64 (8*w.val)) 8 by decide) u ⟨j,hj⟩

theorem duplicateReject (o : Oracle) (input : CheckInput) (n : Nat) (s : MachineState) (h : HashedFrame o input n s)
    (seen : (bucketState s).getReg .x7≠0) (neq : ¬equalWords (tested s)) : Rejects o s 28 0 := by
  let b := bucketState s
  have pc := (bucketInfo s h.pc _ h.index).1
  have pass : (tested s).pc=5172 := by
    unfold tested afterTest;dsimp only [execInstrBr];simp only [beq_iff_eq,show (bucketState s).getReg .x0=0#64 from rfl]
    rw [if_neg (show (bucketState s).getReg .x7≠0#64 from seen)]; change (bucketState s).pc+4=5172;rw [pc];rfl
  have access := compareAccess _ _ _ _ h
  intro fuel
  obtain ⟨result,run,bad,_,q⟩ := top_check_root_rejects (tested s) 269 (Or.inl rfl) pass access.1 access.2 neq fuel false
  unfold obs
  rw [show 28+fuel=12+((15+fuel)+1) by omega,bucketRun _ h.pc (bucketAccess s _ h.index),edge268 b pc]
  have run' : execute Late.Check.Normal.checkerImage (15+fuel) (execInstrBr b (.BEQ .x7 .x0 56)) false=pure result := run
  rw [run']
  simp only [pure_bind,Late.Check.Normal.check_evaluation_pure,Execution.charge,bad]

end CommitGolfCandidate.PairCap.Batch
