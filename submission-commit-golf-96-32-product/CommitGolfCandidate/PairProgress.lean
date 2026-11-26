import CommitGolfCandidate.PairMap
import CommitGolfCandidate.BatchModel
namespace CommitGolfCandidate.PairCap.Batch
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 10000
set_option maxHeartbeats 300000

/-- Checker correctness needs only the exit and number of public calls. -/
def obs (o : Oracle) (fuel : Nat) (s : MachineState) : Exit × Nat :=
  let result := Late.Check.Normal.checkEvaluation o (execute Late.Check.Normal.checkerImage fuel s false)
  (result.1.exit,result.2)

def Runs (o : Oracle) (s t : MachineState) (steps calls : Nat) : Prop :=
  ∀ fuel, obs o (steps+fuel) s = ((obs o fuel t).1,calls+(obs o fuel t).2)

theorem runs_trans {o : Oracle} {s m t : MachineState} {a b q r : Nat}
    (first : Runs o s m a q) (second : Runs o m t b r) : Runs o s t (a+b) (q+r) := by
  intro fuel; rw [Nat.add_assoc,first,second]; simp [Nat.add_assoc]

theorem pureBlockRuns {o : Oracle} {s t : MachineState} {n cyc : Nat}
    (run : ∀ fuel, execute Late.Check.Normal.checkerImage (n+fuel) s false =
      (do let res ← execute Late.Check.Normal.checkerImage fuel t false
          return res.charge cyc 0)) : Runs o s t n 0 := by
  intro fuel
  simp only [obs,run,bind_pure_comp,Late.Check.Normal.check_evaluation_map,Nat.zero_add]
  rfl

def prefixNode (H : Compression) (input : CheckInput) (n : Nat) (u : Fin 256) : Option Digest :=
  ((List.range n).find? (fun r => openingIndex input.positions r / 65536 == u.val)).map
    (lowerHash H input)

/-- A successful record pass has a witness for every populated bucket, and
every previously checked record at that bucket agrees with its witness. -/
structure RecordInvariant (H : Compression) (input : CheckInput) (n : Nat) (s : MachineState) : Prop where
  bounded : n ≤ 128
  indexPtr : s.getReg .x24 = BitVec.ofNat 64 (7650414624 + 8*n)
  valuePtr : s.getReg .x8 = BitVec.ofNat 64 (7784632352 + 256*n)
  proofPtr : s.getReg .x25 = BitVec.ofNat 64 (12079599648 + 536*n)
  remaining : s.getReg .x27 = BitVec.ofNat 64 (128-n)
  scratch : s.getReg .x21 = 256
  depth : s.getReg .x30 = 16
  slots : s.getReg .x19 = 12079668256
  root : s.getReg .x26 = 4294971392
  pc : s.pc = if n=128 then 5276 else 4924
  table : ∀ u, storedAt s u = prefixNode H input n u
  consistent : ∀ r<n, ∀ u : Fin 256, openingIndex input.positions r/65536=u.val →
    prefixNode H input n u = some (lowerHash H input r)
  inputWords : ∀ a : Word, 32768≤a.toNat → a.toNat%8=0 → a.toNat+8≤MEMORY_BYTES →
    s.getMem a = (Late.submission.initialState .check input).getMem a
  gap : ∀ p : Fin 128, readBuffer s (16384+96*p.val+64) 32=0

theorem completedRecords (o : Oracle) (input : CheckInput) (s : MachineState)
    (completed : RecordInvariant o.compression input 128 s) :
    ∀ r<128, let i := openingIndex input.positions r
      (childrenAt o.compression input (i/131072)).child (i.testBit 16) = some (lowerHash o.compression input r) := by
  intro r hr
  let i := openingIndex input.positions r
  have b : i < 16777216 := opening_index_bound input.positions r
  let u : Fin 256 := ⟨i/65536,by omega⟩
  have got := completed.consistent r hr u rfl
  change ((firstAt input u.val).map (lowerHash o.compression input)) = some _ at got
  change (childrenAt o.compression input (i/131072)).child (i.testBit 16) = _
  simp only [Children.child,childrenAt,Nat.testBit_eq_decide_div_mod_eq]
  by_cases right : i/65536%2=1
  · rw [if_pos (by change decide (i/65536%2=1)=true; simp [right])]
    rw [show 2*(i/131072)+1=u.val by dsimp [u]; omega]
    exact got
  · rw [if_neg (by change ¬ decide (i/65536%2=1)=true; simp [right])]
    rw [show 2*(i/131072)=u.val by dsimp [u]; omega]
    exact got
end CommitGolfCandidate.PairCap.Batch
