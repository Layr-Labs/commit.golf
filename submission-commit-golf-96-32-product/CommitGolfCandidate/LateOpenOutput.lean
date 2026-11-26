import CommitGolfCandidate.LateOpenFinish
import CommitGolfCandidate.LateCommitFacts

namespace CommitGolfCandidate.Late.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

def rawLevels (td : Trapdoor) : Levels :=
  (List.range (LOG_LENGTH+1)).map fun d => (List.range (levelCount d)).map fun i =>
    slice td (nodeAddress d i) 32

def rawSalts (td : Trapdoor) : SaltTape := fun i => slice td (saltAddress i) 24

attribute [local irreducible] List.range readBuffer

private theorem raw_agrees (td : Trapdoor) : TrapdoorAgrees td (rawLevels td) (rawSalts td) := by
  refine ⟨?_,fun i => rfl⟩
  intro d hd j hj
  simp only [rawLevels,node,List.getElem?_map,List.getElem?_range (show d<LOG_LENGTH+1 by omega),
    Option.map_some,Option.getD_some,List.getElem?_range hj]

def result (td : Trapdoor) (p : Positions) : Execution :=
  ⟨.success,lastState (initial td p) p.card,cycles p.card,0⟩

private theorem abi (td : Trapdoor) (p : Positions) :
    submission.run .opening (td,p) = execute image 1099511627776 (initial td p) true := by
  have run (c : Submission) (t : BitVec (8*c.sizes.trapdoor)) :
      c.run .opening (t,p) = execute (c.image .opening) (c.steps .opening) (c.initialState .opening (t,p)) true := rfl
  exact run submission td

private theorem facts (td : Trapdoor) (p : Positions) (tree : Levels) (salts : SaltTape)
    (agrees : TrapdoorAgrees td tree salts) :
    Ready (initial td p) p.card ∧ HasBytes (result td p).state proofBase (opening tree salts p) := by
  have size : (indices p).length≤LENGTH := by simpa [indices] using Finset.card_le_univ p
  have n : (indices p).length=p.card := Finset.length_sort ..
  have run := opening_ready (initial td p) _ _ _ (n.symm ▸ opening_abi td p) size (initial_sources td p tree salts agrees)
  rw [n,payload_eq] at run
  exact run

private theorem resource_bounds {k : Nat} (le : k≤LENGTH) :
    0<steps k ∧ steps k≤1099511627776 ∧ 0<cycles k ∧ outputSize k≤13421772800 := by
  change k≤16777216 at le
  by_cases b:k=128
  · subst k;decide
  · by_cases z:k=0
    · subst k;decide
    · simp only [steps,cycles,outputSize,if_neg b,if_neg z]
      exact ⟨by omega, by omega, by omega, by omega⟩

theorem open_execution (td : Trapdoor) (p : Positions) :
    submission.run .opening (td,p)=pure (result td p) := by
  let s := initial td p
  have bound := resource_bounds (show p.card≤LENGTH by simpa using Finset.card_le_univ p)
  have ready := (facts td p _ _ (raw_agrees td)).1
  let fuel := 1099511627776-steps p.card
  have h : 1099511627776=(fuel+1)+(steps p.card-1) := by dsimp [fuel];omega
  rw [abi,h,ready.run]
  have atHalt : (if p.card=128 then 134 else 139) = 134 ∨ (if p.card=128 then 134 else 139)=139 := by split <;> simp
  rw [halt_run _ atHalt _ ready.pc ready.mode ready.success fuel,pure_bind]
  change pure (Execution.charge ⟨.success,_,1,0⟩ (cycles p.card-1) 0) = _
  unfold Execution.charge result
  rw [show cycles p.card-1+1=cycles p.card by omega]
  rfl

theorem succeeded (td : Trapdoor) (p : Positions) : submission.openingSucceeded (result td p)=true := by
  have ready := (facts td p _ _ (raw_agrees td)).1
  have bound := (resource_bounds (show p.card≤LENGTH by simpa using Finset.card_le_univ p)).2.2.2
  change (true && decide (((lastState (initial td p) p.card).getReg .x11).toNat≤13421772800))=true
  rw [ready.len];simp only [W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show outputSize p.card<2^64 by omega),
    decide_eq_true bound,Bool.true_and]

theorem read_payload (td : Trapdoor) (p : Positions) (tree : Levels) (salts : SaltTape) (agrees : TrapdoorAgrees td tree salts) :
    submission.readProof (result td p)=opening tree salts p := by
  obtain ⟨ready,data⟩ := facts td p tree salts agrees
  have size := opening_size tree salts p
  have length : (opening tree salts p).length=outputSize p.card := by
    by_cases b:p.card=BATCH
    · rw [size,if_pos b,outputSize,if_pos (show p.card=128 from b)]
    · rw [size,if_neg b,outputSize,if_neg (show p.card≠128 from b)]
  have bound := (resource_bounds (show p.card≤LENGTH by simpa using Finset.card_le_univ p)).2.2.2
  have ptr : ((result td p).state.getReg .x11).toNat=outputSize p.card := by
    change ((lastState (initial td p) p.card).getReg .x11).toNat=_
    rw [ready.len,W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  rw [Submission.readProof,if_pos (succeeded td p),ptr]
  apply List.ext_getElem
  · simp only [List.length_map,List.length_range,length]
  · intro i _ hi
    simp only [List.getElem_map,List.getElem_range]
    exact data i hi

theorem read_length (td : Trapdoor) (p : Positions) : (submission.readProof (result td p)).length=outputSize p.card := by
  rw [read_payload _ _ _ _ (raw_agrees td), opening_size]; rfl

end CommitGolfCandidate.Late.Open
