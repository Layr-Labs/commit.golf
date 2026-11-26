import CommitGolfCandidate.TruncWireStages
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

def wireCycles (k : Nat) := if k=128 then 116041 else cycles k
def wireSize (k : Nat) := if k=128 then 69120 else outputSize k
def result (td : Trapdoor) (p : Positions) : Execution :=
  let wide:=lastState (initial td p) p.card
  ⟨.success,if p.card=128 then Trunc.Wire.packedEnd wide else wide,wireCycles p.card,0⟩

private theorem abi (td : Trapdoor) (p : Positions) :
    submission.run .opening (td,p) = execute image 1099511627776 (initial td p) true := by
  have run (c : Submission) (t : BitVec (8*c.sizes.trapdoor)) :
      c.run .opening (t,p) = execute (c.image .opening) (c.steps .opening) (c.initialState .opening (t,p)) true := rfl
  exact run submission td

private theorem facts (td : Trapdoor) (p : Positions) (tree : Levels) (salts : SaltTape)
    (agrees : TrapdoorAgrees td tree salts) :
    Ready (initial td p) p.card ∧ HasBytes (lastState (initial td p) p.card) proofBase (wideOpening tree salts p) := by
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
  let wide:=lastState s p.card
  by_cases b:p.card=128
  · have pc : wide.pc=pcAt 134 := ready.pc.trans (by rw [if_pos b])
    let f:=1099511627776-(steps p.card-1+70167)
    have eqn : 1099511627776=(70167+f)+(steps p.card-1) := by dsimp [f];rw [b];decide
    have run:=Trunc.Wire.packRun wide f true pc
    change execute image (70167+f) wide true=_ at run
    rw [abi,eqn,ready.run,run,pure_bind]
    have sum : cycles p.card-1+70167=116041 := by rw [b];decide
    simp only [Execution.charge,result,wireCycles,if_pos b,sum,Nat.zero_add,wide,s]
  · have pc : wide.pc=pcAt 139 := ready.pc.trans (by rw [if_neg b])
    let f:=1099511627776-steps p.card
    have eqn : 1099511627776=(f+1)+(steps p.card-1) := by dsimp [f];omega
    rw [abi,eqn,ready.run,halt_run _ pc ready.mode ready.success f,pure_bind]
    have sum : cycles p.card-1+1=cycles p.card := by omega
    simp only [Execution.charge,result,wireCycles,if_neg b,sum,Nat.zero_add,wide,s]

private theorem outputReg (td : Trapdoor) (p : Positions) :
    (result td p).state.getReg .x11=W (wireSize p.card) := by
  have ready:=(facts td p _ _ (raw_agrees td)).1
  unfold result wireSize
  by_cases b:p.card=128
  · simp only [if_pos b]; exact Trunc.Wire.packedLength _
  · simp only [if_neg b];exact ready.len

private theorem sizeBound (p : Positions) : wireSize p.card≤13421772800 := by
  have h:= (resource_bounds (show p.card≤LENGTH by simpa using Finset.card_le_univ p)).2.2.2
  unfold wireSize;split <;> omega

theorem succeeded (td : Trapdoor) (p : Positions) : submission.openingSucceeded (result td p)=true := by
  change (true && decide (((result td p).state.getReg .x11).toNat≤13421772800))=true
  have h:=sizeBound p;rw [outputReg];simp only [W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show wireSize p.card<2^64 by omega),
    decide_eq_true h,Bool.true_and]

theorem read_payload (td : Trapdoor) (p : Positions) (tree : Levels) (salts : SaltTape) (agrees : TrapdoorAgrees td tree salts) :
    submission.readProof (result td p)=opening tree salts p := by
  obtain ⟨_,data⟩:=facts td p tree salts agrees
  have len : (opening tree salts p).length=wireSize p.card := by rw [opening_size];unfold wireSize outputSize;split <;> simp_all [BATCH]
  have ptr : ((result td p).state.getReg .x11).toNat=wireSize p.card := by
    rw [outputReg,W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have :=sizeBound p;omega)]
  rw [Submission.readProof,if_pos (succeeded td p),ptr]
  apply List.ext_getElem
  · simp only [List.length_map,List.length_range,len]
  · intro j _ hj
    simp only [List.getElem_map,List.getElem_range]
    let wide:=lastState (initial td p) p.card
    by_cases b:p.card=BATCH
    · have small : j<69120 := by rw [opening_size,if_pos b] at hj;exact hj
      have wlen : (wideOpening tree salts p).length=72704 := by rw [wide_size,if_pos b]
      have fit : Trunc.narrowIndex j<(wideOpening tree salts p).length := wlen ▸ (Trunc.widen_narrow j small).1
      have out := (Trunc.Wire.packedBytes wide j small).trans (data _ fit)
      simp only [result,opening,if_pos (show p.card=128 from b),if_pos b,Trunc.pack,List.getElem_map,List.getElem_range,
        List.getElem?_eq_getElem fit,Option.getD_some]
      exact out
    · have hl : opening tree salts p=wideOpening tree salts p := if_neg b
      have ok : j<(wideOpening tree salts p).length := hl ▸ hj
      simp only [result,if_neg (show p.card≠128 from b),hl]
      exact data j ok

theorem read_length (td : Trapdoor) (p : Positions) : (submission.readProof (result td p)).length=wireSize p.card := by
  rw [read_payload _ _ _ _ (raw_agrees td),opening_size]
  unfold wireSize outputSize;split <;> simp_all [BATCH]

end CommitGolfCandidate.Late.Open
