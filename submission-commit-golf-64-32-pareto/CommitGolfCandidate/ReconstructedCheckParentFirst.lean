import CommitGolfCandidate.ReconstructedCheckParentRun

namespace CommitGolfCandidate.Reconstruction.CheckParentFirst
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding Binding.Machine CheckValues CheckOrdinary CheckParentImage CheckParentRun CheckRecorded
set_option maxRecDepth 14000
set_option maxHeartbeats 3500000

def dataWord (i : Nat) := Term.old (loc 2 (8*i))

/-- The compilable expression for each of the eight words at the first
binary hash. The two high words follow the ordinary and residue encodings. -/
def keyWord (d i : Nat) :=
  if i=3 ∨ i=7 then
    if modulus (d+1)=0 then Term.bin .bitOr (.lit (childMask (d+1) false)) (dataWord i)
    else if i=7 then Term.bin .bitOr (dataWord i) (.lit (childMask (d+1) true)) else dataWord i
  else dataWord i

def expectedSite (d : Nat) : Fin 122 := if 1<work d then 67 else 96
def expectedDest (d : Nat) := if 1<work d then ptr 1 0 else ptr 3 0

def firstFields (d : Nat) (hit : Hit) :=
  hit.site=expectedSite d ∧
    hit.state.get .x5=.lit 0 ∧ hit.state.get .x10=ptr 1 64 ∧ hit.state.get .x11=.lit 64 ∧
    hit.state.get .x12=expectedDest d ∧ hit.state.get .x13=.lit 0 ∧
    (∀ i : Fin 8, look table (loc 1 (64+8*i.val)) hit.state.writes=keyWord d i) ∧
    (1<work d → ∀ i : Fin 4, look table (loc 1 (32+8*i.val)) hit.state.writes=.lit 0)

private def test (d : Nat) : Bool := match next table 90 (start d) with
  | none=>false
  | some h=>decide (h.site=expectedSite d ∧
    h.state.get .x5=.lit 0 ∧ h.state.get .x10=ptr 1 64 ∧ h.state.get .x11=.lit 64 ∧
    h.state.get .x12=expectedDest d ∧ h.state.get .x13=.lit 0 ∧
    (∀ i : Fin 8, look table (loc 1 (64+8*i.val)) h.state.writes=keyWord d i) ∧
    (1<work d → ∀ i : Fin 4, look table (loc 1 (32+8*i.val)) h.state.writes=.lit 0))

private theorem receipts : ∀ d : Fin 24, test d=true := by decide +kernel

theorem reach (o : Oracle) (env : Env) (layout : Layout env table) (d : Fin 24)
    (s : MachineState) (args : initialArgs s env d) :
    ∃ hit t, next table 90 (start d)=some hit ∧ Segment o hit.steps s t [] ∧
      Matches env hit.state t ∧ Safe table hit.state.writes ∧
      t.pc=CommitBlocks.addr (674+hit.site.val) ∧ firstFields d hit := by
  have yes := receipts d
  unfold test at yes
  cases eq : next table 90 (start d) with
  | none=>rw [eq] at yes;contradiction
  | some hit=>
    rw [eq] at yes
    obtain ⟨t,sg,state,ok,pc⟩ := CheckParentRun.sound o env table layout 90 (start d) s
      (initial_matches s env d args) (fun _ h=>by cases h) hit eq
    exact ⟨hit,t,rfl,sg,state,ok,pc,by unfold firstFields;exact of_decide_eq_true yes⟩

end CommitGolfCandidate.Reconstruction.CheckParentFirst
