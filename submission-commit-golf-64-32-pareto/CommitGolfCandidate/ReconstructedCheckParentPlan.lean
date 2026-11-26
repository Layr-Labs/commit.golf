import CommitGolfCandidate.ReconstructedCheckParentFirst
import CommitGolfCandidate.ReconstructedCheckOracleMemory

namespace CommitGolfCandidate.Reconstruction.CheckParentPlan
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding Binding.Machine CheckValues CheckOrdinary CheckParentImage CheckParentRun CheckParentFirst CheckOracleMemory

def input (q : Nat) := loc 1 (if q=0 then 64 else 0)
def output (d q : Nat) := if q+1=work d then loc 3 0 else loc 1 0

def rowWord (d q i : Nat) : Term :=
  if q=0 then keyWord d i else if i<4 then .answer (q-1) i else .lit 0

def finalWord (d i : Nat) : Term :=
  let raw := Term.answer (work d-1) i
  if i≠3 ∨ d=0 then raw else
  if modulus d≠0 then .bin .remu raw (.lit (BitVec.ofNat 64 (modulus d)))
  else .bin .bitAnd (.lit (BitVec.ofNat 64 (2^(width d-192)-1))) raw

def callFields (d q : Nat) (hit : Hit) := (match entry hit.site with | .oracle _=>true | _=>false) &&
  decide (hit.state.get .x5=.lit 0 ∧ hit.state.get .x10=.ptr (input q) ∧ hit.state.get .x11=.lit 64 ∧
    hit.state.get .x12=.ptr (output d q) ∧ hit.state.get .x13=.lit 0 ∧
    ∀ i : Fin 8, look table (atIndex (input q) i) hit.state.writes=rowWord d q i)

def preserved : List Reg := [.x3,.x4,.x9,.x18,.x19,.x20,.x21,.x22,.x23,.x24,.x25,.x26,.x27]

def stopFields (d : Nat) (hit : Hit) :=
  (match entry hit.site with | .ret=>true | _=>false) &&
  decide (hit.state.get .x1=.reg .x1 ∧ hit.state.get .x8=.reg .x8 ∧ hit.state.get .x2=ptr 1 144 ∧
    ∀ i : Fin 4, look table (loc 3 (8*i.val)) hit.state.writes=finalWord d i) &&
  hit.state.writes.all (fun x=>decide (x.1.region=1 ∨ x.1.region=3)) &&
  preserved.all (fun r=>decide (hit.state.get r=.reg r))

def modelWrite (d q : Nat) (m : State) : State :=
  {m with pc:=m.pc+4,writes:=install (output d q) q m.writes 4}

def checkWith (nf : State→Option Hit) (d : Nat) (q n : Nat) (m : State) : Bool :=
  (Nat.rec (motive:=fun _=>Nat→State→Bool)
    (fun _ state=>(nf state).elim false (stopFields d))
    (fun _ rec index state=>(nf state).elim false (fun hit=>
      callFields d index hit && rec (index+1) (modelWrite d index hit.state))) n) q m

def check := checkWith (next table 90)

set_option maxRecDepth 25000
set_option maxHeartbeats 10000000

def stepsWith (nf : State→Option Hit) (d : Nat) (q n : Nat) (m : State) : Nat :=
  (Nat.rec (motive:=fun _=>Nat→State→Nat)
    (fun _ state=>(nf state).elim 0 Hit.steps)
    (fun _ rec index state=>(nf state).elim 0 (fun hit=>
      hit.steps+1+rec (index+1) (modelWrite d index hit.state))) n) q m

def steps := stepsWith (next table 90)

def Receipt (d : Nat) := check d 0 (work d) (start d)=true ∧ steps d 0 (work d) (start d)+1≤170

private theorem d0 : Receipt 0 := by unfold Receipt;decide +kernel
private theorem d1 : Receipt 1 := by unfold Receipt;decide +kernel
private theorem d2 : Receipt 2 := by unfold Receipt;decide +kernel
private theorem d3 : Receipt 3 := by unfold Receipt;decide +kernel
private theorem d4 : Receipt 4 := by unfold Receipt;decide +kernel
private theorem d5 : Receipt 5 := by unfold Receipt;decide +kernel
private theorem d6 : Receipt 6 := by unfold Receipt;decide +kernel
private theorem d7 : Receipt 7 := by unfold Receipt;decide +kernel
private theorem d8 : Receipt 8 := by unfold Receipt;decide +kernel
private theorem d9 : Receipt 9 := by unfold Receipt;decide +kernel
private theorem d10 : Receipt 10 := by unfold Receipt;decide +kernel
private theorem d11 : Receipt 11 := by unfold Receipt;decide +kernel
private theorem d12 : Receipt 12 := by unfold Receipt;decide +kernel
private theorem d13 : Receipt 13 := by unfold Receipt;decide +kernel
private theorem d14 : Receipt 14 := by unfold Receipt;decide +kernel
private theorem d15 : Receipt 15 := by unfold Receipt;decide +kernel
private theorem d16 : Receipt 16 := by unfold Receipt;decide +kernel
private theorem d17 : Receipt 17 := by unfold Receipt;decide +kernel
private theorem d18 : Receipt 18 := by unfold Receipt;decide +kernel
private theorem d19 : Receipt 19 := by unfold Receipt;decide +kernel
private theorem d20 : Receipt 20 := by unfold Receipt;decide +kernel
private theorem d21 : Receipt 21 := by unfold Receipt;decide +kernel
private theorem d22 : Receipt 22 := by unfold Receipt;decide +kernel
private theorem d23 : Receipt 23 := by unfold Receipt;decide +kernel

/-- The recorded machine path, return registers and exact instruction count
are checked independently at each depth of the fixed profile. -/
theorem checked (d : Fin 24) : Receipt d := by
  fin_cases d
  · exact d0
  · exact d1
  · exact d2
  · exact d3
  · exact d4
  · exact d5
  · exact d6
  · exact d7
  · exact d8
  · exact d9
  · exact d10
  · exact d11
  · exact d12
  · exact d13
  · exact d14
  · exact d15
  · exact d16
  · exact d17
  · exact d18
  · exact d19
  · exact d20
  · exact d21
  · exact d22
  · exact d23

theorem verified (d : Fin 24) : check d 0 (work d) (start d)=true := (checked d).1

end CommitGolfCandidate.Reconstruction.CheckParentPlan
