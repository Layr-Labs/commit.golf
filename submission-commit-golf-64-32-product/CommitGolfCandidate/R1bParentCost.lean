import Mathlib.Tactic
namespace TwoPermutationPrototype.RV64.R1bParents
set_option maxRecDepth 65536
def site (n : Nat) := if n<524288 then 4125+6*((1024-n%1024)%1024) else 26+4*(1023-n%1024)

/-- Includes the back jumps, both phase exits, and the jump to the root copy. -/
def remainingSteps (n : Nat) : Nat :=
  if n<524288 then 6*n+2*((n+1023)/1024)
  else 4*n+2*(n/1024)+1048576

def width (n : Nat) := if n<524288 then 6 else 4
def controlSteps (n : Nat) := if n<524288 then (if n%1024=1 then 2 else 0)
  else (if n%1024=0 then 2 else 0)

private theorem narrowDelta (n : Nat) (pos : 0<n) :
    6*n+2*((n+1023)/1024)=6+(if n%1024=1 then 2 else 0)+(6*(n-1)+2*((n-1+1023)/1024)) := by
  split <;> omega

private theorem wideDelta (n : Nat) (pos : 0<n) :
    4*n+2*(n/1024)+1048576=4+(if n%1024=0 then 2 else 0)+(4*(n-1)+2*((n-1)/1024)+1048576) := by
  split <;> omega

theorem stepCount {n : Nat} (positive : 0<n) :
    remainingSteps n = width n + controlSteps n + remainingSteps (n-1) := by
  by_cases cut : n=524288
  · subst n;decide
  by_cases low : n<524288
  · simpa only [remainingSteps,width,controlSteps,if_pos low,if_pos (show n-1<524288 by omega)] using narrowDelta n positive
  · simpa only [remainingSteps,width,controlSteps,if_neg low,if_neg (show ¬n-1<524288 by omega)] using wideDelta n positive

theorem upper_count : 5+remainingSteps 8388607=34619391 := by decide

end TwoPermutationPrototype.RV64.R1bParents
