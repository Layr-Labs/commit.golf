import CommitGolfCandidate.RungAPlan
namespace CommitGolfCandidate.RungA.Kernel
open CommitGolf R4
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 2400000
def full : List Act := [
  .call (.leaf 15) (.scratch 4) true false,
  .call (.leaf 16) (.scratch 5) true false,
  .call (.leaf 17) (.scratch 6) true false,
  .call (.scratch 4) (.scratch 6) false false,
  .call (.leaf 12) (.scratch 3) true false,
  .call (.leaf 13) (.scratch 4) true false,
  .call (.leaf 14) (.scratch 5) true false,
  .call (.scratch 3) (.scratch 5) false false,
  .call (.scratch 5) (.scratch 5) false true,
  .call (.leaf 21) (.scratch 9) true false,
  .call (.leaf 22) (.scratch 10) true false,
  .call (.leaf 23) (.scratch 11) true false,
  .call (.scratch 9) (.scratch 11) false false,
  .call (.leaf 18) (.scratch 8) true false,
  .call (.leaf 19) (.scratch 9) true false,
  .call (.leaf 20) (.scratch 10) true false,
  .call (.scratch 8) (.scratch 10) false false,
  .call (.scratch 10) (.scratch 6) true true,
  .call (.scratch 5) (.scratch 6) false true,
  .call (.leaf 3) (.scratch 14) true false,
  .call (.leaf 4) (.scratch 15) true false,
  .call (.leaf 5) (.scratch 16) true false,
  .call (.scratch 14) (.scratch 16) false false,
  .call (.leaf 0) (.scratch 13) true false,
  .call (.leaf 1) (.scratch 14) true false,
  .call (.leaf 2) (.scratch 15) true false,
  .call (.scratch 13) (.scratch 15) false false,
  .call (.scratch 15) (.scratch 15) false true,
  .call (.leaf 9) (.scratch 19) true false,
  .call (.leaf 10) (.scratch 20) true false,
  .call (.leaf 11) (.scratch 21) true false,
  .call (.scratch 19) (.scratch 21) false false,
  .call (.leaf 6) (.scratch 18) true false,
  .call (.leaf 7) (.scratch 19) true false,
  .call (.leaf 8) (.scratch 20) true false,
  .call (.scratch 18) (.scratch 20) false false,
  .call (.scratch 20) (.scratch 16) true true,
  .call (.scratch 15) (.scratch 5) true true,
  .call (.scratch 5) .output true true]
def tailGroup : List Act := [
  .call (.leaf 15) (.scratch 4) true false,
  .clear 5,
  .clear 6,
  .call (.scratch 4) (.scratch 6) true false,
  .call (.leaf 12) (.scratch 3) true false,
  .call (.leaf 13) (.scratch 4) true false,
  .call (.leaf 14) (.scratch 5) true false,
  .call (.scratch 3) (.scratch 5) false false,
  .call (.scratch 5) (.scratch 5) false true,
  .clear 6,
  .call (.scratch 5) (.scratch 6) true true,
  .call (.leaf 3) (.scratch 9) true false,
  .call (.leaf 4) (.scratch 10) true false,
  .call (.leaf 5) (.scratch 11) true false,
  .call (.scratch 9) (.scratch 11) false false,
  .call (.leaf 0) (.scratch 8) true false,
  .call (.leaf 1) (.scratch 9) true false,
  .call (.leaf 2) (.scratch 10) true false,
  .call (.scratch 8) (.scratch 10) false false,
  .call (.scratch 10) (.scratch 10) false true,
  .call (.leaf 9) (.scratch 14) true false,
  .call (.leaf 10) (.scratch 15) true false,
  .call (.leaf 11) (.scratch 16) true false,
  .call (.scratch 14) (.scratch 16) false false,
  .call (.leaf 6) (.scratch 13) true false,
  .call (.leaf 7) (.scratch 14) true false,
  .call (.leaf 8) (.scratch 15) true false,
  .call (.scratch 13) (.scratch 15) false false,
  .call (.scratch 15) (.scratch 11) true true,
  .call (.scratch 10) (.scratch 5) true true,
  .call (.scratch 5) .output true true]
def writes := scratchWrites full ++ scratchWrites tailGroup
theorem verifiedFull : legal 24 writes (initial writes) full=true ∧
    (full.foldl update (initial writes)).out=some (wanted 24 4 0) ∧ queries full=39 := by
  refine ⟨?_,?_,?_⟩ <;> decide +kernel
theorem verifiedTail : legal 16 writes (initial writes) tailGroup=true ∧
    (tailGroup.foldl update (initial writes)).out=some (wanted 16 4 0) ∧ queries tailGroup=28 := by
  refine ⟨?_,?_,?_⟩ <;> decide +kernel
def off (j : Nat) := 96*(j/2)+32*(j%2)
theorem sitesFull : ∀ j : Fin 8, listed (131140+114*j.val) (code full (off j.val))=true ∧
    hasOp (131140+114*j.val+113) (.ADD .x21 .x21 .x25)=true := by decide +kernel
theorem restFull : ∀ j : Fin 2, listed (132054+114*j.val) (code full (off j.val))=true ∧
    hasOp (132054+114*j.val+113) (.ADD .x21 .x21 .x25)=true := by decide +kernel
theorem sitesEnd : listed 132282 (code tailGroup 96)=true ∧
    hasOp 132377 (.ADD .x21 .x21 .x25)=true := by decide +kernel
theorem lengths (o : Nat) : (code full o).length=113 ∧ (code tailGroup o).length=95 := by
  constructor <;> rfl
end CommitGolfCandidate.RungA.Kernel
