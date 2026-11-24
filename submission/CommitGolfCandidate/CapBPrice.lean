import CommitGolfCandidate.GroupOpenCapChunkFrontier
import CommitGolfCandidate.Layout2CapTables
namespace TwoPermutationPrototype.GroupedOpening.CapB
open Sampling CommitGolfCandidate.Layout2
set_option maxHeartbeats 1400000

def entryLen (r : Nat) := if depthOf r=3 then 2 else 3
def chunkPrice (mask : Nat) := 11+((chunkEntries mask).map entryLen).sum
def control (gs : List Nat) (node : Nat) : Nat → Nat
  | 0 => if capIsMarked gs node 3 then chunkPrice (leafMask gs node) else 5
  | h+1 => if capIsMarked gs node (h+4) then 14+control gs (2*node) h+control gs (2*node+1) h else 5

def carryBits (j : Nat) := 46*(j%32)%64
def handlerLen (j : Nat) := let c:=carryBits j
  if c=0 then 12 else if c<18 then 14 else if c=18 then 15 else 16
def handlers : Nat → Nat
  | 0 => 0
  | n+1 => handlers n+handlerLen n
def flushBytes (m : Nat) := Cap.size m-Cap.body m
def flushPrice (m : Nat) := if m%32=0 then 0 else if flushBytes (m%32)=6 then 10 else 8
/-- The root walk exits through 707; the finish then checks phase and copy mode and jumps to the four-word halt. -/
def price (gs : List Nat) (k : Nat) :=
  let f:=(capFrontierNodes gs 1 8).length
  let bytes:=Cap.size f
  297+control gs 1 5+handlers f+1+7+flushPrice f+
    if k%4=0 then 0 else 2+3+5*bytes

def ceiling : Nat → Nat
  | 0 => 13
  | h+1 => 14+2*ceiling h

theorem chunks_bounded : ∀ m : Fin 256, chunkPrice m.val≤13+2*(chunkEntries m.val).length := by decide +kernel

theorem control_bound (gs : List Nat) (n h : Nat) :
    control gs n h≤ceiling h+2*(capFrontierNodes gs n (h+3)).length := by
  induction h generalizing n with
  | zero =>
    simp only [control,ceiling,Nat.zero_add]
    split
    · rename_i marked
      have front:=chunk_frontier gs n
      simpa [front] using chunks_bounded ⟨leafMask gs n,leaf_mask_lt gs n⟩
    · omega
  | succ h ih =>
    have l:=ih (2*n);have r:=ih (2*n+1)
    rw [show h+1+3=(h+3)+1 by omega,capFrontierNodes]
    simp only [control,ceiling,show h+3+1=h+4 by omega]
    split <;> rename_i mark <;> simp only [mark,ite_true,ite_false,List.length_append,List.length_singleton] <;> omega

theorem batch_frontier : ∀ f : Fin 129,
    297+(850+2*f.val)+handlers f.val+1+7+flushPrice f.val≤3375 := by decide +kernel
theorem last_two : (297+(850+2*127)+handlers 127+1+7+flushPrice 127=3366) ∧
    (297+(850+2*128)+handlers 128+1+7+flushPrice 128=3375) := by decide +kernel

theorem scored (gs : List Nat) (hf : (capFrontierNodes gs 1 8).length≤128) :
    price gs 128≤3375 := by
  have c:=control_bound gs 1 5
  change control gs 1 5≤850+2*(capFrontierNodes gs 1 8).length at c
  have stop:=batch_frontier ⟨(capFrontierNodes gs 1 8).length,by omega⟩
  unfold price;dsimp only at stop ⊢;rw [if_pos (by decide : 128%4=0)];omega

end TwoPermutationPrototype.GroupedOpening.CapB
