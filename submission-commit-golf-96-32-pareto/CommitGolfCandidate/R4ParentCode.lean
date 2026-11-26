import CommitGolfCandidate.R4CommitBase
import CommitGolfCandidate.LateTreeMemory
import CommitGolfCandidate.S4MaskState
import CommitGolfCandidate.LateCalls
namespace CommitGolfCandidate.R4
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (pcAt rowAddress nodeAddress levelCount)
abbrev Width := Fin 24
def stagePC (d : Width) := ([3374, 4419, 5119, 5991, 6691, 7563, 8605, 9905, 10947, 12247, 13289, 14589, 15631, 16931, 17973, 19273, 20315, 20841, 21109, 21251, 21327, 21373, 21401, 21423] : List Nat)[d.val]?.getD 0
def bodyPC (d : Width) := ([3392, 4434, 5134, 6006, 6706, 7578, 8620, 9920, 10962, 12262, 13304, 14604, 15646, 16946, 17988, 19288, 20325, 20851, 21119, 21261, 21337, 21383, 21411, 21433] : List Nat)[d.val]?.getD 0
def endPC (d : Width) := ([4419, 5119, 5991, 6691, 7563, 8605, 9905, 10947, 12247, 13289, 14589, 15631, 16931, 17973, 19273, 20315, 20841, 21109, 21251, 21327, 21373, 21401, 21423, 21436] : List Nat)[d.val]?.getD 0

def groupSize (d : Width) := if d.val=0 then 256 else 128
def nodes (d : Width) := levelCount (d.val+1)
def bulkCount (d : Width) := nodes d / groupSize d * groupSize d
def extra (d : Width) := if d.val=0 ∨ d.val=23 then 0 else if d.val<5 then 1 else 3
def laneWidth (d : Width) := 3 + extra d
def bank (d : Width) (tail : Bool) := bodyPC d + (if tail && decide (0 < bulkCount d) then groupSize d * laneWidth d+1 else 0)
def bankSize (d : Width) (tail : Bool) := if tail then nodes d % groupSize d else if 0<bulkCount d then groupSize d else 0
def lane (d : Width) (tail : Bool) (j : Nat) := bank d tail+j*laneWidth d
def destInc (j : Nat) := if j%2=0 then 32 else 64
def maskOps (e : Nat) : List Instr :=
  if e=0 then [] else if e=1 then [.SH .x12 .x0 30] else [.LHU .x6 .x12 28,.AND .x6 .x6 .x28,.SW .x12 .x6 28]
def laneOps (d : Width) (j : Nat) := [Instr.ECALL] ++ maskOps (extra d) ++ [.ADDI .x10 .x10 96,.ADDI .x12 .x12 (BitVec.ofNat 12 (destInc j))]
def Here (n : Nat) (op : Instr) := ∀ s : MachineState,s.pc=pcAt n → fetch (submission.image .commit) s=some (.base op)
def getOp (n : Nat) := if h:n<21447 then decodeInstruction (Artifact.commitCode.get 32 ⟨n,h⟩) else none
def hasOp (n : Nat) (op : Instr) := match getOp n with | some (.base actual)=>decide (actual=op) | _=>false
def listed (n : Nat) (ops : List Instr) := (List.finRange ops.length).all (fun j=>hasOp (n+j.val) ops[j.val])
theorem hasOp_sound {n : Nat} {op : Instr} (h : hasOp n op) : Here n op := by
  unfold hasOp at h
  split at h
  next actual dec =>
    have equal:=of_decide_eq_true h
    subst actual
    by_cases small:n<21447
    · rw [getOp,dif_pos small] at dec
      exact fun s pc=>fetch_of_packed Artifact.commitCode _ s n small pc _ dec
    · simp [getOp,small] at dec
  next => contradiction
theorem listHere {n : Nat} {ops : List Instr} (h : listed n ops) (j : Nat) (hj : j<ops.length) : Here (n+j) ops[j] :=
  hasOp_sound (List.all_eq_true.mp h ⟨j,hj⟩ (List.mem_finRange ..))
def atLane (d : Width) (j : Nat) := ∀ t : Bool, j<bankSize d t → listed (lane d t j) (laneOps d j)=true
instance (d : Width) (j : Nat) : Decidable (atLane d j) := inferInstanceAs (Decidable (∀ t : Bool, _ → _))
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000
private theorem sites0 : ∀ j : Fin 256,atLane 0 j.val := by decide +kernel
private theorem sites1 : ∀ j : Fin 128,atLane 1 j.val := by decide +kernel
private theorem sites2 : ∀ j : Fin 128,atLane 2 j.val := by decide +kernel
private theorem sites3 : ∀ j : Fin 128,atLane 3 j.val := by decide +kernel
private theorem sites4 : ∀ j : Fin 128,atLane 4 j.val := by decide +kernel
private theorem sites5 : ∀ j : Fin 128,atLane 5 j.val := by decide +kernel
private theorem sites6 : ∀ j : Fin 128,atLane 6 j.val := by decide +kernel
private theorem sites7 : ∀ j : Fin 128,atLane 7 j.val := by decide +kernel
private theorem sites8 : ∀ j : Fin 128,atLane 8 j.val := by decide +kernel
private theorem sites9 : ∀ j : Fin 128,atLane 9 j.val := by decide +kernel
private theorem sites10 : ∀ j : Fin 128,atLane 10 j.val := by decide +kernel
private theorem sites11 : ∀ j : Fin 128,atLane 11 j.val := by decide +kernel
private theorem sites12 : ∀ j : Fin 128,atLane 12 j.val := by decide +kernel
private theorem sites13 : ∀ j : Fin 128,atLane 13 j.val := by decide +kernel
private theorem sites14 : ∀ j : Fin 128,atLane 14 j.val := by decide +kernel
private theorem sites15 : ∀ j : Fin 128,atLane 15 j.val := by decide +kernel
private theorem sites16 : ∀ j : Fin 128,atLane 16 j.val := by decide +kernel
private theorem sites17 : ∀ j : Fin 128,atLane 17 j.val := by decide +kernel
private theorem sites18 : ∀ j : Fin 128,atLane 18 j.val := by decide +kernel
private theorem sites19 : ∀ j : Fin 128,atLane 19 j.val := by decide +kernel
private theorem sites20 : ∀ j : Fin 128,atLane 20 j.val := by decide +kernel
private theorem sites21 : ∀ j : Fin 128,atLane 21 j.val := by decide +kernel
private theorem sites22 : ∀ j : Fin 128,atLane 22 j.val := by decide +kernel
private theorem sites23 : ∀ j : Fin 128,atLane 23 j.val := by decide +kernel

theorem laneListed (d : Width) (j : Nat) (t : Bool) (hj : j<bankSize d t) : listed (lane d t j) (laneOps d j) := by
  have lim : bankSize d t ≤ groupSize d := (show ∀ x : Width, ∀ y : Bool, bankSize x y ≤ groupSize x by decide) d t
  fin_cases d
  · exact sites0 ⟨j,lt_of_lt_of_le hj lim⟩ t hj
  · exact sites1 ⟨j,lt_of_lt_of_le hj lim⟩ t hj
  · exact sites2 ⟨j,lt_of_lt_of_le hj lim⟩ t hj
  · exact sites3 ⟨j,lt_of_lt_of_le hj lim⟩ t hj
  · exact sites4 ⟨j,lt_of_lt_of_le hj lim⟩ t hj
  · exact sites5 ⟨j,lt_of_lt_of_le hj lim⟩ t hj
  · exact sites6 ⟨j,lt_of_lt_of_le hj lim⟩ t hj
  · exact sites7 ⟨j,lt_of_lt_of_le hj lim⟩ t hj
  · exact sites8 ⟨j,lt_of_lt_of_le hj lim⟩ t hj
  · exact sites9 ⟨j,lt_of_lt_of_le hj lim⟩ t hj
  · exact sites10 ⟨j,lt_of_lt_of_le hj lim⟩ t hj
  · exact sites11 ⟨j,lt_of_lt_of_le hj lim⟩ t hj
  · exact sites12 ⟨j,lt_of_lt_of_le hj lim⟩ t hj
  · exact sites13 ⟨j,lt_of_lt_of_le hj lim⟩ t hj
  · exact sites14 ⟨j,lt_of_lt_of_le hj lim⟩ t hj
  · exact sites15 ⟨j,lt_of_lt_of_le hj lim⟩ t hj
  · exact sites16 ⟨j,lt_of_lt_of_le hj lim⟩ t hj
  · exact sites17 ⟨j,lt_of_lt_of_le hj lim⟩ t hj
  · exact sites18 ⟨j,lt_of_lt_of_le hj lim⟩ t hj
  · exact sites19 ⟨j,lt_of_lt_of_le hj lim⟩ t hj
  · exact sites20 ⟨j,lt_of_lt_of_le hj lim⟩ t hj
  · exact sites21 ⟨j,lt_of_lt_of_le hj lim⟩ t hj
  · exact sites22 ⟨j,lt_of_lt_of_le hj lim⟩ t hj
  · exact sites23 ⟨j,lt_of_lt_of_le hj lim⟩ t hj

end CommitGolfCandidate.R4
