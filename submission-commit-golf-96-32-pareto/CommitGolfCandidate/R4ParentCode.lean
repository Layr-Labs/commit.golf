import CommitGolfCandidate.R4CommitBase
import CommitGolfCandidate.LateTreeMemory
import CommitGolfCandidate.S4MaskState
import CommitGolfCandidate.LateCalls
set_option Elab.async false

namespace CommitGolfCandidate.R4
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (pcAt rowAddress nodeAddress levelCount)
abbrev Width := Fin 24
def stagePC (d : Width) := ([180278, 200777, 217863, 230169, 238455, 244865, 249677, 252791, 255215, 257213, 258341, 259307, 260111, 260645, 261089, 261335, 261563, 261677, 261785, 261927, 262003, 262049, 262077, 262099] : List Nat)[d.val]?.getD 0
def bodyPC (d : Width) := ([180296, 200792, 217878, 230184, 238470, 244880, 249692, 252806, 255230, 257228, 258356, 259322, 260126, 260660, 261104, 261350, 261578, 261692, 261795, 261937, 262013, 262059, 262087, 262109] : List Nat)[d.val]?.getD 0
def endPC (d : Width) := ([200777, 217863, 230169, 238455, 244865, 249677, 252791, 255215, 257213, 258341, 259307, 260111, 260645, 261089, 261335, 261563, 261677, 261785, 261927, 262003, 262049, 262077, 262099, 262112] : List Nat)[d.val]?.getD 0

def groupSize (d : Width) := ([6820, 4256, 3066, 2056, 1596, 798, 514, 390, 326, 182, 156, 130, 80, 68, 38, 34, 14, 14, 24, 12, 8, 4, 4, 2] : List Nat)[d.val]?.getD 0
def nodes (d : Width) := levelCount (d.val+1)
def bulkCount (d : Width) := nodes d / groupSize d * groupSize d
def extra (d : Width) := if d.val=0 ∨ d.val=23 then 0 else if d.val<5 then 1 else 3
def laneWidth (d : Width) := 3 + extra d
def bank (d : Width) (tail : Bool) := bodyPC d + (if tail && decide (0 < bulkCount d) then groupSize d * laneWidth d+3 else 0)
def bankSize (d : Width) (tail : Bool) := if tail then nodes d % groupSize d else if 0<bulkCount d then groupSize d else 0
def lane (d : Width) (tail : Bool) (j : Nat) := bank d tail+j*laneWidth d
def destInc (j : Nat) := if j%2=0 then 32 else 64
def maskOps (e : Nat) : List Instr :=
  if e=0 then [] else if e=1 then [.SH .x12 .x0 30] else [.LHU .x6 .x12 28,.AND .x6 .x6 .x28,.SW .x12 .x6 28]
def laneOps (d : Width) (j : Nat) := [Instr.ECALL] ++ maskOps (extra d) ++ [.ADDI .x10 .x10 96,.ADDI .x12 .x12 (BitVec.ofNat 12 (destInc j))]
def Here (n : Nat) (op : Instr) := ∀ s : MachineState,s.pc=pcAt n → fetch (submission.image .commit) s=some (.base op)
def getOp (n : Nat) := if h:n<262123 then decodeInstruction (Artifact.commitCode.get 32 ⟨n,h⟩) else none
def hasOp (n : Nat) (op : Instr) := match getOp n with | some (.base actual)=>decide (actual=op) | _=>false
def listed (n : Nat) (ops : List Instr) := (List.finRange ops.length).all (fun j=>hasOp (n+j.val) ops[j.val])
theorem hasOp_sound {n : Nat} {op : Instr} (h : hasOp n op) : Here n op := by
  unfold hasOp at h
  split at h
  next actual dec =>
    have equal:=of_decide_eq_true h
    subst actual
    by_cases small:n<262123
    · rw [getOp,dif_pos small] at dec
      exact fun s pc=>fetch_of_packed Artifact.commitCode _ s n small pc _ dec
    · simp [getOp,small] at dec
  next => contradiction
theorem listHere {n : Nat} {ops : List Instr} (h : listed n ops) (j : Nat) (hj : j<ops.length) : Here (n+j) ops[j] :=
  hasOp_sound (List.all_eq_true.mp h ⟨j,hj⟩ (List.mem_finRange ..))
def atLane (d : Width) (j : Nat) := ∀ t : Bool, j<bankSize d t → listed (lane d t j) (laneOps d j)=true
instance (d : Width) (j : Nat) : Decidable (atLane d j) := inferInstanceAs (Decidable (∀ t : Bool, _ → _))

def rawWord (i : Nat) : BitVec 32 :=
  if h : i<262123 then Artifact.commitCode.get 32 ⟨i,h⟩ else 0
def bankEnd (d : Width) (t : Bool) := bank d t + bankSize d t*laneWidth d-1
def shape (d : Width) : Prop := ∀ t : Bool, 0<bankSize d t →
  bankEnd d t<262123 ∧ ROM.bankChunks (bank d t) (bankEnd d t) (2*laneWidth d) ∧
  ROM.bankWords (bank d t) (bankEnd d t) (2*laneWidth d) (fun k=>rawWord (bank d t+k))
instance (d : Width) : Decidable (shape d) := inferInstanceAs (Decidable (∀ t : Bool, _ → _ ∧ _ ∧ _))
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000
private theorem sites0 : shape 0 := by decide +kernel
private theorem sites1 : shape 1 := by decide +kernel
private theorem sites2 : shape 2 := by decide +kernel
private theorem sites3 : shape 3 := by decide +kernel
private theorem sites4 : shape 4 := by decide +kernel
private theorem sites5 : shape 5 := by decide +kernel
private theorem sites6 : shape 6 := by decide +kernel
private theorem sites7 : shape 7 := by decide +kernel
private theorem sites8 : shape 8 := by decide +kernel
private theorem sites9 : shape 9 := by decide +kernel
private theorem sites10 : shape 10 := by decide +kernel
private theorem sites11 : shape 11 := by decide +kernel
private theorem sites12 : shape 12 := by decide +kernel
private theorem sites13 : shape 13 := by decide +kernel
private theorem sites14 : shape 14 := by decide +kernel
private theorem sites15 : shape 15 := by decide +kernel
private theorem sites16 : shape 16 := by decide +kernel
private theorem sites17 : shape 17 := by decide +kernel
private theorem sites18 : shape 18 := by decide +kernel
private theorem sites19 : shape 19 := by decide +kernel
private theorem sites20 : shape 20 := by decide +kernel
private theorem sites21 : shape 21 := by decide +kernel
private theorem sites22 : shape 22 := by decide +kernel
private theorem sites23 : shape 23 := by decide +kernel
private theorem allSites (d : Width) : shape d := by
  fin_cases d
  · exact sites0
  · exact sites1
  · exact sites2
  · exact sites3
  · exact sites4
  · exact sites5
  · exact sites6
  · exact sites7
  · exact sites8
  · exact sites9
  · exact sites10
  · exact sites11
  · exact sites12
  · exact sites13
  · exact sites14
  · exact sites15
  · exact sites16
  · exact sites17
  · exact sites18
  · exact sites19
  · exact sites20
  · exact sites21
  · exact sites22
  · exact sites23

private theorem firstTwo : ∀ d : Width,∀ j : Fin 2, atLane d j.val := by decide +kernel
private theorem widths (d : Width) : laneWidth d=3 ∨ laneWidth d=4 ∨ laneWidth d=6 := by
  revert d;decide
theorem laneListed (d : Width) (j : Nat) (t : Bool) (hj : j<bankSize d t) : listed (lane d t j) (laneOps d j) := by
  obtain ⟨lim,chunks,words⟩ := allSites d t (by omega)
  let r := j%2
  have eqops : laneOps d j=laneOps d r := by simp [r,laneOps,destInc]
  have early := firstTwo d ⟨r,Nat.mod_lt _ (by decide)⟩ t (lt_of_le_of_lt (Nat.mod_le _ _) hj)
  change listed (lane d t r) (laneOps d r) = true at early
  unfold listed at early ⊢
  rw [eqops]
  apply List.all_eq_true.mpr
  intro k _
  have code:=List.all_eq_true.mp early k (List.mem_finRange ..)
  have lengthEq : (laneOps d r).length=laneWidth d := by
    unfold laneOps maskOps laneWidth extra
    split_ifs <;> simp_all
  have kw : k.val<laneWidth d:=lengthEq ▸ k.isLt
  have range : bank d t ≤ lane d t j+k.val ∧ lane d t j+k.val ≤ bankEnd d t ∧
       lane d t r+k.val ≤ bankEnd d t ∧
       (lane d t j+k.val-bank d t)%(2*laneWidth d)=r*laneWidth d+k.val := by
    unfold lane bankEnd r
    rcases widths d with h|h|h <;> simp only [h] at kw ⊢ <;> omega
  have ww : ROM.allowed (2*laneWidth d) := by rcases widths d with h|h|h <;> rw [h] <;> simp [ROM.allowed]
  have w := ROM.bankRead ww chunks words (lane d t j+k.val) range.1 range.2.1 (by omega)
  rw [range.2.2.2] at w
  have br : bank d t+(r*laneWidth d+k.val)=lane d t r+k.val := by simp [lane,Nat.add_assoc]
  change _ = rawWord (bank d t+(r*laneWidth d+k.val)) at w
  rw [br,rawWord,dif_pos (by omega)] at w
  simp only [hasOp,getOp,dif_pos (show lane d t j+k.val<262123 by omega),w] 
  simpa only [hasOp,getOp,dif_pos (show lane d t r+k.val<262123 by omega)] using code
end CommitGolfCandidate.R4
