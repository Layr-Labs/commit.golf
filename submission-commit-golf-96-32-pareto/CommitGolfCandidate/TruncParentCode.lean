import CommitGolfCandidate.TruncFetch
import CommitGolfCandidate.CommitParents
namespace CommitGolfCandidate.Trunc
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 30000
set_option maxHeartbeats 3500000

inductive Bank | low | high | tail | root deriving DecidableEq

def startWord : Bank → Nat → Nat
  | .low,j => 593+3*j
  | .high,j => 802+4*j
  | .tail,j => 933+4*j
  | .root,_ => 782

def inBank : Bank → Nat → Prop
  | .low,j | .high,j => j<32
  | .tail,j => j<30
  | .root,j => j=30

theorem bankBound (b : Bank) {j : Nat} (h : inBank b j) : j<32 := by
  cases b <;> simp only [inBank] at h <;> omega

theorem suffixWord (i : Nat) :
    (submission.image .commit).code[796+i]?=commitSuffix[i]? := by
  change ((List.set (List.set (List.set ((CommitGolfCandidate.submission.image .commit).code) 592 _) 691 _) 692 _) ++ commitSuffix)[796+i]?=_
  rw [List.getElem?_append_right (by simp only [List.length_set,show (CommitGolfCandidate.submission.image .commit).code.length=796 from rfl];omega)]
  simp only [List.length_set,show (CommitGolfCandidate.submission.image .commit).code.length=796 from rfl,Nat.add_sub_cancel_left]

private theorem highDecode : ∀ j : Fin 32,∀ m : Fin 3,
    (commitSuffix[6+4*j.val+m.val]?).bind decodeInstruction=some (.base (parentLaneInstr (31-j.val) m.val)) := by intro j m;fin_cases j <;> fin_cases m <;> rfl
private theorem tailDecode : ∀ j : Fin 30,∀ m : Fin 3,
    (commitSuffix[137+4*j.val+m.val]?).bind decodeInstruction=some (.base (parentLaneInstr (31-j.val) m.val)) := by intro j m;fin_cases j <;> fin_cases m <;> rfl

theorem laneDecode (b : Bank) (j m : Nat) (hj : inBank b j) (hm : m<3) :
    ((submission.image .commit).code[startWord b j+m]?).bind decodeInstruction=some (.base (parentLaneInstr (31-j) m)) := by
  cases b
  · change j<32 at hj
    change ((submission.image .commit).code[593+3*j+m]?).bind decodeInstruction=_
    rw [originalWord _ (by omega) (by omega) (by omega) (by omega)]
    exact commit_parent_decode false j m hj hm
  · change j<32 at hj
    change ((submission.image .commit).code[802+4*j+m]?).bind decodeInstruction=_
    rw [show 802+4*j+m=796+(6+4*j+m) by omega,suffixWord]
    exact highDecode ⟨j,hj⟩ ⟨m,hm⟩
  · change j<30 at hj
    change ((submission.image .commit).code[933+4*j+m]?).bind decodeInstruction=_
    rw [show 933+4*j+m=796+(137+4*j+m) by omega,suffixWord]
    exact tailDecode ⟨j,hj⟩ ⟨m,hm⟩
  · change j=30 at hj;subst j
    change ((submission.image .commit).code[782+m]?).bind decodeInstruction=_
    rw [originalWord _ (by omega) (by omega) (by omega) (by omega)]
    exact commit_parent_decode true 30 m (by decide) hm

theorem maskDecode (b : Bank) (j : Nat) (hj : inBank b j) (masked : b=.high ∨ b=.tail) :
    ((submission.image .commit).code[startWord b j+3]?).bind decodeInstruction=some (.base (.SH .x12 .x0 30)) := by
  rcases masked with rfl|rfl
  · change j<32 at hj
    change ((submission.image .commit).code[802+4*j+3]?).bind decodeInstruction=_
    rw [show 802+4*j+3=796+(6+4*j+3) by omega,suffixWord]
    exact (show ∀ v : Fin 32, (commitSuffix[6+4*v.val+3]?).bind decodeInstruction=some (.base (.SH .x12 .x0 30)) by intro v;fin_cases v <;> rfl) ⟨j,hj⟩
  · change j<30 at hj
    change ((submission.image .commit).code[933+4*j+3]?).bind decodeInstruction=_
    rw [show 933+4*j+3=796+(137+4*j+3) by omega,suffixWord]
    exact (show ∀ v : Fin 30, (commitSuffix[137+4*v.val+3]?).bind decodeInstruction=some (.base (.SH .x12 .x0 30)) by intro v;fin_cases v <;> rfl) ⟨j,hj⟩
end CommitGolfCandidate.Trunc
