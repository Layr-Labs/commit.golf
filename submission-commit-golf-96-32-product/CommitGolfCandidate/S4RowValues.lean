import CommitGolfCandidate.S4Deposit
import CommitGolfCandidate.LateParents
import CommitGolfCandidate.S4Witness
namespace CommitGolfCandidate.S4.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (Digest)
def cell (s : MachineState) (k : Nat) := readBuffer s (512+32*k) 32

theorem cellWrite {s t : MachineState} {src lane : Nat} (small : lane<3)
    (write : Moved s t src (512+32*lane) 32) (k : Nat) (bound : k<3) :
    cell t k=if k=lane then readBuffer s src 32 else cell s k := by
  by_cases same:k=lane
  · subst k;rw [if_pos rfl];exact write.read (by omega)
  · rw [if_neg same];apply write.away (by omega);omega

theorem tripleRead (s : MachineState) : readBuffer s 512 96=cell s 2 ++ cell s 1 ++ cell s 0 := Late.readTriple s 512

theorem cyclicPayload (i : Nat) (cur a b : Digest) (raw : Nat→Digest) :
    let atLane:=i%3
    let next:=(atLane+1)%3
    let last:=(next+1)%3
    let val (k : Nat):=if k=last then b else if k=next then a else if k=atLane then cur else raw k
    val 2++val 1++val 0=payload (lane 0 i) cur (a,b) := by
  have e : i%3=0 ∨ i%3=1 ∨ i%3=2:=by omega
  rcases e with e|e|e <;> simp only [lane,e,ite_true] <;> rfl

theorem pairPayload (h i : Nat) (bh : 0<h) (cur a : Digest) (raw : Nat→Digest) (extra : Digest) :
    let atLane:=i%2
    let next:=(atLane+1)%2
    let val (k : Nat):=if k=next then a else if k=atLane then cur else raw k
    (0 : Digest)++val 1++val 0=payload (lane h i) cur (a,extra) := by
  have e : i%2=0 ∨ i%2=1:=by omega
  rcases e with e|e <;> simp only [lane,if_neg (by omega : h≠0),e,ite_true] <;> rfl

theorem cellPreserved {s t : MachineState} (mem : t.mem=s.mem) (k : Nat) : cell t k=cell s k :=
  read_buffer_memory_congr t s mem _ _

theorem protectedBytes {s t : MachineState} {a n : Nat} (m : SameOutside s t a n) (lo : 256≤a) (hi : a+n≤608) :
    SameOutside s t 256 352:=fun r b away=>m r b (by omega)
theorem unchangedBytes {s t : MachineState} (same : t.mem=s.mem) (a n : Nat) : SameOutside s t a n := by
  intro q b away;simp only [byte,MachineState.getByte,MachineState.getMem,same]
theorem bothRows {s t u : MachineState} (left : SameOutside s t 512 96) (right : SameOutside t u 512 96) :
    SameOutside s u 512 96:=left.combined right ⟨le_rfl,le_rfl,le_rfl,le_rfl⟩
theorem bothScratch {s t u : MachineState} (left : SameOutside s t 256 352) (right : SameOutside t u 256 352) :
    SameOutside s u 256 352:=left.combined right ⟨le_rfl,le_rfl,le_rfl,le_rfl⟩
end CommitGolfCandidate.S4.Machine
