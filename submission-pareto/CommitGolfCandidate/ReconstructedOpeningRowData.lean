import CommitGolfCandidate.ReconstructedOpeningLinear
import CommitGolfCandidate.ReconstructedCapWriter
import CommitGolfCandidate.ReconstructedOpeningBranch

namespace CommitGolfCandidate.Reconstruction.OpeningRowData
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel OpeningOps OpeningCursor OpeningPut
open TwoPermutationPrototype (Memory writeWord)
open TwoPermutationPrototype.RV64
set_option maxRecDepth 12000

/-- All three full words and the final short word use the same alignment. Logical
word numbers stay constant across the register allocation of the unrolled rows. -/
structure Data where
  root : Nat
  start : Nat
  bits : Nat
  word : Nat → Word
  initial : Model
  room : (root+start+192)/64 < capacity
  width : bits≤64

def atBit (x : Data) (k : Nat) := x.root+x.start+64*k
def off (x : Data) := (x.root+x.start)%64
def width (x : Data) (k : Nat) := if k=3 then x.bits else 64
def before (x : Data) : Nat → Memory
  | 0 => x.initial.mem
  | k+1 => put (before x k) (atBit x k) (width x k) (x.word k)

def addr (x : Data) (k : Nat) := wordAddress (cell (atBit x k))
def old (x : Data) (k : Nat) := before x k (cell (atBit x k))
def high (x : Data) (k : Nat) := x.word k >>> (64-off x)
def merged (x : Data) (k : Nat) := old x k ||| (x.word k <<< off x)
def tailMem (x : Data) (k : Nat) := writeWord (before x k) (cell (atBit x k)+1) (high x k)
def headMem (x : Data) (k : Nat) := writeWord (before x k) (cell (atBit x k)) (merged x k)

theorem alignment (x : Data) (k : Nat) : atBit x k%64=off x := by unfold atBit off;omega
theorem within (x : Data) (k : Nat) (h : k<4) : cell (atBit x k)+1<2^33 := by
  have room := x.room;unfold cell atBit base capacity at *;omega
theorem bounded (x : Data) (k : Nat) (h : k<4) : atBit x k<2^64 := by
  have room := x.room;unfold atBit capacity at *;omega
theorem off_value (x : Data) : (W (off x)).toNat%64=off x := by
  change (((x.root+x.start)%64)%2^64)%64=(x.root+x.start)%64;omega
theorem negative (x : Data) (nz : off x≠0) :
    (((0 : BitVec 32)-(W (off x)).truncate 32).signExtend 64).toNat%64=64-off x :=
  OpeningCursor.negative_shift ⟨off x,by unfold off;omega⟩ (Nat.pos_of_ne_zero nz)
theorem subtract (x : Data) (nz : off x≠0) : ((64 : Word)-W (off x)).toNat%64=64-off x := by
  exact (by decide : ∀ v : Fin 64, v.val≠0 → ((64 : Word)-W v.val).toNat%64=64-v.val)
    ⟨off x,by unfold off;omega⟩ nz

theorem full (x : Data) (k : Nat) (size : k<3) (nz : off x≠0) :
    writeWord (tailMem x k) (cell (atBit x k)) (merged x k)=before x (k+1) := by
  have h : atBit x k%64≠0 := by rw [alignment];exact nz
  unfold before width;rw [ite_eq_right (by omega : k≠3)]
  unfold tailMem merged old high;rw [←alignment x k]
  exact CapWriter.reverse_stores _ _ _ h

theorem aligned (x : Data) (k : Nat) (z : off x=0) :
    writeWord (before x k) (cell (atBit x k)) (x.word k)=before x (k+1) := by
  apply CapWriter.aligned_store _ _ _ _ ((alignment x k).trans z)
  unfold width;split <;> first | exact x.width | decide

theorem short (x : Data) (nz : off x≠0) (fits : off x+x.bits≤64) : headMem x 3=before x 4 := by
  change _=put (before x 3) (atBit x 3) x.bits (x.word 3)
  unfold put first headMem merged old
  simp only [alignment,nz,ite_false,ite_eq_right (by omega : ¬off x+x.bits>64)]

theorem crosses (x : Data) (nz : off x≠0) (cross : 64<off x+x.bits) :
    writeWord (headMem x 3) (cell (atBit x 3)+1) (high x 3)=before x 4 := by
  change _=put (before x 3) (atBit x 3) x.bits (x.word 3)
  unfold put first headMem merged old high
  simp only [alignment,nz,ite_false,cross,ite_true]

theorem keep_before (x : Data) (k w : Nat) (kbound : k≤4) (apart : w<base ∨ 8589934200<w) :
    before x k w=x.initial.mem w := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have ck : cell (atBit x k)+1≤8589934200 := by
      have r := x.room;unfold cell atBit base capacity at *;omega
    have lo : base≤cell (atBit x k) := by unfold cell;omega
    rw [before,keep _ _ _ _ _ (by omega) (by omega)]
    exact ih (by omega)

theorem keep_head (x : Data) (k w : Nat) (kbound : k<4) (apart : w<base ∨ 8589934200<w) :
    headMem x k w=x.initial.mem w := by
  have ck : cell (atBit x k)+1≤8589934200 := by
    have r := x.room;unfold cell atBit base capacity at *;omega
  have lo : base≤cell (atBit x k) := by unfold cell;omega
  change (if w=cell (atBit x k) then _ else _)=_
  rw [ite_eq_right (by omega : w≠cell (atBit x k))]
  exact keep_before x k w (by omega) apart

def withMem (m : Model) (mem : Memory) : Model := ⟨m.reg,mem⟩

theorem storeAs (o : Oracle) (m : Model) (rs rv : Reg) (imm : BitVec 12) (w : Nat) (v : Word) (mem : Memory)
    (room : w<2^33) (loc : m.reg rs+signExtend12 imm=wordAddress w) (value : m.reg rv=v)
    (effect : writeWord m.mem w v=mem) : Contract o [.SD rs rv imm] m (withMem m mem) := by
  rw [←effect];exact OpeningLinear.write o m rs rv imm w v room loc value

end CommitGolfCandidate.Reconstruction.OpeningRowData
