import CommitGolfCandidate.S5Trapdoor
import CommitGolfCandidate.InputMemory

namespace CommitGolfCandidate.S5Machine.Open
open CommitGolfCandidate.Late (bytes)
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def W (n : Nat) := BitVec.ofNat 64 n

def wordAt (s : MachineState) (a : Nat) := s.getMem (BitVec.ofNat 64 a)
def byteAt (s : MachineState) (a : Nat) := s.getByte (BitVec.ofNat 64 a)

def indexBase := 8589934592
def proofBase := 13421772800
def tdEnd := 7113551872

theorem byte_word (s : MachineState) (a : Nat) :
    byteAt s a = extractByte (wordAt s (8*(a/8))) (a%8) := by
  have same := aligned_byte s (a/8) (a%8) (by omega)
  simpa only [Nat.div_add_mod a 8, Nat.div_eq_of_lt (Nat.mod_lt a (by decide : 0<8)),
    Nat.mul_zero,Nat.add_zero,Nat.mod_eq_of_lt (Nat.mod_lt a (by decide : 0<8)),byteAt,wordAt] using same

/-- All aligned words outside the written interval keep their former value. -/
def Outside (s t : MachineState) (base size : Nat) := ∀ a < MEMORY_BYTES, a%8=0 →
  a<base ∨ base+size≤a → wordAt t a=wordAt s a

theorem outside_byte {s t : MachineState} {b n : Nat} (same : Outside s t b n)
    (start : b%8=0) (len : n%8=0) {a : Nat} (inside : a<MEMORY_BYTES) (away : a<b ∨ b+n≤a) :
    byteAt t a=byteAt s a := by
  rw [byte_word,byte_word s, same (8*(a/8)) (by omega) (by omega) (by omega)]

theorem outside_read {s t : MachineState} {b n : Nat} (same : Outside s t b n)
    (start : b%8=0) (len : n%8=0) (addr count : Nat) (inside : addr+count≤MEMORY_BYTES)
    (away : addr+count≤b ∨ b+n≤addr) : readBuffer t addr count=readBuffer s addr count := by
  unfold readBuffer
  apply congrArg (BitVec.ofNat _)
  apply Finset.sum_congr rfl
  intro k hk
  have edge := Finset.mem_range.mp hk
  have eq := outside_byte same start len (a:=addr+k) (by omega) (by omega)
  exact congrArg (fun z : Byte => z.toNat * 2^(8*k)) eq

def HasBytes (s : MachineState) (a : Nat) (bs : List Byte) := ∀ i (hi : i<bs.length),
  byteAt s (a+i) = bs[i]

structure Written (s t : MachineState) (a : Nat) (bs : List Byte) : Prop where
  outside : Outside s t a bs.length
  data : HasBytes t a bs

theorem Written.empty (s : MachineState) (a : Nat) : Written s s a [] :=
  ⟨fun _ _ _ _ => rfl,fun _ hi => by simp at hi⟩

theorem Written.append {s t u : MachineState} {a : Nat} {xs ys : List Byte}
    (x : Written s t a xs) (y : Written t u (a+xs.length) ys)
    (aligned : (a+xs.length)%8=0) (whole : ys.length%8=0) (bounded : a+xs.length≤MEMORY_BYTES) :
    Written s u a (xs++ys) := by
  constructor
  · intro w hw al outside
    simp only [List.length_append] at outside
    exact (y.outside w hw al (by omega)).trans (x.outside w hw al (by omega))
  · intro i hi
    by_cases left : i<xs.length
    · rw [List.getElem_append_left left]
      exact (outside_byte y.outside aligned whole (by omega) (by omega)).trans (x.data i left)
    · have right : i-xs.length<ys.length := by simp only [List.length_append] at hi; omega
      rw [List.getElem_append_right (by omega)]
      simpa only [show a+xs.length+(i-xs.length)=a+i by omega] using y.data _ right

theorem Written.congr_mem {s t s' t' : MachineState} {a : Nat} {xs : List Byte}
    (w : Written s t a xs) (b : s'.mem=s.mem) (e : t'.mem=t.mem) : Written s' t' a xs := by
  constructor
  · intro q hi al out
    simpa only [wordAt,MachineState.getMem,b,e] using w.outside q hi al out
  · intro q hq
    simpa only [byteAt,MachineState.getByte,MachineState.getMem,e] using w.data q hq

theorem read_bytes (s : MachineState) (a n : Nat) (v : BitVec (8*n)) (read : readBuffer s a n=v) :
    HasBytes s a (bytes v) := by
  intro j hj
  have b : j<n := by simpa only [bytes,List.length_ofFn] using hj
  simp only [bytes,List.getElem_ofFn]
  exact (read_buffer_byte s a n j b).symm.trans (congrArg (fun x : BitVec (8*n) => x.extractLsb' (8*j) 8) read)

end CommitGolfCandidate.S5Machine.Open
