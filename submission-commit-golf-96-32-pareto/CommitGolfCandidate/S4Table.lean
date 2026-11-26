import CommitGolfCandidate.S4Seen
import CommitGolfCandidate.S4Auth
namespace CommitGolfCandidate.S4.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (Digest)
def upperAddr (i : Nat) := 16384+32*i
def capAddr (i : Nat) := 2048+32*i
def flagAddr (i : Nat) := 768+i
def HighExcept (s t : MachineState) (dst len : Nat) :=
  ∀ q,608≤q → q<2^64 → (q<dst ∨ dst+len≤q) → byte t q=byte s q

theorem HighExcept.read {s t : MachineState} {dst len a n : Nat} (e : HighExcept s t dst len)
    (lo : 608≤a) (hi : a+n≤2^64) (out : a+n≤dst ∨ dst+len≤a) : readBuffer t a n=readBuffer s a n:=by
  unfold readBuffer;apply congrArg (BitVec.ofNat _);apply Finset.sum_congr rfl;intro j bj
  have hb:=Finset.mem_range.mp bj
  exact congrArg (fun x : Byte=>x.toNat*2^(8*j)) (e (a+j) (by omega) (by omega) (by omega))

theorem highOnly {s t : MachineState} {a n dst len : Nat} (e : SameOutside s t a n) (scratch : a+n≤608) :
    HighExcept s t dst len:=fun q lo hi _=>e q hi (Or.inr (by omega))
theorem HighExcept.trans {s t u : MachineState} {a n : Nat} (l : HighExcept s t a n) (r : HighExcept t u a n) :
    HighExcept s u a n:=fun q lo hi out=>(r q lo hi out).trans (l q lo hi out)
theorem highWrite {s t : MachineState} {a n : Nat} (w : SameOutside s t a n) : HighExcept s t a n:=
  fun q _ hi out=>w q hi out
theorem HighExcept.env {s t : MachineState} {a n : Nat} {x : CheckInput}
    (e : HighExcept s t a n) (endA : a+n≤32768) (old : InputsStill x s) : InputsStill x t:=
  fun q lo hi=>(e q (by omega) hi (Or.inr (by omega))).trans (old q lo hi)

def capValue (H : Compression) (v : View) (j : Nat) := batchCap .byte H v j
def nodeValue (H : Compression) (v : View) (k j : Nat) := upper .byte H (capValue H v) k j
def Level (H : Compression) (v : View) (k : Nat) (s : MachineState) :=
  ∀ j<width (16+k),readBuffer s (upperAddr j) 32=nodeValue H v k j

theorem missingUpper (H : Compression) (v : View) (k j : Nat) (off : width (16+k)≤j) :
    nodeValue H v k j=0:=by
  cases k with
  | zero=>change (if j<171 then _ else _)=_;exact if_neg (by change 171≤j at off;omega)
  | succ k=>
    change (if j<width (17+k) then _ else _)=_;exact if_neg (by rw [show 16+(k+1)=17+k by omega] at off;omega)

def rowInput (H : Compression) (v : View) (k i : Nat) :=
  Late.parentBlock (nodeValue H v k (2*i)) (nodeValue H v k (2*i+1))
theorem nextUpper (H : Compression) (v : View) (k i : Nat) (inside : i<width (17+k)) :
    nodeValue H v (k+1) i=retained .byte (17+k) (H (rowInput H v k i)):=if_pos inside

structure RowMemory (H : Compression) (v : View) (k i : Nat) (s : MachineState) : Prop where
  done : ∀ j < i,readBuffer s (upperAddr j) 32=nodeValue H v (k+1) j
  rest : ∀ j,2*i≤j → j<2*width (17+k) → readBuffer s (upperAddr j) 32=nodeValue H v k j

private theorem upperCounts : ∀ k : Fin 8,width (16+k.val)≤2*width (17+k.val) ∧ 2*width (17+k.val)≤width (16+k.val)+1 ∧
    0<width (17+k.val) ∧ width (16+k.val)≤171 := by decide
theorem upperBounds (k : Nat) (bk : k<8) : width (16+k)≤2*width (17+k) ∧ 2*width (17+k)≤width (16+k)+1 ∧
    0<width (17+k) ∧ width (16+k)≤171 := upperCounts ⟨k,bk⟩

theorem rowStartMemory (H : Compression) (v : View) (k : Nat) (bk : k<8) (s : MachineState) (old : Level H v k s)
    (pad : width (16+k)<2*width (17+k) → readBuffer s (upperAddr (width (16+k))) 32=0) : RowMemory H v k 0 s:=by
  refine ⟨fun _ b=>False.elim (by omega),?_⟩
  intro j _ lim
  by_cases valid:j<width (16+k)
  · exact old j valid
  · have bounds:=upperBounds k bk
    have e:j=width (16+k):=by omega
    exact e ▸ (pad (by omega)).trans (missingUpper H v k _ le_rfl).symm

theorem rowNextMemory (H : Compression) (v : View) (k i : Nat) (bk : k<8) (inside : i<width (17+k))
    (s t : MachineState) (before : RowMemory H v k i s)
    (value : readBuffer t (upperAddr i) 32=nodeValue H v (k+1) i)
    (frame : HighExcept s t (upperAddr i) 32) : RowMemory H v k (i+1) t:=by
  have bounds:=upperBounds k bk
  constructor
  · intro j bj;by_cases same:j=i
    · subst j;exact value
    · exact (frame.read (a:=upperAddr j) (n:=32) (by unfold upperAddr;omega) (by unfold upperAddr;omega) (Or.inl (by unfold upperAddr;omega))).trans (before.done j (by omega))
  · intro j lo hi
    exact (frame.read (a:=upperAddr j) (n:=32) (by unfold upperAddr;omega) (by unfold upperAddr;omega)
      (Or.inr (by unfold upperAddr;omega))).trans (before.rest j (by omega) hi)
end CommitGolfCandidate.S4.Machine
