import CommitGolfCandidate.S5CheckInput
import CommitGolfCandidate.S5WireBytes
import CommitGolfCandidate.S5CheckCells
import CommitGolfCandidate.S5ReadField
namespace CommitGolfCandidate.S5Machine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W Outside)
attribute [local irreducible] initial
def HighInput (x : CheckInput) (s : MachineState) := ∀ q,rootBase≤q → q<MEMORY_BYTES → q%8=0 →
  Open.wordAt s q=Open.wordAt (initial x) q

theorem HighInput.read {x s} (h : HighInput x s) (a n : Nat) (base : rootBase≤a) (limit : a+n≤MEMORY_BYTES) :
    readBuffer s a n=readBuffer (initial x) a n := by
  unfold readBuffer;apply congrArg (BitVec.ofNat _);apply Finset.sum_congr rfl;intro j hj
  have edge:=Finset.mem_range.mp hj
  apply congrArg (fun w : Byte=>w.toNat*2^(8*j))
  change Open.byteAt s (a+j)=Open.byteAt (initial x) (a+j)
  have z : rootBase%8=0:=by decide
  rw [Open.byte_word,Open.byte_word (initial x),h _ (by omega) (by omega) (by omega)]
theorem HighInput.after {x s t a n} (h : HighInput x s) (far : Outside s t a n) (low : a+n≤rootBase) : HighInput x t :=
  fun q edge bounds align=>(far q bounds align (Or.inr (by omega))).trans (h q edge bounds align)
theorem HighInput.same {x s t} (h : HighInput x s) (m : t.mem=s.mem) : HighInput x t :=
  fun q e b al=>(congrFun m _).trans (h q e b al)

end CommitGolfCandidate.S5Machine.Check
