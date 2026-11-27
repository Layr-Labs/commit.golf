import CommitGolfCandidate.R4bChunk
import CommitGolfCandidate.R4bTable
namespace CommitGolfCandidate.R4b
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open CommitGolfCandidate.S4
open Machine (W Safe Wrote byte proofBase)
open S4.Open (Sources)
def completed (n : Nat) := n-n%8

structure Cursor (tape : Nat→Byte) (n : Nat) (s : MachineState) : Prop where
  filled : ∀ j,j<completed n → byte s (proofBase+j)=tape j
  pending : n%8≠0 → ∀ j,j<8 → extractByte (s.getReg .x20) j=if j<n%8 then tape (completed n+j) else 0

theorem Cursor.mem {tape : Nat→Byte} {n : Nat} {s t : MachineState} (h : Cursor tape n s)
    (same : t.mem=s.mem) (carry : t.getReg .x20=s.getReg .x20) : Cursor tape n t := by
  refine ⟨fun j h' => ?_,fun nz j h'=>by rw [carry];exact h.pending nz j h'⟩
  simpa only [byte,MachineState.getByte,MachineState.getMem,same] using h.filled j h'

def Protect (s t : MachineState) := ∀ a,a<2^64 → (a<proofBase ∨ proofBase+65280≤a) → byte t a=byte s a
theorem Protect.trans {s t u : MachineState} (h : Protect s t) (k : Protect t u) : Protect s u :=
  fun _ a b=>(k _ a b).trans (h _ a b)
theorem Protect.ofMem {s t : MachineState} (h : t.mem=s.mem) : Protect s t := by
  intro a _ _;simp only [byte,MachineState.getByte,MachineState.getMem,h]
theorem Protect.sources {td : Late.Trapdoor} {ps : Positions} {s t : MachineState} (h : Protect s t)
    (known : Sources td ps s) : Sources td ps t := by
  intro q lo hi;rw [h q (by unfold Machine.valueBase at hi;omega) (Or.inl (by unfold Machine.valueBase proofBase at *;omega))]
  exact known q lo hi
theorem Protect.table {s t : MachineState} (h : Protect s t) (known : TableMem s) : TableMem t :=
  tableOfBytes known (fun a lo hi=>h a (by unfold tableBase at hi;omega) (Or.inr (by unfold proofBase tableBase at *;omega)))

theorem advanceWord {s t : MachineState} (tape : Nat→Byte) (k n : Nat) (v : Word)
    (fit : k+n≤65280) (nlen : n=6 ∨ n=8) (short : k%8+n<8 → k%8=0)
    (prior : Cursor tape k s) (input : ∀ j,j<n → extractByte v j=tape (k+j))
    (tail : (k%8+n)%8≠0 → t.getReg .x20=restWord (k%8) n v)
    (stored : if 8≤k%8+n then
      Wrote s t (proofBase+completed k) 8 (extractByte (mergeWord (k%8) v (s.getReg .x20))) else t.mem=s.mem) :
    Cursor tape (k+n) t ∧ Protect s t := by
  have r8:=Nat.mod_lt k (by decide : 0<8)
  have eqmod : (k+n)%8=(k%8+n)%8:=by omega
  have dest : proofBase+65280<2^64:=by decide
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro j hj
    by_cases flush:8≤k%8+n
    · rw [if_pos flush] at stored
      rw [stored (proofBase+j) (by unfold completed at hj;omega)]
      by_cases before:j<completed k
      · rw [if_neg (by omega)];exact prior.filled j before
      · rw [if_pos (by unfold completed at *;omega),show proofBase+j-(proofBase+completed k)=j-completed k by omega]
        let off:=j-completed k
        have idx : off<8:=by dsimp [off];unfold completed at *;omega
        have zeros : k%8≤off → k%8≠0 → extractByte (s.getReg .x20) off=0:=by
          intro above nz;rw [prior.pending nz _ idx,if_neg (by omega)]
        change extractByte _ off=_
        rw [byteMerge _ _ _ _ r8 idx zeros]
        split
        next carried=>
          rw [prior.pending (by omega) _ idx,if_pos carried];congr 1;dsimp [off];omega
        next fromInput=>
          rw [input _ (by dsimp [off] at *;unfold completed at *;omega)]
          congr 1;dsimp [off] at *;unfold completed at *;omega
    · rw [if_neg flush] at stored
      have eqB : byte t (proofBase+j)=byte s (proofBase+j):=by simp only [byte,MachineState.getByte,MachineState.getMem,stored]
      exact eqB.trans (prior.filled j (by unfold completed at *;omega))
  · intro nz j j8
    rw [eqmod] at nz
    rw [tail nz,byteRest _ _ _ _ r8 (by omega) j8 short nz,eqmod]
    split
    next inside=>
      rw [input _ (by split <;> omega)]
      congr 1;unfold completed;split <;> omega
    next =>rfl
  · by_cases flush:8≤k%8+n
    · rw [if_pos flush] at stored;intro a ha away
      rw [stored a ha,if_neg (by unfold completed;omega)]
    · rw [if_neg flush] at stored;exact Protect.ofMem stored

end CommitGolfCandidate.R4b
