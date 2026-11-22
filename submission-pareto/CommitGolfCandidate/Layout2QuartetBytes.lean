import CommitGolfCandidate.Layout2QuartetImage
import CommitGolfCandidate.Layout2Invariant

namespace CommitGolfCandidate.Layout2.Quartet
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxHeartbeats 1200000

theorem block_bytes {s t : MachineState} {B : Nat} {q : Fin 4}
    (aligned : B%8=0) (room : B+200≤MEMORY_BYTES)
    (cells : ∀ d : Cell, t.getMem (key B d)=s.getMem (addr (B+16+8*wordAt false q d)))
    (frame : ∀ a : Word, (∀ d, a≠key B d) → t.getMem a=s.getMem a)
    (a : Nat) (fit : a<MEMORY_BYTES) :
    byte t a=if B+16≤a ∧ a<B+200 then
      byte s (B+16+8*wordAt false q ((a-(B+16))/8)+(a-(B+16))%8)
      else byte s a := by
  have memlim : MEMORY_BYTES<2^64 := by decide
  split
  · rename_i hit
    let d : Cell := ⟨(a-(B+16))/8,by omega⟩
    let lane := (a-(B+16))%8
    have low : lane<8 := by dsimp [lane];omega
    have atOut := Layout2Writer.aligned_byte' t (B+16+8*d.val) lane (by omega) low
    have atIn := Layout2Writer.aligned_byte' s (B+16+8*wordAt false q d) lane (by omega) low
    have eq : B+16+8*d.val+lane=a := by dsimp [d,lane];omega
    rw [eq] at atOut
    exact atOut.trans ((congrArg (fun v=>extractByte v lane) (cells d)).trans atIn.symm)
  · rename_i miss
    let base:=8*(a/8)
    have away (d : Cell) : addr base≠key B d := by
      intro e
      have eq:=congrArg BitVec.toNat e
      have di:=d.isLt
      simp only [key,addr,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show base<2^64 by dsimp [base];omega),
        Nat.mod_eq_of_lt (show B+16+8*d.val<2^64 by omega)] at eq
      dsimp [base] at eq;omega
    have mt:=Layout2Writer.aligned_byte' t base (a%8) (by dsimp [base];omega) (by omega)
    have ms:=Layout2Writer.aligned_byte' s base (a%8) (by dsimp [base];omega) (by omega)
    rw [show base+a%8=a by dsimp [base];omega] at mt ms
    exact mt.trans ((congrArg (fun z=>extractByte z (a%8)) (frame _ away)).trans ms.symm)

/-- The kernel is a complete byte-frame operation on one nominal cell, including its
unaligned endpoints. This is the form consumed by a sorted-record traversal. -/
theorem cell_run (s : MachineState) (j : Nat) (q : Fin 4)
    (base : s.getReg .x8=addr (proofBase+8*((534*j)/8)))
    (room : proofBase+534*(j+1)≤MEMORY_BYTES) (here : s.pc=pc (body q)) :
    ∃ t, Runs checkImage s t 46 46 ∧ t.pc=pc (body q+46) ∧
      Writes s t (proofBase+534*j) 534
        (fun x=>byte s (proofBase+534*j+within false q (window j) x)) ∧
      (∀ r : Reg, r≠.x28 → r≠.x29 → t.getReg r=s.getReg r) := by
  let B:=proofBase+8*((534*j)/8)
  have alg : B%8=0 := by dsimp [B,proofBase];omega
  have span : B+200≤MEMORY_BYTES := by dsimp [B];omega
  obtain ⟨t,run,pcT,cells,frame,regs⟩:=kernel_run s B q base alg span here
  refine ⟨t,run,pcT,?_,regs⟩
  intro a fit
  rw [block_bytes alg span cells frame a fit]
  have offset:=window_base j
  have left : B+16=proofBase+534*j+window j := by dsimp [B];omega
  have w : window j≤16 := by unfold window;omega
  by_cases inCell : proofBase+534*j≤a ∧ a<proofBase+534*j+534
  · rw [if_pos inCell]
    dsimp only
    unfold within
    by_cases active : B+16≤a ∧ a<B+200
    · rw [if_pos active,if_pos (by omega : window j≤a-(proofBase+534*j) ∧ a-(proofBase+534*j)<window j+184)]
      have e : a-(B+16)=a-(proofBase+534*j)-window j := by omega
      rw [e];congr 1;omega
    · rw [if_neg active,if_neg (by omega : ¬(window j≤a-(proofBase+534*j) ∧ a-(proofBase+534*j)<window j+184))]
      congr 1;omega
  · rw [if_neg inCell,if_neg (by omega : ¬(B+16≤a ∧ a<B+200))]

end CommitGolfCandidate.Layout2.Quartet
