import CommitGolfCandidate.ReconstructedCommitParentsSave

namespace CommitGolfCandidate.Reconstruction.CommitParents
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding
set_option maxRecDepth 8192

def markAfter (s : MachineState) (d : Fin 24) := runPlain s (Image.mark d)

private theorem add62 (a : Nat) : BitVec.ofNat 64 a + signExtend12 62 = BitVec.ofNat 64 (a+62) :=
  (BitVec.ofNat_add ..).symm

theorem mark_step (o : Oracle) (im : CommitGolf.Riscv.Image) (d : Fin 24) (s : MachineState) (src : Nat)
    (align : src%8=0) (room : src+64 ≤ MEMORY_BYTES)
    (pointer : s.getReg .x10=BitVec.ofNat 64 src)
    (label : modulus (d+1) ≠ 0 → s.getReg .x23=BitVec.ofNat 64 (d.val+1))
    (x : Binding.Digest) (can : Canonical (d.val+1) x) (prior : cell s (src+32) = written (d.val+1) x)
    (fetch : Loaded im s.pc (Image.mark d)) :
    let t := markAfter s d
    CommitExact.Segment o im (Image.mark d).length s t ∧ t.pc = s.pc+BitVec.ofNat 64 (4*(Image.mark d).length) ∧
    cell t (src+32) = marked (d.val+1) true x ∧ Frame (src+32) s t ∧ ∀ r, t.getReg r = s.getReg r := by
  have small : src+64 ≤ 2^64 := by unfold MEMORY_BYTES at room;omega
  by_cases modded : modulus (d.val+1) = 0
  · have empty : Image.mark d = [] := by simp [Image.mark,modded]
    have yes := plain_segment o im s (Image.mark d) fetch (by rw [empty];trivial)
    refine ⟨yes.1,yes.2,?_,?_,?_⟩
    · simp only [markAfter,empty,runPlain,prior,written,Nat.succ_ne_zero,ite_false]
      simp [marked,childMask,modded]
    · rw [markAfter,empty];exact fun _ _ _ _ => rfl
    · rw [markAfter,empty];exact fun _ => rfl
  · have single : Image.mark d = [.labelRight] := by simp [Image.mark,modded]
    have loc : s.getReg .x10 + signExtend12 62 = BitVec.ofNat 64 ((src+32)+30) := by
      rw [pointer,add62,show src+62=(src+32)+30 by omega]
    have access : accessValid (BitVec.ofNat 64 ((src+32)+30)) 2 = true := by
      simp only [accessValid,rangeValid,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show src+32+30<2^64 by omega),
        Bool.and_eq_true,decide_eq_true_eq]
      exact ⟨by omega,by omega⟩
    have loc' : s.getReg .x10 + signExtend12 62#12 = BitVec.ofNat 64 ((src+32)+30) := loc
    have ok : ready s (Image.mark d) := by simp [single,ready,Image.Atom.op,memoryArgumentsValid,memAccess,loc',access]
    have h := plain_segment o im s (Image.mark d) fetch ok
    have count : d.val+1 < 25 := by have := d.isLt;omega
    have hi := congrArg Prod.snd ((cell_words s (src+32) (by omega)).symm.trans prior)
    change atWord s (src+32+24) = (written (d.val+1) x).2 at hi
    have value := consumed_residue_right ⟨d.val+1,count⟩ (by simp) modded x can
    let high := (marked (d.val+1) true x).2
    have mapped : (markAfter s d).mem = (putTop s (src+32) high).mem := by
      simp only [markAfter,single,runPlain,Image.Atom.op,execInstrBr]
      rw [loc,label modded,half_store _ _ _ (by omega),hi]
      change _ = (putTop s (src+32) high).mem
      rw [value]
      rfl
    refine ⟨h.1,h.2,?_,?_,?_⟩
    · rw [cell_congr mapped,putTop_cell _ _ _ (by omega) (by omega),prior]
      simp [written,marked,high]
    · intro a n bound sep
      exact (read_buffer_memory_congr _ _ mapped a n).trans (putTop_frame s (src+32) high (by omega) (by omega) a n bound sep)
    · intro r
      rw [markAfter,single]
      rfl

end CommitGolfCandidate.Reconstruction.CommitParents
