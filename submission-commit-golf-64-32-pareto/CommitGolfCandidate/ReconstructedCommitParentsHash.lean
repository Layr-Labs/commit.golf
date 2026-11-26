import CommitGolfCandidate.ReconstructedCommitParentsLine
import CommitGolfCandidate.CopyRefinement

namespace CommitGolfCandidate.Reconstruction.CommitParents
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding CommitExact
open Image (Atom)
set_option maxRecDepth 8192
set_option maxHeartbeats 700000

def hashOps (d : Nat) : List Atom := .compress :: Image.rehash d

theorem hash_phase (o : Oracle) (im : CommitGolf.Riscv.Image) (s : MachineState) (d src dst : Nat)
    (srcRoom : src+64 ≤ MEMORY_BYTES) (dstRoom : dst+64 ≤ MEMORY_BYTES)
    (srcAlign : src%8=0) (dstAlign : dst%8=0) (key : Key)
    (read : readBuffer s src 64 = encodeKey key) (zero : cell s (dst+32)=zeroDigest)
    (regs : s.getReg .x5=0 ∧ s.getReg .x10=BitVec.ofNat 64 src ∧ s.getReg .x11=64 ∧
      s.getReg .x12=BitVec.ofNat 64 dst ∧ s.getReg .x13=0)
    (f : Loaded im s.pc (hashOps d)) :
    ∃ t, Segment o im (hashOps d).length s t ∧ t.pc = s.pc+BitVec.ofNat 64 (4*(hashOps d).length) ∧
      cell t dst = rawC o (lastKey (rawC o) key (work d-1)) ∧ Frame dst s t ∧
      ∀ r, r ≠ .x10 → t.getReg r = s.getReg r := by
  let first := callAfter s o dst key
  have step := call_exact o im s src dst key srcRoom (by omega) srcAlign dstAlign
    regs.1 regs.2.1 regs.2.2.1 regs.2.2.2.1 regs.2.2.2.2 read (f.head s rfl)
  have range : dst+64 ≤ 2^64 := by unfold MEMORY_BYTES at dstRoom;omega
  obtain ⟨val,f₀⟩ := call_contents s o dst key (by omega)
  have kept : ∀ r, first.getReg r=s.getReg r := fun r => writeBits_register _ _ _ r
  have p₁ : first.pc = s.pc+4 := rfl
  by_cases h : 1 < work d
  · let move := execInstrBr first (.ADDI .x10 .x12 0)
    let n := work d-1
    have ops : Image.rehash d = .continueAtDst :: List.replicate n .compress := by simp [Image.rehash,h,n]
    have rem : Loaded im first.pc (.continueAtDst :: List.replicate n .compress) := by
      rw [p₁,←ops];exact f.tail
    have stepMove : Segment o im 1 first move :=
      plain o im first move _ (rem.head first rfl) rfl
    have p₂ : move.pc = first.pc+4 := rfl
    have keptMove (r : Reg) (diff : r ≠ .x10) : move.getReg r = s.getReg r := by
      unfold move
      rw [execInstrBr,MachineState.getReg_setPC,MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm diff),kept]
    have regs' : move.getReg .x5=0 ∧ move.getReg .x10=BitVec.ofNat 64 dst ∧ move.getReg .x11=64 ∧
        move.getReg .x12=BitVec.ofNat 64 dst ∧ move.getReg .x13=0 := by
      refine ⟨(keptMove _ (by decide)).trans regs.1,?_,(keptMove _ (by decide)).trans regs.2.2.1,
        (keptMove _ (by decide)).trans regs.2.2.2.1,(keptMove _ (by decide)).trans regs.2.2.2.2⟩
      change first.getReg .x12 + signExtend12 0 = _
      rw [kept,regs.2.2.2.1];exact BitVec.add_zero _
    let rest := continues move o dst key n
    have entries := rem.tail
    rw [←p₂] at entries
    have regCell (a : Nat) : cell move a = cell first a := by
      apply congrArg unpack;exact read_buffer_memory_congr _ _ rfl a 32
    have z : cell move (dst+32) = zeroDigest := (regCell _).trans
      ((congrArg unpack (f₀ (dst+32) 32 (by omega) (Or.inr le_rfl))).trans zero)
    obtain ⟨seg,value,frame⟩ := continue_exact move o im dst key n dstRoom dstAlign regs'
      ((regCell _).trans val) z (fun j hj t pc => by
        have h₁ := entries ⟨j,by simpa using hj⟩ t pc
        simpa only [List.getElem_replicate,Image.Atom.op] using h₁)
    have cp := continued_registers move o dst key n
    have l : (hashOps d).length = 1+1+n := by simp [hashOps,ops];omega
    refine ⟨rest,l ▸ compose (compose step stepMove) seg,?_,value,?_,fun r hr => (cp.2 r).trans (keptMove r hr)⟩
    · rw [l,cp.1,p₂,p₁,BitVec.add_assoc,BitVec.add_assoc,show 4*(1+1+n) = 4 + (4+4*n) by omega]
      simp only [BitVec.ofNat_add];rfl
    · apply f₀.trans
      intro a len lim dis
      exact (frame a len lim dis).trans (read_buffer_memory_congr move first rfl a len)
  · have n : work d-1 = 0 := by omega
    have l : (hashOps d).length=1 := by simp [hashOps,Image.rehash,h]
    refine ⟨first,l ▸ step,?_,?_,f₀,fun r _ => kept r⟩
    · rw [l];rfl
    · rw [n];exact val

end CommitGolfCandidate.Reconstruction.CommitParents
