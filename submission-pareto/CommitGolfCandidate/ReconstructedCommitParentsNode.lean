import CommitGolfCandidate.ReconstructedCommitParentsPointers
import CommitGolfCandidate.ReconstructedCommitParentsMark
import CommitGolfCandidate.ReconstructedCommitParentsHash
import CommitGolfCandidate.ReconstructedCommitParentsHeap

namespace CommitGolfCandidate.Reconstruction.CommitParents
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding CommitExact
open Image (Atom)
set_option maxRecDepth 10000
set_option maxHeartbeats 1500000
attribute [local irreducible] readBuffer

structure NodeRegisters (d : Fin 24) (s : MachineState) : Prop where
  hash : s.getReg .x5=0 ∧ s.getReg .x11=64 ∧ s.getReg .x13=0
  masks : aux d s
  label : modulus (d.val+1) ≠ 0 → s.getReg .x23=BitVec.ofNat 64 (d.val+1)

structure NodeWrites (src dst : Nat) (s t : MachineState) : Prop where
  frame : ∀ a len, a+len ≤ 2^64 → (a+len ≤ dst ∨ dst+32 ≤ a) →
    (a+len ≤ src+32 ∨ src+64 ≤ a) → readBuffer t a len = readBuffer s a len

theorem Frame.cell_at {a dst : Nat} {s t : MachineState} (f : Frame dst s t)
    (small : a+32 ≤ 2^64) (sep : a+32 ≤ dst ∨ dst+32 ≤ a) :
    cell t a = cell s a := congrArg unpack (f a 32 small sep)

private theorem body_split (d i : Nat) :
    Image.body d i = headOps i ++ (Image.mark d ++ (outOps i ++ (hashOps d ++ Image.save d))) := by
  simp [Image.body,headOps,outOps,hashOps,List.append_assoc]

private theorem masks_of_registers {d : Nat} {s t : MachineState} (h : aux d s)
    (r17 : t.getReg .x17 = s.getReg .x17) (r21 : t.getReg .x21 = s.getReg .x21) : aux d t :=
  ⟨fun a => r17.trans (h.1 a),fun a => r21.trans (h.2.1 a),fun a b => r21.trans (h.2.2 a b)⟩

private theorem pc_join (p : Word) (m n : Nat) :
    p+BitVec.ofNat 64 (4*m)+BitVec.ofNat 64 (4*n)=p+BitVec.ofNat 64 (4*(m+n)) := by
  rw [BitVec.add_assoc,←BitVec.ofNat_add,Nat.mul_add]

/-- Complete execution of one tag/write/hash/project body at a legal node. -/
theorem node_step (o : Oracle) (im : CommitGolf.Riscv.Image) (s : MachineState) (d : Fin 24)
    (i src dst : Nat) (srcRoom : src+64 ≤ MEMORY_BYTES) (dstRoom : dst+64 ≤ MEMORY_BYTES)
    (srcA : src%8=0) (dstA : dst%8=0) (sep : dst+64 ≤ src)
    (l r : Binding.Digest) (can : Canonical (d.val+1) r)
    (left : cell s src = written (d.val+1) l) (right : cell s (src+32) = written (d.val+1) r)
    (zero : cell s (dst+32)=zeroDigest)
    (inPtr : srcReg s i+signExtend12 (Image.sourceImm ⟨i%64,by omega⟩) = BitVec.ofNat 64 src)
    (outPtr : dstReg s i+signExtend12 (Image.destImm ⟨i%128,by omega⟩) = BitVec.ofNat 64 dst)
    (regs : NodeRegisters d s) (f : Loaded im s.pc (Image.body d i)) :
    ∃ t, Segment o im (Image.body d i).length s t ∧ t.pc=s.pc+BitVec.ofNat 64 (4*(Image.body d i).length) ∧
      cell t dst = written d (parent (rawC o) d l r) ∧ cell t (src+32) = marked (d.val+1) true r ∧
      NodeWrites src dst s t ∧ t.getReg .x18=srcReg s i ∧ t.getReg .x19=dstReg s i ∧
      t.getReg .x12=BitVec.ofNat 64 dst ∧
      ∀ q, q ≠ .x6 → q ≠ .x10 → q ≠ .x12 → q ≠ .x18 → q ≠ .x19 → t.getReg q=s.getReg q := by
  rw [body_split] at f
  obtain ⟨fh,f⟩ := f.split
  let a := runPlain s (headOps i)
  obtain ⟨sh,ph⟩ := plain_segment o im s (headOps i) fh (head_ready s i)
  change Segment o im _ s a at sh
  change a.pc = _ at ph
  obtain ⟨am,ptr,sreg,dreg,ar⟩ := head_regs s i
  change a.mem = _ at am
  rw [←ph] at f
  obtain ⟨fm,f⟩ := f.split
  let b := markAfter a d
  obtain ⟨sm,pm,rb,fb,br⟩ := mark_step o im d a src srcA srcRoom (ptr.trans inPtr)
    (fun m => (ar _ (by decide) (by decide) (by decide)).trans (regs.label m))
    r can ((cell_congr am _).trans right) fm
  change Segment o im _ a b at sm
  change b.pc = _ at pm
  rw [←pm] at f
  obtain ⟨fo,f⟩ := f.split
  let c := runPlain b (outOps i)
  obtain ⟨so,po⟩ := plain_segment o im b (outOps i) fo (out_ready b i)
  obtain ⟨cm,det,cr⟩ := out_regs b i
  change c.mem=b.mem at cm
  change c.pc=_ at po
  rw [←po] at f
  obtain ⟨fk,fs⟩ := f.split
  have dstPointer : c.getReg .x12 = BitVec.ofNat 64 dst := by
    rw [det,br,dreg,outPtr]
  have srcBound : src+64 ≤ 2^64 := by unfold MEMORY_BYTES at srcRoom;omega
  have dstBound : dst+64 ≤ 2^64 := by omega
  have key : readBuffer c src 64 = encodeKey (pairKey (d.val+1) l r) := by
    rw [pair_read c src srcA,cell_congr cm,fb.cell_at (by omega) (Or.inl le_rfl),cell_congr am,left,
      cell_congr cm,rb]
    rfl
  have z : cell c (dst+32)=zeroDigest := by
    rw [cell_congr cm,fb.cell_at (by omega) (Or.inl (by omega)),cell_congr am,zero]
  have keep (q : Reg) (x10 : q ≠ .x10) (x12 : q ≠ .x12) (x18 : q ≠ .x18) (x19 : q ≠ .x19) :
      c.getReg q = s.getReg q := (cr _ x12).trans ((br _).trans (ar _ x10 x18 x19))
  obtain ⟨v,sk,pk,raw,fv,vr⟩ := hash_phase o im c d src dst srcRoom dstRoom srcA dstA _ key z
    ⟨(keep _ (by decide) (by decide) (by decide) (by decide)).trans regs.hash.1,
      (cr _ (by decide)).trans ((br _).trans (ptr.trans inPtr)),
      (keep _ (by decide) (by decide) (by decide) (by decide)).trans regs.hash.2.1,dstPointer,
      (keep _ (by decide) (by decide) (by decide) (by decide)).trans regs.hash.2.2⟩ fk
  rw [←pk] at fs
  have vptr := (vr _ (show Reg.x12 ≠ .x10 by decide)).trans dstPointer
  have va := masks_of_registers regs.masks
    ((vr _ (by decide)).trans (keep _ (by decide) (by decide) (by decide) (by decide)))
    ((vr _ (by decide)).trans (keep _ (by decide) (by decide) (by decide) (by decide)))
  let t := runPlain v (Image.save d)
  obtain ⟨ss,ps⟩ := plain_segment o im v (Image.save d) fs (save_ready d v dst (by omega) dstA vptr)
  obtain ⟨result,ft,tr⟩ := save_effect d v dst (by omega) dstA vptr va
  change t.pc = _ at ps
  let both := fv.trans ft
  have tc (q : Reg) (q6 : q ≠ .x6) (q10 : q ≠ .x10) : t.getReg q=c.getReg q :=
    (tr _ q6).trans (vr _ q10)
  refine ⟨t,?_,?_,?_,?_,⟨?_⟩,?_,?_,(tc _ (by decide) (by decide)).trans dstPointer,?_⟩
  · simpa only [body_split,List.length_append,Nat.add_assoc] using compose sh (compose sm (compose so (compose sk ss)))
  · rw [ps,pk,po,pm,ph,pc_join,pc_join,pc_join,pc_join,body_split]
    simp [Nat.add_assoc]
  · rw [result,raw];rfl
  · rw [both.cell_at (by omega) (Or.inr (by omega)),cell_congr cm,rb]
  · intro a' len h hd hs
    exact (both a' len h hd).trans ((read_buffer_memory_congr _ _ cm _ _).trans
      ((fb a' len h hs).trans (read_buffer_memory_congr _ _ am _ _)))
  · exact (tc _ (by decide) (by decide)).trans ((cr _ (by decide)).trans ((br _).trans sreg))
  · exact (tc _ (by decide) (by decide)).trans ((cr _ (by decide)).trans ((br _).trans dreg))
  · intro q h6 h10 h12 h18 h19
    exact (tc q h6 h10).trans (keep q h10 h12 h18 h19)

end CommitGolfCandidate.Reconstruction.CommitParents
