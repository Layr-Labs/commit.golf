import CommitGolfCandidate.ReconstructedCommitParentsAdvance
import CommitGolfCandidate.ReconstructedCommitParentsReceipts

namespace CommitGolfCandidate.Reconstruction.CommitParents
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding CommitExact
attribute [local irreducible] readBuffer
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000

def srcCentre (d k i : Nat) := addr (d+1) (2*k)+2048+4096*((i-1)/64)
def dstCentre (d k i : Nat) := addr d k+2048+4096*((i-1)/128)

structure Cursor (d : Fin 24) (k i : Nat) (s : MachineState) : Prop where
  pc : s.pc = CommitBlocks.addr (Image.start d i)
  regs : NodeRegisters d s
  step : s.getReg .x22=4096
  src : s.getReg .x18 = BitVec.ofNat 64 (srcCentre d k i)
  dst : s.getReg .x19 = BitVec.ofNat 64 (dstCentre d k i)

def Outside (s t : MachineState) :=
  ∀ a n, a+n ≤ 2^64 → (a+n≤4294971424 ∨ 5637148528-128≤a) → readBuffer t a n=readBuffer s a n

theorem Outside.refl (s : MachineState) : Outside s s := fun _ _ _ _ => rfl

theorem Outside.trans {s t u} (f : Outside s t) (g : Outside t u) : Outside s u :=
  fun a n h h' => (g a n h h').trans (f a n h h')

theorem Outside.of_mem {s t : MachineState} (eq : t.mem=s.mem) : Outside s t :=
  fun a n _ _ => read_buffer_memory_congr _ _ eq a n

theorem Outside.of_writes {s t : MachineState} {d k : Nat} (depth : d<24)
    (lo : 2^d ≤ k) (hi : k<2^(d+1))
    (f : NodeWrites (addr (d+1) (2*k)) (addr d k) s t) : Outside s t := by
  have b := parent_memory_bounds d k depth lo hi
  intro a n h dis
  apply f.frame a n h <;> omega

theorem src_step {d k i s} (c : Cursor d k i s) :
    srcReg s i=BitVec.ofNat 64 (srcCentre d k (i+1)) := by
  unfold srcReg
  split
  · rw [c.src,c.step,←show BitVec.ofNat 64 4096=4096 by rfl,←BitVec.ofNat_add]
    congr 1;unfold srcCentre;omega
  · rw [c.src];congr 1;unfold srcCentre;omega

theorem dst_step {d k i s} (c : Cursor d k i s) :
    dstReg s i=BitVec.ofNat 64 (dstCentre d k (i+1)) := by
  unfold dstReg
  split
  · rw [c.dst,c.step,←show BitVec.ofNat 64 4096=4096 by rfl,←BitVec.ofNat_add]
    congr 1;unfold dstCentre;omega
  · rw [c.dst];congr 1;unfold dstCentre;omega

private theorem address_step (x n : Nat) :
    CommitBlocks.addr x+BitVec.ofNat 64 (4*n)=CommitBlocks.addr (x+n) := by
  unfold CommitBlocks.addr
  rw [←BitVec.ofNat_add];congr 1;omega

private theorem ptr1 {d k i s} (c : Cursor d k i s) :
    srcReg s i + signExtend12 (Image.sourceImm ⟨i%64,by omega⟩) = BitVec.ofNat 64 (addr (d.val+1) (2*(k+i))) := by
  rw [src_step c,source_disp]
  let a := addr (d.val+1) (2*(k+i))
  have large : 64*(i%64) ≤ a + 2048 := by dsimp [a,addr];omega
  have eq : srcCentre d k (i+1)=a+2048-64*(i%64) := by unfold srcCentre a addr;omega
  rw [eq];exact centre_add _ _ large

private theorem ptr2 {d k i s} (c : Cursor d k i s) :
    dstReg s i + signExtend12 (Image.destImm ⟨i%128,by omega⟩) = BitVec.ofNat 64 (addr d (k+i)) := by
  rw [dst_step c,dest_disp]
  let a := addr d (k+i)
  have large : 32*(i%128) ≤ a + 2048 := by dsimp [a,addr];omega
  have eq : dstCentre d k (i+1)=a+2048-32*(i%128) := by unfold dstCentre a addr;omega
  rw [eq];exact centre_add _ _ large

private theorem stable_regs {d : Fin 24} {s t : MachineState} (old : NodeRegisters d s)
    (keep : ∀ q : Reg, q ≠ .x6 → q ≠ .x10 → q ≠ .x12 → q ≠ .x18 → q ≠ .x19 → t.getReg q=s.getReg q) :
    NodeRegisters d t := by
  have k5 := keep .x5 (by decide) (by decide) (by decide) (by decide) (by decide)
  have k11 := keep .x11 (by decide) (by decide) (by decide) (by decide) (by decide)
  have k13 := keep .x13 (by decide) (by decide) (by decide) (by decide) (by decide)
  have k17 := keep .x17 (by decide) (by decide) (by decide) (by decide) (by decide)
  have k21 := keep .x21 (by decide) (by decide) (by decide) (by decide) (by decide)
  have k23 := keep .x23 (by decide) (by decide) (by decide) (by decide) (by decide)
  exact ⟨⟨k5.trans old.hash.1,k11.trans old.hash.2.1,k13.trans old.hash.2.2⟩,
    ⟨fun a=>k17.trans (old.masks.1 a),fun a=>k21.trans (old.masks.2.1 a),fun a b=>k21.trans (old.masks.2.2 a b)⟩,
    fun a=>k23.trans (old.label a)⟩

/-- A finite prefix of the actual unrolled body builds every successive
parent. The cursor may start at any legal group in the outer counted loop. -/
theorem group_prefix (o : Oracle) (d : Fin 24) (base : Nat) (lo : 2^d.val ≤ base)
    (leaves : Nat → Binding.Digest) (can : ∀ k, Canonical 24 (leaves k))
    (s : MachineState) (initial : Cursor d base 0 s)
    (heap : Snapshot (cell s) (node (rawC o) leaves) d base) (n : Nat)
    (unrolled : n ≤ Image.unroll d) (inTree : base+n ≤ 2^(d.val+1)) :
    ∃ t, Segment o CommitSetup.im (Image.start d n-Image.levelStart d) s t ∧ Cursor d base n t ∧
      Snapshot (cell t) (node (rawC o) leaves) d (base+n) ∧ Outside s t ∧
      t.getReg .x20=s.getReg .x20 ∧ (0<n → t.getReg .x12=BitVec.ofNat 64 (addr d (base+n-1))) := by
  induction n with
  | zero => exact ⟨s,by simpa [Image.start] using empty o CommitSetup.im s,initial,by simpa using heap,Outside.refl s,rfl,by omega⟩
  | succ n ih =>
    obtain ⟨v,sv,cur,past,frame,counter,last⟩ := ih (by omega) (by omega)
    have hf := Image.node_loaded d ⟨n,by omega⟩
    rw [←cur.pc] at hf
    obtain ⟨t,st,pc,done,write,sr,dr,dt,keep⟩ := actual_parent o CommitSetup.im v d n (base+n) (by omega)
      (by omega) leaves can past (ptr1 cur) (ptr2 cur) cur.regs hf
    have ord : Image.levelStart d ≤ Image.start d n := by unfold Image.start;omega
    have len : Image.start d (n+1)-Image.levelStart d =
        Image.start d n-Image.levelStart d+(Image.body d n).length := by rw [Image.next_start];omega
    have cx : Cursor d base (n+1) t := by
      refine ⟨?_,stable_regs cur.regs keep,(keep _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans cur.step,
        sr.trans (src_step cur),dr.trans (dst_step cur)⟩
      rw [pc,cur.pc,address_step,Image.next_start]
    refine ⟨t,len ▸ compose sv st,cx,?_,frame.trans (Outside.of_writes d.isLt (by omega) (by omega) write),
      (keep _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans counter,?_⟩
    · simpa [Nat.add_assoc] using done
    · intro _;simpa [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using dt

end CommitGolfCandidate.Reconstruction.CommitParents
