import CommitGolfCandidate.ReconstructedCommitParentsOuter
import CommitGolfCandidate.ReconstructedCommitParentsSetup

namespace CommitGolfCandidate.Reconstruction.CommitParents
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding CommitExact
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
attribute [local irreducible] readBuffer

def bodyLen (d : Nat) := Outer.tailPC d-Image.levelStart d
def visitSteps (d : Nat) (n : Nat) := n*(bodyLen d+5)-1
def groups (d : Nat) := 2^d / Image.unroll d
def depthSteps (d : Nat) := if 10≤d then visitSteps d (groups d) else bodyLen d
def depthEnd (d : Nat) := Outer.tailPC d+(if 10≤d then 5 else 0)

structure Done (o : Oracle) (leaves : Nat→Binding.Digest) (d : Fin 24) (s t : MachineState) : Prop where
  pc : t.pc=CommitBlocks.addr (depthEnd d)
  heap : Snapshot (cell t) (node (rawC o) leaves) d (2^(d.val+1))
  outside : Outside s t
  tags : t.getReg .x5=0 ∧ t.getReg .x11=64 ∧ t.getReg .x13=0
  output : t.getReg .x12=BitVec.ofNat 64 (addr d (2^(d.val+1)-1))

theorem snapshot_mem {s t : MachineState} {tree d k} (mem : t.mem=s.mem) (past : Snapshot (cell s) tree d k) :
    Snapshot (cell t) tree d k :=
  ⟨fun e j b=>(cell_congr mem _).trans (past.1 e j b),fun e b=>(cell_congr mem _).trans (past.2 e b)⟩

private theorem reps : ∀ d : Fin 24, (10≤d.val → Image.unroll d=512 ∧ groups d*512=2^d.val ∧ 0<groups d) ∧
    (d.val<10 → Image.unroll d=2^d.val ∧ 0<Image.unroll d) := by decide

private theorem moved {d : Fin 24} {s t : MachineState} {base n : Nat} (c : Cursor d base 512 s)
    (v : Outer.EndRegs s t n) (pc : t.pc=CommitBlocks.addr (Image.start d 0)) : Cursor d (base+512) 0 t := by
  have keep (r : Reg) (a : r≠.x18) (b : r≠.x19) (e : r≠.x20) := v.keep r a b e
  have mask : aux d t := ⟨fun x => (keep _ (by decide) (by decide) (by decide)).trans (c.regs.masks.1 x),
    fun x => (keep _ (by decide) (by decide) (by decide)).trans (c.regs.masks.2.1 x),
    fun x y => (keep _ (by decide) (by decide) (by decide)).trans (c.regs.masks.2.2 x y)⟩
  refine ⟨pc,⟨⟨(keep _ (by decide) (by decide) (by decide)).trans c.regs.hash.1,
    (keep _ (by decide) (by decide) (by decide)).trans c.regs.hash.2.1,
    (keep _ (by decide) (by decide) (by decide)).trans c.regs.hash.2.2⟩,mask,
    fun x => (keep _ (by decide) (by decide) (by decide)).trans (c.regs.label x)⟩,
    (keep _ (by decide) (by decide) (by decide)).trans c.step,?_,?_⟩
  · rw [v.src,c.src,c.step,←show BitVec.ofNat 64 4096=4096 by rfl,←BitVec.ofNat_add]
    congr 1;unfold srcCentre addr;omega
  · rw [v.dst,c.dst,c.step,←show BitVec.ofNat 64 4096=4096 by rfl,←BitVec.ofNat_add]
    congr 1;unfold dstCentre addr;omega

theorem counted_level (o : Oracle) (d : Fin 24) (large : 10≤d.val)
    (leaves : Nat→Binding.Digest) (can : ∀ k, Canonical 24 (leaves k))
    (n base : Nat) (s : MachineState) (cursor : Cursor d base 0 s) (lo : 2^d.val≤base)
    (full : base+(n+1)*512=2^(d.val+1))
    (counter : s.getReg .x20 = BitVec.ofNat 64 (n+1))
    (heap : Snapshot (cell s) (node (rawC o) leaves) d base) :
    ∃ t, Segment o CommitSetup.im (visitSteps d (n+1)) s t ∧ Done o leaves d s t := by
  induction n generalizing base s
  all_goals
    have unrolled := ((reps d).1 large).1
    have bound : 2^(d.val+1) ≤ 2^24 := Nat.pow_le_pow_right (by decide) (by have := d.isLt;omega)
    obtain ⟨v,g,cur,arr,ext,cnt,last⟩ := group_prefix o d base lo leaves can s cursor heap 512 (by omega) (by omega)
    have endPC : v.pc=CommitBlocks.addr (Outer.tailPC d) := by rw [Outer.tailPC,unrolled];exact cur.pc
  case zero =>
      obtain ⟨u,tail,pc,mem,reg⟩ := Outer.suffix o d large v endPC 0 (by decide) (cnt.trans counter)
      refine ⟨u,?_,⟨?_,?_,ext.trans (Outside.of_mem mem),?_,?_⟩⟩
      · have eq : visitSteps d 1=(Image.start d 512-Image.levelStart d)+4 := by
          simp [visitSteps,bodyLen,Outer.tailPC,unrolled]
        rw [eq];exact compose g tail
      · simpa [depthEnd,large] using pc
      · apply snapshot_mem mem
        convert arr using 1 <;> omega
      · exact ⟨(reg.keep _ (by decide) (by decide) (by decide)).trans cur.regs.hash.1,
          (reg.keep _ (by decide) (by decide) (by decide)).trans cur.regs.hash.2.1,
          (reg.keep _ (by decide) (by decide) (by decide)).trans cur.regs.hash.2.2⟩
      · rw [reg.keep _ (by decide) (by decide) (by decide),last (by decide)]
        congr 2;omega
  case succ n ih =>
      obtain ⟨u,tail,pc,mem,reg⟩ := Outer.suffix o d large v endPC (n+1) (by omega) (cnt.trans counter)
      have cp : u.pc=CommitBlocks.addr (Image.start d 0) := by simpa using pc
      obtain ⟨t,rem,done⟩ := ih (base+512) u (moved cur reg cp) (by omega) (by omega) reg.count (snapshot_mem mem arr)
      refine ⟨t,?_,{ done with outside := (ext.trans (Outside.of_mem mem)).trans done.outside }⟩
      have eq : visitSteps d (n+1+1)=(Image.start d 512-Image.levelStart d)+5+visitSteps d (n+1) := by
        unfold visitSteps;rw [Nat.succ_mul];unfold bodyLen Outer.tailPC;rw [unrolled]
        have pos : 0<(n+1)*(Image.start d 512-Image.levelStart d+5) := Nat.mul_pos (by omega) (by omega)
        omega
      rw [eq]
      exact compose (compose g tail) rem

theorem depth (o : Oracle) (d : Fin 24) (leaves : Nat→Binding.Digest)
    (can : ∀ k, Canonical 24 (leaves k)) (s : MachineState) (pc : s.pc=CommitBlocks.addr (Setup.begin d))
    (kind : s.getReg .x5=0) (regular : d.val<23 → s.getReg .x11=64 ∧ s.getReg .x13=0)
    (initial : Snapshot (cell s) (node (rawC o) leaves) d (2^d.val)) :
    ∃ t, Segment o CommitSetup.im ((Setup.ops d).length+depthSteps d) s t ∧ Done o leaves d s t := by
  let v := Setup.after s (Setup.ops d)
  obtain ⟨setup,mem,cur,cnt⟩ := Setup.start_level o s d pc kind regular
  change Segment o CommitSetup.im _ s v at setup
  have mem' : v.mem=s.mem := mem
  have init := snapshot_mem mem' initial
  by_cases big : 10≤d.val
  · obtain ⟨ulen,div,pos⟩ := (reps d).1 big
    let n := groups d-1
    have eq : groups d=n+1 := by dsimp [n];omega
    have num : v.getReg .x20=BitVec.ofNat 64 (n+1) := by rw [←eq];exact cnt
    obtain ⟨t,sg,done⟩ := counted_level o d big leaves can n (2^d.val) v cur le_rfl
      (by rw [←eq,div,Nat.pow_succ];omega) num init
    refine ⟨t,?_,{done with outside := (Outside.of_mem mem').trans done.outside}⟩
    rw [depthSteps,ite_eq_left big,eq];exact compose setup sg
  · obtain ⟨len,pos⟩ := (reps d).2 (by omega)
    have sz : 2^d.val+Image.unroll d=2^(d.val+1) := by rw [len,Nat.pow_succ];omega
    obtain ⟨t,sg,c,ready,ext,_,last⟩ := group_prefix o d (2^d.val) le_rfl leaves can v cur init (Image.unroll d) le_rfl sz.le
    refine ⟨t,?_,⟨?_,sz ▸ ready,(Outside.of_mem mem').trans ext,c.regs.hash,?_⟩⟩
    · rw [depthSteps,ite_eq_right big];exact compose setup sg
    · simpa [depthEnd,big,Outer.tailPC] using c.pc
    · rw [←sz];exact last pos

end CommitGolfCandidate.Reconstruction.CommitParents
