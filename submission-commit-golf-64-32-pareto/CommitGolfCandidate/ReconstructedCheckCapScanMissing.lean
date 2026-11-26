import CommitGolfCandidate.ReconstructedCheckCapScanFlags
import CommitGolfCandidate.ReconstructedCheckCapSlots

namespace CommitGolfCandidate.Reconstruction.CheckCapScanMissing
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CheckRecorded CommitBlocks CheckCapArith
abbrev W := BitVec.ofNat 64
set_option maxRecDepth 12000
set_option maxHeartbeats 1400000
attribute [local irreducible] execute ArtifactEncoding.decode

def code : List Line := [(.x17,.op (.add .x16 .x17)),(.x5,.op (.slli .x12 32)),
  (.x12,.addiw .x12 1),(.x5,.op (.srli .x5 30)),(.x5,.op (.add .x29 .x5))]

private theorem offset (j : Fin 257) : ((W j.val <<< (32:Nat)) >>> (30:Nat))=W (4*j.val) :=
  (by decide +kernel : ∀ j : Fin 257, ((W j.val <<< (32:Nat)) >>> (30:Nat))=W (4*j.val)) j

private theorem incr (p : Fin 257) :
    ((W p.val).truncate 32+(signExtend12 1).truncate 32).signExtend 64=W (p.val+1) :=
  (by decide +kernel : ∀ j : Fin 257, ((W j.val).truncate 32+(signExtend12 1).truncate 32).signExtend 64=W (j.val+1)) p

private theorem cut (v : Nat) : (W v).truncate 32=BitVec.ofNat 32 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [W,BitVec.truncate,BitVec.toNat_setWidth,BitVec.toNat_ofNat];omega

def result (s : MachineState) (base p k : Nat) (l r : Bool) :=
  if l=r then s.setPC (addr 442) else
    ((effect (s.setPC (addr 453)) code).setWord32 (CheckCapSlots.address base p)
      (BitVec.ofNat 32 (k+l.toNat))).setPC (addr 442)

theorem positive (o : Oracle) (s : MachineState) (base k : Nat) (p : Fin 257) (l r : Bool)
    (pc : s.pc=addr 452) (left : s.getReg .x17=W l.toNat) (right : s.getReg .x5=W r.toNat)
    (index : s.getReg .x16=W k) (count : s.getReg .x12=W p.val) (pointer : s.getReg .x29=W base)
    (align : base%8=0) (room : base+4*p.val+4≤MEMORY_BYTES) :
    Segment o (if l=r then 1 else 8) s (result s base p.val k l r) [] := by
  have branch:=CheckBranch.event o s 452 442 .eq .x17 .x5 8152 (by decide) pc rfl (by decide)
  change Segment o 1 s (s.setPC (if s.getReg .x17==s.getReg .x5 then addr 442 else addr 453)) [] at branch
  rw [left,right] at branch
  by_cases same : l=r
  · subst r
    simpa only [result,ite_true,beq_self_eq_true] using branch
  · have different : W l.toNat≠W r.toNat := by cases l <;> cases r <;> first | decide | contradiction
    rw [beq_eq_false_iff_ne.mpr different] at branch
    let u:=s.setPC (addr 453)
    let t:=effect u code
    have block:=CheckCapArith.positive o u 453 code rfl (by decide)
    have location : t.pc=addr 458:=CheckCapArith.location u 453 code rfl
    have position : t.getReg .x5=CheckCapSlots.address base p.val := by
      rw [show t.getReg .x5=regs u.getReg code .x5 from register ..]
      change s.getReg .x29+((s.getReg .x12 <<< (32:Nat)) >>> (30:Nat))=_
      rw [count,pointer,offset];exact (BitVec.ofNat_add ..).symm
    have value : (t.getReg .x17).truncate 32=BitVec.ofNat 32 (k+l.toNat) := by
      rw [show t.getReg .x17=regs u.getReg code .x17 from register ..]
      change (s.getReg .x16+s.getReg .x17).truncate 32=_
      rw [index,left,←BitVec.ofNat_add,cut]
    have store:=CheckMemoryOps.store32 o t 458 .x5 .x17 _ _ (by decide) location position value
      (CheckCapSlots.valid _ _ align room)
    have j:=CheckBranch.jump o ((t.setWord32 (CheckCapSlots.address base p.val) (BitVec.ofNat 32 (k+l.toNat))).setPC (addr 459)) 459 442 2097084 (by decide) rfl rfl (by decide)
    simp only [result,ite_eq_right same]
    exact compose (compose (compose branch block) store) j

theorem count (s : MachineState) (base k : Nat) (p : Fin 257) (l r : Bool) (old : s.getReg .x12=W p.val) :
    (result s base p.val k l r).getReg .x12=W (p.val+(l != r).toNat) := by
  by_cases eq : l=r
  · subst r;simpa only [result,ite_true,bne_self_eq_false,Bool.toNat_false,Nat.add_zero,MachineState.getReg_setPC] using old
  · rw [result,ite_eq_right eq]
    change (effect (s.setPC (addr 453)) code).getReg .x12=_
    rw [register];change ((s.getReg .x12).truncate 32+(signExtend12 1).truncate 32).signExtend 64=_
    rw [old,incr];cases l <;> cases r <;> first | rfl | contradiction

theorem memory (s : MachineState) (base p k : Nat) (l r : Bool) :
    (result s base p k l r).mem=(if l=r then s else s.setWord32 (CheckCapSlots.address base p) (BitVec.ofNat 32 (k+l.toNat))).mem := by
  unfold result;split
  · rfl
  · exact CapScanMemory.word_congr (CheckCapArith.memory ..) _ _

theorem keep (s : MachineState) (base p k : Nat) (l r : Bool) (q : Reg) (fresh : q∉[Reg.x17,.x5,.x12]) :
    (result s base p k l r).getReg q=s.getReg q := by
  unfold result;split
  · rfl
  · change (effect (s.setPC (addr 453)) code).getReg q=_
    apply outside
    simp_all [code]

end CommitGolfCandidate.Reconstruction.CheckCapScanMissing
