import CommitGolfCandidate.S5SiteRun
import CommitGolfCandidate.S5MemoryStep

namespace CommitGolfCandidate.S5Machine
open CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

def finalLeafState (h : Compression) (s : MachineState) (tile : Nat) (i : Fin 256) :=
  let u := siteResult h tile s i 0
  let a := siteResult h tile u i 1
  let b := siteResult h tile a i 2
  siteResult h tile b i 3

private theorem site_mem (h : Compression) {s : MachineState} {tile : Nat} {i : Fin 256}
    (regs : LeafRegs s tile i) (j : Fin 4) (t : MachineState) (same : s.mem = t.mem) :
    (siteResult h tile s i j).mem =
      (compressAt h t (leafSource (256*tile+i.val) j) (leafTarget (256*tile+i.val) j)).mem := by
  unfold siteResult
  erw [reply_memory regs j (h (readBuffer s (leafSource (256*tile+i.val) j) 96)),
    read_congr_mem s t (leafSource (256*tile+i.val) j) 96 same]
  exact write_bits_memory_congr s t _ _ same

private theorem next_pc (h : Compression) (s : MachineState) (tile : Nat) (i : Fin 256) (j j' : Fin 4)
    (next : j'.val = j.val+1) (pc : s.pc = pcAt (leafPC i j)) :
    (siteResult h tile s i j).pc = pcAt (leafPC i j') := by
  rw [show (siteResult h tile s i j).pc = s.pc+12 from call_pc _ _ _ _ _ _, pc]
  change BitVec.ofNat 64 _ + BitVec.ofNat 64 12 = BitVec.ofNat 64 _
  rw [← BitVec.ofNat_add]
  apply congrArg (BitVec.ofNat 64)
  unfold leafPC tileSite
  omega

theorem leaf_state_memory (h : Compression) (s : MachineState) (tile : Nat) (i : Fin 256)
    (regs : LeafRegs s tile i) :
    (finalLeafState h s tile i).mem = (writeLeaf h s (256*tile+i.val)).mem := by
  let u := siteResult h tile s i 0
  let a := siteResult h tile u i 1
  let b := siteResult h tile a i 2
  have ru : LeafRegs u tile i := reply_regs regs 0 _
  have ra : LeafRegs a tile i := reply_regs ru 1 _
  have rb : LeafRegs b tile i := reply_regs ra 2 _
  have hu := site_mem h regs 0 s rfl
  have ha := site_mem h ru 1 _ hu
  have hb := site_mem h ra 2 _ ha
  exact site_mem h rb 3 _ hb

theorem fixed_leaf (o : Oracle) (s : MachineState) (tile : Nat) (i : Fin 256) (regs : LeafRegs s tile i)
    (pc : s.pc = pcAt (leafPC i 0)) (inside : 256*tile+i.val < LENGTH) (fuel : Nat) :
    o.run (execute commitImage (fuel+12) s true) =
      (do let (out,n) ← o.run (execute commitImage fuel (finalLeafState o.compression s tile i) true)
          return (out.charge 40 4,4+n)) := by
  let u := siteResult o.compression tile s i 0
  let a := siteResult o.compression tile u i 1
  let b := siteResult o.compression tile a i 2
  have ru : LeafRegs u tile i := reply_regs regs 0 _
  have ra : LeafRegs a tile i := reply_regs ru 1 _
  have rb : LeafRegs b tile i := reply_regs ra 2 _
  have pc₁ : u.pc = pcAt (leafPC i 1) := next_pc _ _ _ _ 0 1 rfl pc
  have pc₂ : a.pc = pcAt (leafPC i 2) := next_pc _ _ _ _ 1 2 rfl pc₁
  have pc₃ : b.pc = pcAt (leafPC i 3) := next_pc _ _ _ _ 2 3 rfl pc₂
  rw [fixed_site o regs 0 pc inside (fuel+9), fixed_site o ru 1 pc₁ inside (fuel+6),
      fixed_site o ra 2 pc₂ inside (fuel+3), fixed_site o rb 3 pc₃ inside fuel]
  simp only [bind_assoc, pure_bind, Execution.charge, ← Nat.add_assoc]
  rfl

end CommitGolfCandidate.S5Machine
