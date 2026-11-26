import CommitGolfCandidate.ReconstructedCheckCapArith

namespace CommitGolfCandidate.Reconstruction.CheckCapScanAdvance
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CheckRecorded CommitBlocks CheckCapArith
abbrev W := BitVec.ofNat 64
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000

def code : List Line := [(.x16,.addiw .x16 2),(.x13,.op (.addi .x13 2)),
  (.x14,.op (.addi .x14 2)),(.x15,.op (.addi .x15 1))]
def dest (k hi : Nat) := if k+2<hi then 447 else 460
def result (s : MachineState) (k hi : Nat) := (effect s code).setPC (addr (dest k hi))

private theorem increment (k : Fin 1024) :
    ((W k.val).truncate 32+(signExtend12 2).truncate 32).signExtend 64=W (k.val+2) :=
  (by decide +kernel : ∀ i : Fin 1024, ((W i.val).truncate 32+(signExtend12 2).truncate 32).signExtend 64=W (i.val+2)) k

theorem after (s : MachineState) (k : Fin 1024) (index : s.getReg .x16=W k.val) :
    (effect s code).getReg .x16=W (k.val+2) := by
  rw [register];change ((s.getReg .x16).truncate 32+(signExtend12 2).truncate 32).signExtend 64=_
  rw [index,increment]

theorem positive (o : Oracle) (s : MachineState) (k : Fin 1024) (hi : Nat) (small : hi<2^64)
    (pc : s.pc=addr 442) (index : s.getReg .x16=W k.val) (last : s.getReg .x20=W hi) :
    Segment o 5 s (result s k.val hi) [] := by
  let u:=effect s code
  have block:=CheckCapArith.positive o s 442 code pc (by decide)
  have pos : u.pc=addr 446:=CheckCapArith.location s 442 code pc
  have cmp:=CheckBranch.event o u 446 460 .ge .x16 .x20 56 (by decide) pos rfl (by decide)
  have last' : u.getReg .x20=W hi := (outside s code .x20 (by decide)).trans last
  have ok := after s k index
  have test : (W (k.val+2)).ult (W hi)=decide (k.val+2<hi) := by
    simp only [BitVec.ult,W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small,Nat.mod_eq_of_lt (by have:=k.isLt;omega : k.val+2<2^64)]
  change Segment o 1 u (u.setPC (if !(u.getReg .x16 |>.ult (u.getReg .x20)) then addr 460 else addr 447)) [] at cmp
  rw [ok,last',test] at cmp
  by_cases done : k.val+2<hi
  · rw [decide_eq_true done] at cmp
    rw [result,dest,ite_eq_left done]
    exact compose block cmp
  · rw [decide_eq_false done] at cmp
    rw [result,dest,ite_eq_right done]
    exact compose block cmp

theorem state (s : MachineState) (k : Fin 1024) (hi : Nat) (index : s.getReg .x16=W k.val) :
    let t:=result s k.val hi
    t.pc=addr (dest k.val hi) ∧ t.mem=s.mem ∧ t.getReg .x16=W (k.val+2) ∧
    t.getReg .x13=s.getReg .x13+2 ∧ t.getReg .x14=s.getReg .x14+2 ∧ t.getReg .x15=s.getReg .x15+1 ∧
    ∀ q∉[Reg.x16,.x13,.x14,.x15], t.getReg q=s.getReg q := by
  exact ⟨rfl,memory s code,after s k index,register s code .x13,register s code .x14,register s code .x15,fun q h=>outside s code q h⟩

end CommitGolfCandidate.Reconstruction.CheckCapScanAdvance
