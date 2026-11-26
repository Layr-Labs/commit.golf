import CommitGolfCandidate.ReconstructedCheckCapArithInputs
import CommitGolfCandidate.ReconstructedCheckCapScanData

namespace CommitGolfCandidate.Reconstruction.CheckCapScanStart
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CheckRecorded CommitBlocks CheckCapArith
open CheckCapScanData (W flag active)
set_option maxRecDepth 15000
set_option maxHeartbeats 1500000

def shifts : List Line := [(.x25,.sllw .x18 .x9),(.x20,.sllw .x22 .x9)]
def setup : List Line := [(.x12,.op (.addi .x0 0)),(.x10,.op (.addi .x25 1)),(.x10,.op (.slli .x10 32)),
  (.x10,.op (.srli .x10 32)),(.x14,.op (.lui 1040)),(.x13,.op (.add .x10 .x14)),(.x11,.op (.slli .x25 32)),
  (.x11,.op (.srli .x11 32)),(.x10,.srliw .x25 1),(.x19,.op (.add .x10 .x14)),(.x14,.op (.add .x11 .x14)),
  (.x15,.op (.addi .x19 0)),(.x16,.op (.addi .x25 0))]
def effect1 (s : MachineState) := effect s shifts
def effect2 (s : MachineState) := effect ((effect1 s).setPC (addr 428)) setup
def result (s : MachineState) := (effect2 s).setPC (addr 447)

def lhs (d : Nat) : Reg→Word := fun r=>match r with
  | .x18=>1 | .x22=>2 | .x9=>W d | _=>0
def mid (d : Nat) : Reg→Word := fun r=>if r=.x25 then W (2^d) else 0
def checks (d : Nat) : Prop :=
  regs (lhs d) shifts .x25=W (2^d) ∧ regs (lhs d) shifts .x20=W (2^(d+1)) ∧
  regs (mid d) setup .x12=0 ∧ regs (mid d) setup .x10=W (2^(d-1)) ∧ regs (mid d) setup .x11=W (2^d) ∧
  regs (mid d) setup .x19=flag (2^(d-1)) ∧ regs (mid d) setup .x13=flag (2^d+1) ∧
  regs (mid d) setup .x14=flag (2^d) ∧ regs (mid d) setup .x15=flag (2^(d-1)) ∧ regs (mid d) setup .x16=W (2^d)
deriving instance Decidable for checks

private theorem finite (d : Fin 9) : checks (d.val+1) :=
  (by decide +kernel : ∀ i : Fin 9, checks (i.val+1)) d

structure Registers (s : MachineState) (d : Nat) : Prop where
  index : s.getReg .x16=W (2^d)
  count : s.getReg .x12=0
  beginIdx : s.getReg .x25=W (2^d)
  endIdx : s.getReg .x20=W (2^(d+1))
  lo : s.getReg .x14=flag (2^d)
  hi : s.getReg .x13=flag (2^d+1)
  parent : s.getReg .x15=flag (2^(d-1))
  firstParent : s.getReg .x19=flag (2^(d-1))
  firstId : s.getReg .x11=W (2^d)
  parentId : s.getReg .x10=W (2^(d-1))

private theorem checked (d : Nat) (pos : 0<d) (max : d≤9) : checks d := by
  let i : Fin 9:=⟨d-1,by omega⟩
  have hd : i.val+1=d:=by dsimp [i];omega
  exact hd ▸ finite i

private theorem shifted (s : MachineState) (d : Nat) (ok : checks d)
    (unit : s.getReg .x18=1) (two : s.getReg .x22=2) (depth : s.getReg .x9=W d) :
    (effect1 s).getReg .x25=W (2^d) ∧ (effect1 s).getReg .x20=W (2^(d+1)) := by
  constructor
  · rw [effect1,register]
    change (wordResult .sll ((s.getReg .x18).truncate 32) ((s.getReg .x9).truncate 32)).signExtend 64=_
    rw [unit,depth];exact ok.1
  · rw [effect1,register]
    change (wordResult .sll ((s.getReg .x22).truncate 32) ((s.getReg .x9).truncate 32)).signExtend 64=_
    rw [two,depth];exact ok.2.1

private theorem registers (u : MachineState) (d : Nat) (ok : checks d)
    (lo : u.getReg .x25=W (2^d)) (hi : u.getReg .x20=W (2^(d+1))) :
    Registers (effect u setup) d := by
  obtain ⟨_,_,c0,pId,lId,pBase,hiBase,loBase,pPtr,index⟩:=ok
  have initial : CheckCapArithInputs.Agrees u.getReg (mid d) [.x0,.x25] := by
    intro q h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl; rfl;exact lo
  have final:=CheckCapArithInputs.agree u.getReg (mid d) setup [.x0,.x25] initial (by decide)
  have equivalence (r : Reg) (member : r∈CheckCapArithInputs.finish [.x0,.x25] setup) :
      (effect u setup).getReg r=regs (mid d) setup r := (register u setup r).trans (final r member)
  exact ⟨(equivalence .x16 (by decide)).trans index,(equivalence .x12 (by decide)).trans c0,
    (outside u setup .x25 (by decide)).trans lo,(outside u setup .x20 (by decide)).trans hi,
    (equivalence .x14 (by decide)).trans loBase,(equivalence .x13 (by decide)).trans hiBase,
    (equivalence .x15 (by decide)).trans pPtr,(equivalence .x19 (by decide)).trans pBase,
    (equivalence .x11 (by decide)).trans lId,(equivalence .x10 (by decide)).trans pId⟩

private theorem less (d : Nat) (max : d≤9) : (W (2^d)).ult (W (2^(d+1)))=true :=
  (by decide : ∀ i : Fin 10,(W (2^i.val)).ult (W (2^(i.val+1)))=true) ⟨d,by omega⟩

private theorem traverse (o : Oracle) (s : MachineState) (d : Nat) (bound : d≤9) (pc : s.pc=addr 425)
    (lo : (effect1 s).getReg .x25=W (2^d)) (hi : (effect1 s).getReg .x20=W (2^(d+1))) :
    Segment o 17 s (result s) [] := by
  let u:=(effect1 s).setPC (addr 428)
  have sh : Segment o 2 s (effect1 s) []:=CheckCapArith.positive o s 425 shifts pc (by decide)
  have cmp:=CheckBranch.event o (effect1 s) 427 423 .ge .x25 .x20 8176 (by decide) (location s 425 shifts pc) rfl (by decide)
  change Segment o 1 (effect1 s) ((effect1 s).setPC (if !((effect1 s).getReg .x25 |>.ult ((effect1 s).getReg .x20)) then addr 423 else addr 428)) [] at cmp
  rw [lo,hi,less d bound] at cmp
  change Segment o 1 (effect1 s) u [] at cmp
  have block : Segment o 13 u (effect u setup) []:=CheckCapArith.positive o u 428 setup rfl (by decide)
  have whereAt : (effect u setup).pc=addr 441:=location u 428 setup rfl
  have j:=CheckBranch.jump o (effect u setup) 441 447 24 (by decide) whereAt rfl (by decide)
  exact compose (compose (compose sh cmp) block) j

private theorem move {s : MachineState} {d : Nat} (v : Word) (h : Registers s d) : Registers (s.setPC v) d :=
  ⟨h.index,h.count,h.beginIdx,h.endIdx,h.lo,h.hi,h.parent,h.firstParent,h.firstId,h.parentId⟩

attribute [local irreducible] CheckCapArith.effect

theorem positive (o : Oracle) (s : MachineState) (d : Nat) (pos : 0<d) (max : d≤9) (pc : s.pc=addr 425)
    (unit : s.getReg .x18=1) (two : s.getReg .x22=2) (depth : s.getReg .x9=W d) :
    Segment o 17 s (result s) [] ∧ (result s).pc=addr 447 ∧ (result s).mem=s.mem ∧ Registers (result s) d ∧
    ∀ r∉(shifts.map Prod.fst++setup.map Prod.fst),(result s).getReg r=s.getReg r := by
  have ok:=checked d pos max
  obtain ⟨lo,hi⟩:=shifted s d ok unit two depth
  let u:=(effect1 s).setPC (addr 428)
  have loU : u.getReg .x25=W (2^d):=(MachineState.getReg_setPC ..).trans lo
  have hiU : u.getReg .x20=W (2^(d+1)):=(MachineState.getReg_setPC ..).trans hi
  have next:=registers u d ok loU hiU
  have kept (r : Reg) (fresh : r∉(shifts.map Prod.fst++setup.map Prod.fst)) : (result s).getReg r=s.getReg r := by
    simp only [List.mem_append,not_or] at fresh
    change ((effect u setup).setPC (addr 447)).getReg r=_
    rw [MachineState.getReg_setPC, outside u setup r fresh.2]
    change ((effect s shifts).setPC (addr 428)).getReg r=_
    rw [MachineState.getReg_setPC];exact outside s shifts r fresh.1
  have finalmem : (result s).mem=s.mem := by
    change (effect u setup).mem=s.mem
    have firstMem : u.mem=s.mem:=memory s shifts
    exact (memory u setup).trans firstMem
  have ending : Registers (result s) d:=by
    change Registers ((effect u setup).setPC (addr 447)) d
    exact move (addr 447) next
  exact ⟨traverse o s d max pc lo hi,rfl,finalmem,ending,kept⟩

end CommitGolfCandidate.Reconstruction.CheckCapScanStart
