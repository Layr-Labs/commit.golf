import CommitGolfCandidate.Layout2CapSpan
import CommitGolfCandidate.Layout2Superblock

namespace CommitGolfCandidate.Layout2.Cap
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open CommitGolfCandidate.Layout2.Quartet (checkImage)
set_option maxRecDepth 10000
set_option maxHeartbeats 1500000
structure Cursor (s t : MachineState) (base n g : Nat) : Prop where
  start : t.pc=pc 1010
  dst : t.getReg .x8=addr (base+952*g)
  rem : t.getReg .x9=addr (n-952*g)
  size : t.getReg .x20=addr 952
  eight : t.getReg .x21=8
  output : Output s t base (952*g) (result s base n)
  kept : Kept temps s t

theorem ult (a b : Nat) (ha : a<2^64) (hb : b<2^64) :
    BitVec.ult (addr a) (addr b)=decide (a<b) := by
  simp only [BitVec.ult,BitVec.toNat_ofNat,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb]

theorem full_loop {s u base n} (cur : Cursor s u base n 0)
    (data : AtData s) (scratch : s.getReg .x10=addr scratchBase) (sp : s.getReg .x2=addr tableBase)
    (sep : scratchBase+2136≤base) (room : base+n≤tableBase) :
    ∃ t, Runs checkImage u t (100926*(n/952)) (100926*(n/952)) ∧ Cursor s t base n (n/952) := by
  apply loop (n/952) 100926 100926 (fun j t=>Cursor s t base n j) u cur
  intro j more v c
  have enough : 952*j+952≤n := by omega
  have lim : n<2^64 := by unfold tableBase at room;omega
  obtain ⟨a,ra,pa,ma,regA,ka⟩:=ctl_choose v c.start
  have atA : a.pc=pc 1011 := by
    rw [c.rem,c.size,ult _ _ (by omega) (by decide)] at pa
    simpa [show ¬n-952*j<952 by omega] using pa
  obtain ⟨b,rb,pb,mb,regB,kb⟩:=ctl_full a atA
  have stable:=c.kept.trans (ka.trans kb)
  have baseB : b.getReg .x8=addr (base+952*j) := by simp [regB,regA,c.dst]
  have sizeB : b.getReg .x18=addr (size 32) := by rw [regB];rfl
  have tableB : b.getReg .x19=addr (tableBase+offset 32) := by
    rw [regB,if_neg (by decide),if_pos rfl,regA,c.kept _ (by decide),sp];decide
  obtain ⟨d,rd,pd,od,kd⟩:=block_run (m:=32) (ret:=1016) data (by decide) (by decide) (by simp [more]) sep room enough
    (c.output.mem (mb.trans ma)) pb baseB sizeB tableB ((stable _ (by decide)).trans scratch)
    (by simp [regB,regA,c.eight]) (by rw [regB,if_pos rfl];decide)
  obtain ⟨z,rz,pz,mz,regZ,kz⟩:=ctl_advance d pd
  refine ⟨z,((ra.thenDo rb).thenDo rd).thenDo rz,pz,?_,?_,?_,?_,?_,stable.trans ((kd.weaken call_temps).trans kz)⟩
  · rw [regZ,if_neg (by decide),if_pos rfl,kd _ (by decide),baseB,show 952#64=addr 952 from rfl,addr_add]
    congr 1 <;> omega
  · rw [regZ,if_pos rfl,kd _ (by decide),regB];simp only [reduceCtorEq,ite_false,regA,c.rem]
    rw [show n-952*j=(n-952*(j+1))+952 by omega,←addr_add]
    change (addr (n-952*(j+1))+952#64)+18446744073709550664#64=_
    simp [BitVec.add_assoc]
  · simp [regZ,kd _ (by decide : Reg.x20∉callScratch),regB,regA,c.size]
  · simp [regZ,kd _ (by decide : Reg.x21∉callScratch),regB,regA,c.eight]
  · simpa only [Nat.mul_succ,show size 32=952 from rfl] using od.mem mz
end CommitGolfCandidate.Layout2.Cap
