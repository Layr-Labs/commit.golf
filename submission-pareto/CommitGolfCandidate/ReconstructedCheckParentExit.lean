import CommitGolfCandidate.ReconstructedCheckParentControl

namespace CommitGolfCandidate.Reconstruction.CheckParentExit
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CheckRecorded CommitBlocks CheckCapArith CheckGroupRadix CheckGroupControl CheckParentControl
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000

def code : List Line := [(.x18,.op (.addi .x0 1)),(.x22,.op (.addi .x0 2))]

structure Ready (t : MachineState) (e : Nat) (cursor : Word) : Prop where
  pc : t.pc=addr (if e=0 then 632 else 425)
  depth : t.getReg .x9=W e
  one : t.getReg .x18=1
  two : t.getReg .x22=2
  static : Context t cursor

theorem run (o : Oracle) (s : MachineState) (e : Nat) (c : Word) (pc : s.pc=addr 629) (depth : s.getReg .x9=W e)
    (small : e≤8) (ctx : Context s c) :
    ∃ t,Segment o 3 s t [] ∧ Ready t e c ∧ t.mem=s.mem ∧ Kept [.x18,.x22] s t := by
  let u:=effect s code
  have stem:=CheckCapArith.positive o s 629 code pc (by decide)
  have keep (r : Reg) (h : r∉[Reg.x18,.x22]) : u.getReg r=s.getReg r:=outside s code r h
  have point:=CheckBranch.event o u 631 425 .ne .x9 .x0 7368 (by decide) (CheckCapArith.location s 629 code pc) rfl (by decide)
  change Segment o 1 u (u.setPC (if u.getReg .x9 != 0#64 then addr 425 else addr 632)) [] at point
  rw [keep .x9 (by decide),depth] at point
  have loc : (if W e != 0#64 then addr 425 else addr 632)=addr (if e=0 then 632 else 425) := by
    by_cases z : e=0
    · subst e;rfl
    · have ne : W e≠0#64:=by intro h;have n:=congrArg BitVec.toNat h;change e%2^64=0 at n;omega
      rw [ite_eq_right z];simp [ne]
  rw [loc] at point
  let t:=u.setPC (addr (if e=0 then 632 else 425))
  have unit : u.getReg .x18=1:=by rw [register s code];rfl
  have two : u.getReg .x22=2:=by rw [register s code];rfl
  exact ⟨t,compose stem point,⟨rfl,(keep _ (by decide)).trans depth,unit,two,
    ⟨(keep _ (by decide)).trans ctx.one,(keep _ (by decide)).trans ctx.sp,(keep _ (by decide)).trans ctx.fp,
     (keep _ (by decide)).trans ctx.heap,(keep _ (by decide)).trans ctx.bits,(keep _ (by decide)).trans ctx.scratch⟩⟩,
    memory s code,keep⟩
end CommitGolfCandidate.Reconstruction.CheckParentExit

