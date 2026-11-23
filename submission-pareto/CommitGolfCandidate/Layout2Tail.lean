import CommitGolfCandidate.Layout2Superblock
namespace CommitGolfCandidate.Layout2
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxHeartbeats 1500000
def tailScratch : List Reg := [.x5,.x18,.x19,.x31]
def dispatchCost (r : Nat) := if r=1 then 8 else 11

structure TailEntry (r : Nat) (s u : MachineState) : Prop where
  pcAt : u.pc=pc 759
  size : u.getReg .x18=addr (534*r)
  table : u.getReg .x19=addr (tableBase+tableOffset r)
  link : u.getReg .x31=pc 739
  same : u.mem=s.mem
  kept : Kept tailScratch s u

private theorem dispatch_1 {I} (program : Program I) (s : MachineState) (here : s.pc=pc 721)
    (rem : s.getReg .x9=addr 1) (stack : s.getReg .x2=addr tableBase) :
    ∃ u, Runs I s u (dispatchCost 1) (dispatchCost 1) ∧ TailEntry 1 s u := by
  let s1:=after .tail s
  have b1:=move program .tail s here trivial
  have p1 : s1.pc=pc 722 := by rw [b1.pos];simp [pcOut,rem,addr]
  have r1 : s1.getReg .x9=addr 1 := (b1.kept _ (by decide)).trans rem
  let s2:=after .one s1
  have b2:=move program .one s1 p1 trivial
  have p2 : s2.pc=pc 734 := by rw [b2.pos];simp [pcOut,r1,addr]
  have r2 : s2.getReg .x9=addr 1 := (b2.kept _ (by decide)).trans r1
  let s3:=after .single s2
  have b3:=move program .single s2 p2 trivial
  have p3 : s3.pc=pc 737 := by rw [b3.pos];simp [pcOut,r2,addr]
  have r3 : s3.getReg .x9=addr 1 := (b3.kept _ (by decide)).trans r2
  let s4:=after .callTail s3
  have b4:=move program .callTail s3 p3 trivial
  have p4 : s4.pc=pc 759 := by rw [b4.pos];simp [pcOut,r3,addr]
  have r4 : s4.getReg .x9=addr 1 := (b4.kept _ (by decide)).trans r3
  have kept : Kept tailScratch s s4 := ((((b1.kept.weaken (b:=tailScratch) (by intro q h;cases q <;> simp_all [clobbers,tailScratch]))).trans (b2.kept.weaken (b:=tailScratch) (by intro q h;cases q <;> simp_all [clobbers,tailScratch]))).trans (b3.kept.weaken (b:=tailScratch) (by intro q h;cases q <;> simp_all [clobbers,tailScratch]))).trans (b4.kept.weaken (b:=tailScratch) (by intro q h;cases q <;> simp_all [clobbers,tailScratch]))
  refine ⟨s4,(((b1.run).thenDo b2.run).thenDo b3.run).thenDo b4.run,p4,?_,?_,?_,b4.mem.trans (b3.mem.trans (b2.mem.trans (b1.mem))),kept⟩
  · rw [b4.regs];simp only [regOut,reduceCtorEq,ite_false];rw [b3.regs];rfl
  · rw [b4.regs];simp only [regOut,reduceCtorEq,ite_false,ite_true];rw [b3.regs .x5]
    rw [b3.kept .x2 (by decide)]
    rw [b2.kept .x2 (by decide)]
    rw [b1.kept .x2 (by decide)]
    rw [stack];rfl
  · rw [b4.regs];rfl

private theorem dispatch_2 {I} (program : Program I) (s : MachineState) (here : s.pc=pc 721)
    (rem : s.getReg .x9=addr 2) (stack : s.getReg .x2=addr tableBase) :
    ∃ u, Runs I s u (dispatchCost 2) (dispatchCost 2) ∧ TailEntry 2 s u := by
  let s1:=after .tail s
  have b1:=move program .tail s here trivial
  have p1 : s1.pc=pc 722 := by rw [b1.pos];simp [pcOut,rem,addr]
  have r1 : s1.getReg .x9=addr 2 := (b1.kept _ (by decide)).trans rem
  let s2:=after .one s1
  have b2:=move program .one s1 p1 trivial
  have p2 : s2.pc=pc 724 := by rw [b2.pos];simp [pcOut,r1,addr]
  have r2 : s2.getReg .x9=addr 2 := (b2.kept _ (by decide)).trans r1
  let s3:=after .two s2
  have b3:=move program .two s2 p2 trivial
  have p3 : s3.pc=pc 730 := by rw [b3.pos];simp [pcOut,r2,addr]
  have r3 : s3.getReg .x9=addr 2 := (b3.kept _ (by decide)).trans r2
  let s4:=after .pair s3
  have b4:=move program .pair s3 p3 trivial
  have p4 : s4.pc=pc 737 := by rw [b4.pos];simp [pcOut,r3,addr]
  have r4 : s4.getReg .x9=addr 2 := (b4.kept _ (by decide)).trans r3
  let s5:=after .callTail s4
  have b5:=move program .callTail s4 p4 trivial
  have p5 : s5.pc=pc 759 := by rw [b5.pos];simp [pcOut,r4,addr]
  have r5 : s5.getReg .x9=addr 2 := (b5.kept _ (by decide)).trans r4
  have kept : Kept tailScratch s s5 := (((((b1.kept.weaken (b:=tailScratch) (by intro q h;cases q <;> simp_all [clobbers,tailScratch]))).trans (b2.kept.weaken (b:=tailScratch) (by intro q h;cases q <;> simp_all [clobbers,tailScratch]))).trans (b3.kept.weaken (b:=tailScratch) (by intro q h;cases q <;> simp_all [clobbers,tailScratch]))).trans (b4.kept.weaken (b:=tailScratch) (by intro q h;cases q <;> simp_all [clobbers,tailScratch]))).trans (b5.kept.weaken (b:=tailScratch) (by intro q h;cases q <;> simp_all [clobbers,tailScratch]))
  refine ⟨s5,((((b1.run).thenDo b2.run).thenDo b3.run).thenDo b4.run).thenDo b5.run,p5,?_,?_,?_,b5.mem.trans (b4.mem.trans (b3.mem.trans (b2.mem.trans (b1.mem)))),kept⟩
  · rw [b5.regs];simp only [regOut,reduceCtorEq,ite_false];rw [b4.regs];rfl
  · rw [b5.regs];simp only [regOut,reduceCtorEq,ite_false,ite_true];rw [b4.regs .x5]
    rw [b4.kept .x2 (by decide)]
    rw [b3.kept .x2 (by decide)]
    rw [b2.kept .x2 (by decide)]
    rw [b1.kept .x2 (by decide)]
    rw [stack];rfl
  · rw [b5.regs];rfl

private theorem dispatch_3 {I} (program : Program I) (s : MachineState) (here : s.pc=pc 721)
    (rem : s.getReg .x9=addr 3) (stack : s.getReg .x2=addr tableBase) :
    ∃ u, Runs I s u (dispatchCost 3) (dispatchCost 3) ∧ TailEntry 3 s u := by
  let s1:=after .tail s
  have b1:=move program .tail s here trivial
  have p1 : s1.pc=pc 722 := by rw [b1.pos];simp [pcOut,rem,addr]
  have r1 : s1.getReg .x9=addr 3 := (b1.kept _ (by decide)).trans rem
  let s2:=after .one s1
  have b2:=move program .one s1 p1 trivial
  have p2 : s2.pc=pc 724 := by rw [b2.pos];simp [pcOut,r1,addr]
  have r2 : s2.getReg .x9=addr 3 := (b2.kept _ (by decide)).trans r1
  let s3:=after .two s2
  have b3:=move program .two s2 p2 trivial
  have p3 : s3.pc=pc 726 := by rw [b3.pos];simp [pcOut,r2,addr]
  have r3 : s3.getReg .x9=addr 3 := (b3.kept _ (by decide)).trans r2
  let s4:=after .three s3
  have b4:=move program .three s3 p3 trivial
  have p4 : s4.pc=pc 737 := by rw [b4.pos];simp [pcOut,r3,addr]
  have r4 : s4.getReg .x9=addr 3 := (b4.kept _ (by decide)).trans r3
  let s5:=after .callTail s4
  have b5:=move program .callTail s4 p4 trivial
  have p5 : s5.pc=pc 759 := by rw [b5.pos];simp [pcOut,r4,addr]
  have r5 : s5.getReg .x9=addr 3 := (b5.kept _ (by decide)).trans r4
  have kept : Kept tailScratch s s5 := (((((b1.kept.weaken (b:=tailScratch) (by intro q h;cases q <;> simp_all [clobbers,tailScratch]))).trans (b2.kept.weaken (b:=tailScratch) (by intro q h;cases q <;> simp_all [clobbers,tailScratch]))).trans (b3.kept.weaken (b:=tailScratch) (by intro q h;cases q <;> simp_all [clobbers,tailScratch]))).trans (b4.kept.weaken (b:=tailScratch) (by intro q h;cases q <;> simp_all [clobbers,tailScratch]))).trans (b5.kept.weaken (b:=tailScratch) (by intro q h;cases q <;> simp_all [clobbers,tailScratch]))
  refine ⟨s5,((((b1.run).thenDo b2.run).thenDo b3.run).thenDo b4.run).thenDo b5.run,p5,?_,?_,?_,b5.mem.trans (b4.mem.trans (b3.mem.trans (b2.mem.trans (b1.mem)))),kept⟩
  · rw [b5.regs];simp only [regOut,reduceCtorEq,ite_false];rw [b4.regs];rfl
  · rw [b5.regs];simp only [regOut,reduceCtorEq,ite_false,ite_true];rw [b4.regs .x5]
    rw [b4.kept .x2 (by decide)]
    rw [b3.kept .x2 (by decide)]
    rw [b2.kept .x2 (by decide)]
    rw [b1.kept .x2 (by decide)]
    rw [stack];rfl
  · rw [b5.regs];rfl

theorem dispatch_tail {I} (program : Program I) (s : MachineState) (r : Nat) (lo : 1≤r) (hi : r≤3)
    (here : s.pc=pc 721) (rem : s.getReg .x9=addr r) (stack : s.getReg .x2=addr tableBase) :
    ∃ u, Runs I s u (dispatchCost r) (dispatchCost r) ∧ TailEntry r s u := by
  interval_cases r
  · exact dispatch_1 program s here rem stack
  · exact dispatch_2 program s here rem stack
  · exact dispatch_3 program s here rem stack

end CommitGolfCandidate.Layout2
