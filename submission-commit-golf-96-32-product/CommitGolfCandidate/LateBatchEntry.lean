import CommitGolfCandidate.LateCheckHeader

namespace CommitGolfCandidate.Late.Check.Micro
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open CommitGolfCandidate.Late.Open (W)

/-- Register and memory interface at word 207 for the shared 128-record proof. -/
structure BatchEntry (s t : MachineState) : Prop where
  pc : t.pc=4924
  records : t.getReg .x27=128
  indices : t.getReg .x24=s.getReg .x13
  values : t.getReg .x8=s.getReg .x14
  proof : t.getReg .x25=s.getReg .x15
  root : t.getReg .x26=s.getReg .x11
  slots : t.getReg .x19=s.getReg .x15+65280
  scratch : t.getReg .x21=256
  depth : t.getReg .x30=16
  mem : t.mem=s.mem

theorem batchRegisters (s : MachineState) (pc : s.pc=pcAt 0) (mode : s.getReg .x16=128)
    (size : s.getReg .x17=69120) : BatchEntry s (initialRows s) := by
  have pp:=dispatch_pc s pc;rw [if_pos mode] at pp
  have len:=basic .batchLen (dispatch s) pp rfl
  let t:=Part.batchLen.after (dispatch s)
  have guard : Test.batchLen.taken t=false := by
    change (t.getReg .x6 != t.getReg .x17)=false
    rw [len.regs,len.regs];change (69120 != (dispatch s).getReg .x17)=false
    rw [dispatch_reg s pc];change (69120 != s.getReg .x17)=false;rw [size];rfl
  have ep : (lengthState s true).pc=pcAt 201 := by
    change (Test.batchLen.after t).pc=_;rw [after_pc,guard];rfl
  let u:=lengthState s true
  have ready:=basic .batchReady u ep rfl
  have keep (r : Reg) (ok : Part.batchLen.equation r=Open.original r) :
      u.getReg r=(Part.dispatch.equation r).eval s := by
    change (Test.batchLen.after t).getReg r=_
    rw [after_regs,len.regs,ok]
    have original : (Open.original r).eval (dispatch s)=(dispatch s).getReg r := by cases r <;> rfl
    rw [original,dispatch_reg s pc]
  change BatchEntry s (Part.batchReady.after u)
  refine ⟨ready.pc,?_,?_,?_,?_,?_,?_,ready.regs .x21,ready.regs .x30,?_⟩
  · rw [ready.regs];change u.getReg .x27=128
    rw [keep _ rfl];change s.getReg .x16+0=128;simpa using mode
  · rw [ready.regs];change u.getReg .x24=_;rw [keep _ rfl];change s.getReg .x13+0=_;simp
  · rw [ready.regs];change u.getReg .x8=_;rw [keep _ rfl];change s.getReg .x14+0=_;simp
  · rw [ready.regs];change u.getReg .x25=_;rw [keep _ rfl];change s.getReg .x15+0=_;simp
  · rw [ready.regs];change u.getReg .x26=_;rw [keep _ rfl];change s.getReg .x11+0=_;simp
  · rw [ready.regs];change u.getReg .x25+65280=_;rw [keep _ rfl];change (s.getReg .x15+0)+65280=_;simp
  · exact ready.mem.trans ((after_mem .batchLen t).trans (len.mem.trans (dispatch_mem s pc)))

end CommitGolfCandidate.Late.Check.Micro
