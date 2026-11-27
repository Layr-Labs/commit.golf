import CommitGolfCandidate.Stage3cBatchRecord
import CommitGolfCandidate.Stage3cRecordBranch
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (Levels SaltTape)
open Writer (widths)

structure BatchRegs (s : MachineState) (r k : Nat) : Prop where
  pc : s.pc=pcAt (if r<k then 127 else 324)
  table : s.getReg .x3=W 2048
  indices : s.getReg .x9=W (indexBase+8*r)
  remaining : s.getReg .x22=W (k-r)
  salts : s.getReg .x20=W rowBase
  proof : s.getReg .x18=W proofBase
  marks : s.getReg .x21=W 1024
  flag : s.getReg .x26=1

private theorem mark_tail (s : MachineState) (i : Index) (left : Nat) (small : left<LENGTH)
    (xs seen : List Index) (tree : Levels) (salt : SaltTape) (fs : List Binary.Field) (size : xs.length≤LENGTH)
    (limit : widths fs≤542720) (env : InputRows s xs seen tree salt) (c : FieldCursor tree s fs)
    (pc : s.pc=pcAt 320) (bucket : s.getReg .x14=W (indexAbove i 15)) (base : s.getReg .x21=W 1024)
    (flag : s.getReg .x26=1) (cnt : s.getReg .x22=W (left+1)) :
    ∃ t,Runs s t 4 4 ∧ t.pc=pcAt (if 0<left then 127 else 324) ∧ t.getReg .x22=W left ∧
      FieldCursor tree t fs ∧ InputRows t xs (seen++[i]) tree salt ∧ ∀ q,q≠.x6 → q≠.x22 → t.getReg q=s.getReg q := by
  let j:=indexAbove i 15
  have inside : j<512:=above_bound i 15 (by decide)
  let u:=pathEnd s markPath
  obtain ⟨store,ip,mem,reg⟩:=mark_run s j inside pc base bucket flag
  have marked:=mark_cursor c j inside limit
  have cu:=cursor_same marked mem (reg _ (by decide)) (reg _ (by decide)) (reg _ (by decide)) (reg _ (by decide))
  obtain ⟨back,ep,rem,same,rest⟩:=batch_latch u left small ip ((reg _ (by decide)).trans cnt)
  exact ⟨_,store.trans back,ep,rem,
    cursor_same cu same (rest _ (by decide)) (rest _ (by decide)) (rest _ (by decide)) (rest _ (by decide)),
    inputs_mem (mark_input env size i) (same.trans mem),fun q q6 q22=>(rest q q22).trans (reg q q6)⟩

structure BatchCycle (s t : MachineState) (xs seen : List Index) (tree : Levels) (salt : SaltTape)
    (r : Nat) (fs : List Binary.Field) : Prop where
  run : let i:=ix xs r;let cost:=197+energy (widths fs) (Binary.recordFields tree salt i)
        Runs s t cost (cost+3)
  regs : BatchRegs t (r+1) xs.length
  cursor : FieldCursor tree t (fs++Binary.recordFields tree salt (ix xs r))
  input : InputRows t xs (seen++[ix xs r]) tree salt

attribute [local irreducible] Binary.recordFields energy ix
private theorem cost4 {s u t : MachineState} {a : Nat} (x : Runs s u (193+a) (193+a+3)) (y : Runs u t 4 4) :
    Runs s t (197+a) (197+a+3) := by convert x.trans y using 1 <;> omega

theorem batch_cycle (s : MachineState) (r : Nat) (xs seen : List Index) (tree : Levels) (salt : SaltTape)
    (fs : List Binary.Field) (hr : r<xs.length) (size : xs.length≤LENGTH) (limit : widths fs+3780≤542720)
    (env : InputRows s xs seen tree salt) (cur : FieldCursor tree s fs) (reg : BatchRegs s r xs.length) :
    ∃ t,BatchCycle s t xs seen tree salt r fs := by
  let i:=ix xs r
  let left:=xs.length-(r+1)
  have smaller : left<LENGTH:=by dsimp [left];omega
  obtain ⟨u,body⟩:=batch_record s r xs seen tree salt fs hr size limit cur env (reg.pc.trans (by rw [if_pos hr]))
    reg.indices reg.salts reg.table
  have wlim : widths (fs++Binary.recordFields tree salt i)≤542720 := by rw [sum_append,batch_record_width];exact limit
  obtain ⟨t,tail,ep,rem,c,data,keep⟩:=mark_tail u i left smaller xs seen tree salt _ size wlim body.input body.cursor
    body.pc body.bucket ((body.keep .x21 (by decide) (by decide)).trans reg.marks)
    ((body.keep .x26 (by decide) (by decide)).trans reg.flag)
    ((body.keep .x22 (by decide) (by decide)).trans (reg.remaining.trans (congrArg W (by dsimp [left];omega))))
  have kept (q : Reg) (h : q∈outerRegs) (q9 : q≠.x9) (q22 : q≠.x22) : t.getReg q=s.getReg q :=
    (keep q (by intro e;subst q;exact (by decide : Reg.x6∉outerRegs) h) q22).trans (body.keep q h q9)
  have regs : BatchRegs t (r+1) xs.length := by
    refine ⟨?_,(kept _ (by decide) (by decide) (by decide)).trans reg.table,(keep _ (by decide) (by decide)).trans body.nextIndex,rem,
      (kept _ (by decide) (by decide) (by decide)).trans reg.salts,
      (kept _ (by decide) (by decide) (by decide)).trans reg.proof,(kept _ (by decide) (by decide) (by decide)).trans reg.marks,
      (kept _ (by decide) (by decide) (by decide)).trans reg.flag⟩
    simpa only [show 0<left ↔ r+1<xs.length by dsimp [left];omega] using ep
  refine ⟨t,⟨?_,regs,c,data⟩⟩
  have run:=body.run
  change Runs s u (193+energy _ _) (193+energy _ _+3) at run
  simpa only [Nat.add_assoc] using (cost4 (a:=energy (widths fs) (Binary.recordFields tree salt i))
    (by simpa only [Nat.add_assoc] using run) tail)
end CommitGolfCandidate.Chained.BinaryMachine.Open
