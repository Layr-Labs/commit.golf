import CommitGolfCandidate.ReconstructedCheckCapArithInputs
import CommitGolfCandidate.ReconstructedCheckCapPrepare

namespace CommitGolfCandidate.Reconstruction.CheckCapEnter
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CheckRecorded CommitBlocks CheckCapArith
open CheckCapScanData (W fp scratch cap)
open CheckCapLowMemory (proofBase)
set_option maxRecDepth 16000
set_option maxHeartbeats 1000000

def first : List Line := [(.x9,.op (.addi .x0 9)),(.x18,.op (.addi .x0 1)),(.x22,.op (.addi .x0 2)),
  (.x23,.op (.lui 1024)),(.x10,.op (.lui 78848)),(.x27,.addiw .x10 131),(.x27,.op (.slli .x27 5)),
  (.x1,.op (.addi .x0 65)),(.x10,.op (.lui 512))]
def last : List Line := [(.x29,.op (.addi .x8 2048)),(.x29,.op (.addi .x29 3784)),(.x21,.op (.addi .x0 211))]

structure Entry (s : MachineState) (d c : Nat) : Prop where
  pc : s.pc=addr 425
  frame : s.getReg .x8=W fp
  stack : s.getReg .x2=W 68719473296
  depth : s.getReg .x9=W d
  cursor : s.getReg .x24=W c
  table : s.getReg .x23=W cap
  proof : s.getReg .x27=W proofBase
  limit : s.getReg .x1=65
  one : s.getReg .x18=1
  two : s.getReg .x22=2
  slots : s.getReg .x29=W scratch
  radix : s.getReg .x21=211
  magic : s.getReg .x26=W CheckGroupRadix.magic

private theorem first_value (s : MachineState) (q : Reg) (touched : q∈CheckCapArithInputs.finish [.x0] first) :
    (effect s first).getReg q=regs (fun _=>0) first q := by
  apply (register s first q).trans
  exact CheckCapArithInputs.agree s.getReg (fun _=>0) first [.x0] (by intro t h;simp only [List.mem_singleton] at h;subst t;rfl)
    (by decide) q touched

private theorem magic (o : Oracle) (s : MachineState) (pc : s.pc=addr 418) (ptr : s.getReg .x10=2097152)
    (source : s.getMem 2097152=W CheckGroupRadix.magic) :
    Segment o 1 s ((s.setReg .x26 (W CheckGroupRadix.magic)).setPC (addr 419)) [] := by
  apply plain o _ _ _ (CheckMemoryOps.parsed (n:=418) (ins:=.base (.LD .x26 .x10 0)) (by decide) s pc)
  simp only [ordinaryStep,memoryArgumentsValid,memAccess,ptr,show signExtend12 0=0#64 by decide,BitVec.add_zero,
    show accessValid 2097152 8=true by decide,ite_true,execInstrBr,source,pc,addr_next]

attribute [local irreducible] CheckCapArith.effect

def loadState (a : MachineState) := (a.setReg .x26 (W CheckGroupRadix.magic)).setPC (addr 419)
def finishState (b : MachineState) := (effect b last).setPC (addr 425)

private theorem loaded_reg (a : MachineState) (r : Reg) (ne : r≠.x26) :
    (loadState a).getReg r=a.getReg r := by
  simp [loadState,MachineState.getReg_setPC,TwoPermutationPrototype.Opening.getReg_setReg,Ne.symm ne]

private theorem end_reg (b : MachineState) (r : Reg) (ne : r∉last.map Prod.fst) :
    (finishState b).getReg r=b.getReg r := by
  rw [finishState,MachineState.getReg_setPC];exact outside b last r ne

private theorem enter_segment (o : Oracle) (s : MachineState) (pc : s.pc=addr 409)
    (word : s.getMem 2097152=W CheckGroupRadix.magic) : Segment o 14 s (finishState (loadState (effect s first))) [] := by
  let a:=effect s first
  let b:=loadState a
  have pre : Segment o 9 s a []:=CheckCapArith.positive o s 409 first pc (by decide)
  have apc : a.pc=addr 418:=location s 409 first pc
  have am : a.mem=s.mem:=memory s first
  have ptr : a.getReg .x10=2097152:= first_value s .x10 (by decide)
  have ld : Segment o 1 a b []:=magic o a apc ptr ((congrFun am _).trans word)
  have post : Segment o 3 b (effect b last) []:=CheckCapArith.positive o b 419 last rfl (by decide)
  have vpc : (effect b last).pc=addr 422:=location b 419 last rfl
  have j:=CheckBranch.jump o (effect b last) 422 425 12 (by decide) vpc rfl (by decide)
  exact compose (compose (compose pre ld) post) j

private theorem end_values (b : MachineState) (fpReg : b.getReg .x8=W fp) :
    (finishState b).getReg .x29=W scratch ∧ (finishState b).getReg .x21=211 := by
  constructor
  · rw [finishState,MachineState.getReg_setPC,register]
    change (b.getReg .x8+signExtend12 2048)+signExtend12 3784=_
    rw [fpReg];rfl
  · rw [finishState,MachineState.getReg_setPC,register];rfl

private theorem first_run (o : Oracle) (s : MachineState) (pc : s.pc=addr 409) :
    ∃ a,Segment o 9 s a [] ∧ a.pc=addr 418 ∧ a.mem=s.mem ∧
      (∀ q∈CheckCapArithInputs.finish [.x0] first,a.getReg q=regs (fun _=>0) first q) ∧
      ∀ q∉first.map Prod.fst,a.getReg q=s.getReg q :=
  ⟨_,CheckCapArith.positive o s 409 first pc (by decide),location s 409 first pc,memory s first,
   first_value s,fun q h=>outside s first q h⟩

private theorem last_run (o : Oracle) (a : MachineState) (pc : a.pc=addr 418) (fpReg : a.getReg .x8=W fp)
    (addrReg : a.getReg .x10=2097152) (word : a.getMem 2097152=W CheckGroupRadix.magic) :
    ∃ t,Segment o 5 a t [] ∧ t.pc=addr 425 ∧ t.mem=a.mem ∧ t.getReg .x29=W scratch ∧
      t.getReg .x21=211 ∧ t.getReg .x26=W CheckGroupRadix.magic ∧
      ∀ q∉[Reg.x29,.x21,.x26],t.getReg q=a.getReg q := by
  let b:=loadState a
  let t:=finishState b
  have stage:=magic o a pc addrReg word
  have post : Segment o 3 b (effect b last) []:=CheckCapArith.positive o b 419 last rfl (by decide)
  have lastPc : (effect b last).pc=addr 422:=location b 419 last rfl
  have jump:=CheckBranch.jump o (effect b last) 422 425 12 (by decide) lastPc rfl (by decide)
  have bf := (loaded_reg a .x8 (by decide)).trans fpReg
  obtain ⟨slot,rad⟩:=end_values b bf
  have mag : t.getReg .x26=W CheckGroupRadix.magic:=end_reg b .x26 (by decide)
  refine ⟨t,compose (compose stage post) jump,rfl,memory b last,slot,rad,mag,?_⟩
  intro q f
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at f
  exact (end_reg b q (by simp [last,f.1,f.2.1])).trans (loaded_reg a q f.2.2)

theorem run (o : Oracle) (s : MachineState) (c : Nat) (pc : s.pc=addr 409) (fpReg : s.getReg .x8=W fp)
    (sp : s.getReg .x2=W 68719473296) (cursor : s.getReg .x24=W c)
    (word : s.getMem 2097152=W CheckGroupRadix.magic) :
    ∃ t,Segment o 14 s t [] ∧ Entry t 9 c ∧ t.mem=s.mem := by
  obtain ⟨a,pre,pcA,memA,fixed,kept⟩:=first_run o s pc
  have afp:=(kept .x8 (by decide)).trans fpReg
  obtain ⟨t,post,pcT,memT,slot,rad,mag,stable⟩:=last_run o a pcA afp (fixed .x10 (by decide)) ((congrFun memA _).trans word)
  have saved (q : Reg) (f : q∉[Reg.x29,.x21,.x26]) (m : q∉first.map Prod.fst) :
      t.getReg q=s.getReg q := (stable q f).trans (kept q m)
  have known (q : Reg) (f : q∉[Reg.x29,.x21,.x26]) (m : q∈CheckCapArithInputs.finish [.x0] first) :
      t.getReg q=regs (fun _=>0) first q := (stable q f).trans (fixed q m)
  exact ⟨t,compose pre post,⟨pcT,(saved .x8 (by decide) (by decide)).trans fpReg,
    (saved .x2 (by decide) (by decide)).trans sp,known .x9 (by decide) (by decide),
    (saved .x24 (by decide) (by decide)).trans cursor,known .x23 (by decide) (by decide),
    known .x27 (by decide) (by decide),known .x1 (by decide) (by decide),
    known .x18 (by decide) (by decide),known .x22 (by decide) (by decide),slot,rad,mag⟩,memT.trans memA⟩

end CommitGolfCandidate.Reconstruction.CheckCapEnter
