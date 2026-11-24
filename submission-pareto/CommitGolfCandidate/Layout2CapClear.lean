import CommitGolfCandidate.Layout2CapFull
namespace CommitGolfCandidate.Layout2.Cap
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Layout2Helpers
open CommitGolfCandidate.Layout2.Quartet (checkImage run_control)
set_option maxRecDepth 20000
set_option maxHeartbeats 1400000

private theorem clear_words : ∀ j : Fin 119,
    (checkImage.code[1034+j.val]?).bind decodeInstruction=some (.base (.SD .x10 .x0 (BitVec.ofNat 12 (8*j.val)))) := by
  intro j;fin_cases j <;> rfl
private theorem clear_imm : ∀ j : Fin 119, signExtend12 (BitVec.ofNat 12 (8*j.val))=addr (8*j.val) := by decide +kernel

theorem clear (s : MachineState) (here : s.pc=pc 1034) (src : s.getReg .x10=addr scratchBase) :
    ∃ t, Runs checkImage s t 120 120 ∧ t.pc=pc 1001 ∧ Writes s t scratchBase 952 (fun _=>0) ∧ Kept temps s t := by
  let P := fun (j : Nat) (u : MachineState)=>u.pc=pc (1034+j) ∧ Writes s u scratchBase (8*j) (fun _=>0) ∧ ∀ r,u.getReg r=s.getReg r
  have init : P 0 s := ⟨here,writes_zero _ _ _,fun _=>rfl⟩
  obtain ⟨u,run,atU⟩:=loop 119 1 1 P s init (by
    intro j hi u h
    obtain ⟨pcU,mem,regs⟩:=h
    let op:=Instr.SD .x10 .x0 (BitVec.ofNat 12 (8*j))
    have address : u.getReg .x10+signExtend12 (BitVec.ofNat 12 (8*j))=addr (scratchBase+8*j) := by
      rw [regs,src,clear_imm ⟨j,hi⟩,addr_add]
    have ok : memoryArgumentsValid u op=true := by
      change accessValid _ 8=true;rw [address];apply access_ok <;> dsimp [scratchBase,MEMORY_BYTES] <;> omega
    let t:=execInstrBr u op
    refine ⟨t,run_control checkImage u (1034+j) op 1 (by omega) pcU (clear_words ⟨j,hi⟩)
      (by simp only [op,ordinaryStep] at ok ⊢;simp only [ok,ite_true]) rfl,?_,?_,?_⟩
    · change u.pc+4=_;rw [pcU,pc_next] <;> congr 1 <;> omega
    · have st : t.mem=(u.setMem (addr (scratchBase+8*j)) 0).mem := by simp only [t,op,execInstrBr,address,zero];rfl
      simpa only [Nat.mul_succ] using (mem.storeZeroWord (by unfold scratchBase;omega) (by unfold scratchBase MEMORY_BYTES;omega)).move rfl st
    · intro r;simpa only [t,op,execInstrBr,MachineState.getReg_setPC,reg_word] using regs r)
  obtain ⟨pcU,clean,regs⟩:=atU
  obtain ⟨t,ret,pcT,memT,_,kt⟩:=ctl_clearExit u pcU
  exact ⟨t,run.thenDo ret,pcT,clean.move rfl memT,(show Kept temps s u from fun r _=>regs r).trans kt⟩
end CommitGolfCandidate.Layout2.Cap
