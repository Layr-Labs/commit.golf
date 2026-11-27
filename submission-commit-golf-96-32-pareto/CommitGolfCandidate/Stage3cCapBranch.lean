import CommitGolfCandidate.Stage3cCapChoose
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
def selectSlot : Bool→Bool→PathCode
  | false,false=>[(342,.JAL .x0 32)]
  | false,true=>[(347,.BEQ .x7 .x0 12)]
  | true,true=>[(347,.BEQ .x7 .x0 12),(348,.BNE .x28 .x0 8)]
  | true,false=>[(347,.BEQ .x7 .x0 12),(348,.BNE .x28 .x0 8),(349,.ADDI .x10 .x10 32)]

private theorem branch_data (s : MachineState) (p : Nat) (l r : Bool)
    (nxt : s.pc=pcAt (if l || r then 347 else 342)) (lo : s.getReg .x7=flag l) (hi : s.getReg .x28=flag r)
    (addr : s.getReg .x10=W (if l || r then nodeAddress 15 (2*p) else nodeAddress 16 p)) :
    let ops:=selectSlot l r
    pathReady s ops ∧ (pathEnd s ops).pc=pcAt 350 ∧ (pathEnd s ops).mem=s.mem ∧
      (pathEnd s ops).getReg .x10=W (nodeAddress (slotLevel l r) (slotIndex p l r)) := by
  have adjacent : W (nodeAddress 15 (2*p))+32=W (nodeAddress 15 (2*p+1)) := by
    change BitVec.ofNat 64 (nodeAddress 15 (2*p))+BitVec.ofNat 64 32=_;rw [←BitVec.ofNat_add]
    apply congrArg W
    change 4294975488+levelOffset 15+(96*(2*p/2)+32*(2*p%2))+32=4294975488+levelOffset 15+(96*((2*p+1)/2)+32*((2*p+1)%2))
    omega
  change s.regs .x7=flag l at lo
  change s.regs .x28=flag r at hi
  change s.regs .x10=_ at addr
  cases l <;> cases r <;> simp +decide [selectSlot,slotIndex,slotLevel,secondSide,flag,pathReady,pathEnd,ordinaryStep,
    memoryArgumentsValid,memAccess,execInstrBr,MachineState.getReg,MachineState.setReg,MachineState.setPC,
    pcAt,nxt,signExtend12,signExtend13,signExtend21] at * <;> simp_all +decide

theorem cap_source (s : MachineState) (xs : List Index) (p : Nat) (small : p<256) (marks : Marked s xs)
    (pc : s.pc=pcAt 328) (base : s.getReg .x21=W 1024) (pos : s.getReg .x22=W p)
    (lb : s.getReg .x14=W (layerBase 15)) (ub : s.getReg .x15=W (layerBase 16)) :
    let l:=(flags xs p).1
    let r:=(flags xs p).2
    let cost:=Writer.capCost l r-4
    ∃ t,Runs s t cost cost ∧ t.pc=pcAt 350 ∧ t.getReg .x10=W (nodeAddress (slotLevel l r) (slotIndex p l r)) ∧
      t.mem=s.mem ∧ ∀ q,q∉([.x6,.x7,.x10,.x28,.x29] : List Reg)→t.getReg q=s.getReg q := by
  let l:=(flags xs p).1
  let r:=(flags xs p).2
  let u:=pathEnd s markHead
  obtain ⟨hd,ip,left,right,m,unused⟩:=mark_head s xs p small marks pc base pos
  let v:=evaluated (capOps (l || r)) u
  obtain ⟨map,ip',mem,src,keep⟩:=cap_calc u (l || r) p small ip ((unused _ (by decide)).trans pos)
    ((unused _ (by decide)).trans lb) ((unused _ (by decide)).trans ub)
  obtain ⟨ready,ep,endMem,good⟩:=branch_data v p l r ip' ((keep _ (by decide) (by decide) (by decide)).trans left)
    ((keep _ (by decide) (by decide) (by decide)).trans right) src
  let t:=pathEnd v (selectSlot l r)
  have walk : Runs v t (selectSlot l r).length (selectSlot l r).length:=
    path_run _ true _ _ ((by decide +kernel : ∀ a b : Bool,(selectSlot a b).all (matchesWord .opening)) l r) ready
  have price : 6+(if l || r then 4 else 8)+(selectSlot l r).length=Writer.capCost l r-4:=by cases l <;> cases r <;> decide
  refine ⟨t,price ▸ ((hd.trans map).trans walk),ep,good,endMem.trans (mem.trans m),?_⟩
  intro q safe
  by_cases zero : q=.x0
  · subst q;rfl
  have stable : ∀ a b : Bool,(selectSlot a b).all (fun x=>keepsReg q x.2) := by
    intro a b;cases a <;> cases b <;> cases q <;> first | decide | contradiction | (exfalso;apply safe;decide)
  apply (path_keeps_reg _ v q (stable l r)).trans
  apply (keep q (by intro e;subst q;simp at safe) (by intro e;subst q;simp at safe) (by intro e;subst q;simp at safe)).trans
  apply unused;intro h;apply safe;cases q <;> simp_all
end CommitGolfCandidate.Chained.BinaryMachine.Open
