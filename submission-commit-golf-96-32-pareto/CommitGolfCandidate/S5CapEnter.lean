import CommitGolfCandidate.S5CapLoop
import CommitGolfCandidate.S5BatchCycle
namespace CommitGolfCandidate.S5Machine.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (Levels SaltTape)

def capEnter : List Calc := [.ld .x14 .x3 120,.ld .x15 .x3 128,.addi .x22 .x0 0,.addi .x9 .x0 171]
theorem cap_enter (s : MachineState) (xs : List Index) (tree : Levels) (salt : SaltTape) (fs : List S5.Field)
    (old : BatchRegs s 128 128) (env : InputRows s xs xs tree salt) (cur : FieldCursor tree s fs) :
    ∃ t,Runs s t 4 4 ∧ CapRegs t 0 ∧ InputRows t xs xs tree salt ∧ FieldCursor tree t fs := by
  have lay : ∀ j : Fin 4,decodeInstruction (openWord (351+j.val))=some (.base ((capEnter[j.val]?.getD (.addi .x0 .x0 0)).instr)) := by decide +kernel
  have gp:=old.table
  have initial : live s s original:=by intro r;cases r <;> rfl
  have safe : ∀ v∈requirements original capEnter,accessValid (v.eval s) 8=true := by
    intro v hv
    change v∈[Expr.op .add (.reg .x3) (.lit (signExtend12 120)),Expr.op .add (.reg .x3) (.lit (signExtend12 128))] at hv
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl | rfl <;> change accessValid (s.getReg .x3+_) 8=true <;> rw [gp] <;> simp only [Expr.eval] <;> decide
  obtain ⟨run,regs,mem,pc⟩:=evaluate_block capEnter 351 s s original initial rfl old.pc (by decide)
    (fun op hm=>bne_iff_ne.mp (List.all_eq_true.mp (by decide : capEnter.all fun op=>op.dst != .x0) op hm)) safe
    (fun j hj=>by simpa only [List.getElem?_eq_getElem hj,Option.getD_some] using lay ⟨j,hj⟩)
  let t:=evaluated capEnter s
  have keep (q : Reg) (h : q∉([.x14,.x15,.x22,.x9] : List Reg)) : t.getReg q=s.getReg q:=by
    apply (regs q).trans;cases q <;> first | rfl | (exfalso;apply h;decide)
  have lb:=regs .x14
  have ub:=regs .x15
  change t.getReg .x14=s.getMem (s.getReg .x3+signExtend12 120) at lb
  change t.getReg .x15=s.getMem (s.getReg .x3+signExtend12 128) at ub
  rw [gp] at lb ub
  have cap : CapRegs t 0:=⟨pc,regs .x22,regs .x9,(keep _ (by decide)).trans old.marks,
    lb.trans (env.table 15 (by decide)),ub.trans (env.table 16 (by decide)),(keep _ (by decide)).trans old.proof⟩
  exact ⟨t,run,cap,inputs_mem env mem,cursor_same cur mem (keep _ (by decide)) (keep _ (by decide)) (keep _ (by decide)) (keep _ (by decide))⟩
end CommitGolfCandidate.S5Machine.Open
