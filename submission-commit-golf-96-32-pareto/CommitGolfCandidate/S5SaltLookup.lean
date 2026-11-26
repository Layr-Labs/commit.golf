import CommitGolfCandidate.S5OpenFrame
import CommitGolfCandidate.S5SiblingLookup
namespace CommitGolfCandidate.S5Machine.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
def recordPC (b : Bool) := if b then 144 else 501
def saltOps : List Calc := [.ld .x14 .x9 0,.addi .x9 .x9 8,.slli .x6 .x14 1,.add .x6 .x6 .x14,
  .slli .x6 .x6 5,.add .x6 .x20 .x6,.andi .x7 .x14 1]
def saltTest (b even : Bool) : PathCode :=
  [(recordPC b+7,.BNE .x7 .x0 8)]++if even then [(recordPC b+8,.ADDI .x6 .x6 72)] else []
def saltStart (b : Bool) (s : MachineState) (i : Index) :=
  pathEnd (evaluated saltOps s) (saltTest b (i.val%2=0))

private theorem layout (b : Bool) :
    ∀ j : Fin 7, decodeInstruction (openWord (recordPC b+j.val))=some (.base (saltOps[j.val]?.getD (.addi .x0 .x0 0)).instr) := by
  cases b <;> decide +kernel

private theorem select (b even : Bool) (s : MachineState) (pc : s.pc=pcAt (recordPC b+7))
    (parity : (s.getReg .x7==0)=even) :
    let code := saltTest b even
    pathReady s code ∧ (pathEnd s code).pc=pcAt (recordPC b+9) ∧
      (pathEnd s code).getReg .x6=s.getReg .x6+(if even then 72 else 0) ∧ (pathEnd s code).mem=s.mem := by
  change (s.regs .x7==0#64)=even at parity
  cases even
  · have ne : s.regs .x7≠0#64 := by simpa using parity
    cases b <;> simp +decide [saltTest,pathReady,pathEnd,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,
      MachineState.getReg,MachineState.setReg,MachineState.setPC,pc,pcAt,recordPC,signExtend12,signExtend13,ne] <;> simp_all +decide
  · have eq:=beq_iff_eq.mp parity
    cases b <;> simp +decide [saltTest,pathReady,pathEnd,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,
      MachineState.getReg,MachineState.setReg,MachineState.setPC,pc,pcAt,recordPC,signExtend12,signExtend13,eq] <;> simp_all +decide

theorem salt_lookup (s : MachineState) (b : Bool) (a : Nat) (i : Index) (pc : s.pc=pcAt (recordPC b))
    (cursor : s.getReg .x9=W a) (safe : accessValid (W a) 8=true) (value : wordAt s a=W i.val)
    (base : s.getReg .x20=W rowBase) :
    let t:=saltStart b s i
    let even:=decide (i.val%2=0)
    Runs s t (if even then 9 else 8) (if even then 9 else 8) ∧ t.pc=pcAt (recordPC b+9) ∧
    t.getReg .x6=W (saltAddress i.val) ∧ t.getReg .x9=W (a+8) ∧ t.getReg .x14=W i.val ∧ t.mem=s.mem ∧
      ∀ r : Reg, r ≠ .x6 → r ≠ .x7 → r ≠ .x9 → r ≠ .x14 → t.getReg r = s.getReg r := by
  let u:=evaluated saltOps s
  let even:=decide (i.val%2=0)
  let code:=saltTest b even
  have orig : live s s original := by intro r;cases r <;> rfl
  have ea : s.getReg .x9+0#64=W a := by rw [BitVec.add_zero,cursor]
  have read : s.getMem (s.getReg .x9+0#64)=W i.val := ea ▸ value
  have hdr:=evaluate_block saltOps (recordPC b) s s original orig rfl pc
    (by cases b <;> decide) (fun c m=>bne_iff_ne.mp (List.all_eq_true.mp (by decide : saltOps.all (fun x=>x.dst != .x0)) c m))
    (by intro x hx;change x∈[Expr.op .add (.reg .x9) (.lit 0)] at hx;obtain rfl:=List.mem_singleton.mp hx
        change accessValid (s.getReg .x9+0#64) 8=true;rw [ea];exact safe)
    (fun j hj=>by simpa only [List.getElem?_eq_getElem hj,Option.getD_some] using layout b ⟨j,hj⟩)
  obtain ⟨first,reg,mem,ip⟩:=hdr
  have idx : u.getReg .x14=W i.val := (reg .x14).trans read
  have ix : u.getReg .x9=W (a+8) := by
    have e:=reg .x9;change _=s.getReg .x9+8 at e
    rw [cursor] at e;exact e.trans (BitVec.ofNat_add ..).symm
  have masked : u.getReg .x7=W (i.val%2) := by
    have e:=reg .x7;change _=s.getMem (s.getReg .x9+0#64) &&& (1 : Word) at e
    rw [read] at e
    change _=BitVec.ofNat 64 i.val &&& BitVec.ofNat 64 (2^1-1) at e
    rw [←BitVec.ofNat_and,Nat.and_two_pow_sub_one_eq_mod] at e;exact e
  have flag : (u.getReg .x7==0)=even := by
    rw [masked];by_cases h : i.val%2=0
    · simp [h,even,W]
    · rw [show i.val%2=1 by omega];simp [W,even,h]
  obtain ⟨ok,last,ptr,mem'⟩:=select b even u ip flag
  have sites : code.all (matchesWord .opening) := (by decide +kernel : ∀ b e : Bool,(saltTest b e).all (matchesWord .opening)) b even
  have second : Runs u (pathEnd u code) code.length code.length := path_run _ _ _ _ sites ok
  have unchanged (r : Reg) (h : r≠.x6) : (pathEnd u code).getReg r=u.getReg r := by
    apply path_keeps_reg
    have eq (m e : Bool) : (saltTest m e).all (fun x=>keepsReg r x.2) := by
      cases m <;> cases e <;> cases r <;> first | decide | contradiction
    exact eq b even
  have cost : 7+code.length=(if even then 9 else 8) := by change 7+(saltTest b even).length=_;cases even <;> rfl
  refine ⟨?_,last,?_,(unchanged _ (by decide)).trans ix,(unchanged _ (by decide)).trans idx,mem'.trans mem,?_⟩
  · rw [←cost];exact first.trans second
  · have e:=reg .x6
    change _=s.getReg .x20+(((s.getMem (s.getReg .x9+0#64) <<< 1)+s.getMem (s.getReg .x9+0#64)) <<< 5) at e
    rw [base,read] at e
    unfold W at e
    rw [shifted,←BitVec.ofNat_add,shifted,←BitVec.ofNat_add] at e
    change (pathEnd u (saltTest b even)).getReg .x6=_
    change u.getReg .x6=_ at e
    rw [ptr,e];by_cases h : i.val%2=0 <;> simp [even,h,saltAddress,W,←BitVec.ofNat_add] <;> congr 1 <;> omega
  · intro r h6 h7 h9 h14
    apply (unchanged r h6).trans
    apply (reg r).trans
    cases r <;> first | rfl | contradiction
end CommitGolfCandidate.S5Machine.Open
