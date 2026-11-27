import CommitGolfCandidate.Stage3cOpenFrame
import CommitGolfCandidate.Stage3cSiblingLookup
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
def recordPC (b : Bool) := if b then 127 else 460
def saltOps : List Calc := [.ld .x14 .x9 0,.addi .x9 .x9 8,.srli .x6 .x14 1,.addi .x7 .x0 184,
    .mul .x6 .x6 .x7,.add .x6 .x20 .x6,.andi .x7 .x14 1,.slli .x7 .x7 4,.add .x6 .x6 .x7,.addi .x6 .x6 72]
def saltStart (_ : Bool) (s : MachineState) (_ : Index) := evaluated saltOps s
private theorem layout (b : Bool) : ∀ j : Fin 10,decodeInstruction (openWord (recordPC b+j.val))=some (.base (saltOps[j.val]?.getD (.addi .x0 .x0 0)).instr) := by cases b <;> decide +kernel

theorem salt_lookup (s : MachineState) (b : Bool) (a : Nat) (i : Index) (pc : s.pc=pcAt (recordPC b))
    (cursor : s.getReg .x9=W a) (safe : accessValid (W a) 8=true) (value : wordAt s a=W i.val)
    (base : s.getReg .x20=W rowBase) :
    let t:=saltStart b s i
    Runs s t 10 13 ∧ t.pc=pcAt (recordPC b+10) ∧
    t.getReg .x6=W (saltAddress i.val) ∧ t.getReg .x9=W (a+8) ∧ t.getReg .x14=W i.val ∧ t.mem=s.mem ∧
      ∀ r : Reg, r ≠ .x6 → r ≠ .x7 → r ≠ .x9 → r ≠ .x14 → t.getReg r = s.getReg r := by
  let u:=evaluated saltOps s
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
  refine ⟨first,ip,?_,ix,idx,mem,?_⟩
  · have e:=reg .x6
    let z:=s.getMem (s.getReg .x9+0#64)
    change _=(s.getReg .x20+((z >>> 1)*184)+((z &&& 1) <<< 4))+72 at e
    have mz : z=W i.val:=read
    have par : (W i.val &&& 1)=W (i.val%2):=by
      change BitVec.ofNat 64 i.val &&& BitVec.ofNat 64 (2^1-1)=_
      rw [←BitVec.ofNat_and,Nat.and_two_pow_sub_one_eq_mod];rfl
    rw [base,mz,par] at e
    have small:i.val<2^64:=Nat.lt_trans i.isLt (by decide)
    apply e.trans
    change (BitVec.ofNat 64 rowBase+((BitVec.ofNat 64 i.val >>> (1:Nat))*BitVec.ofNat 64 184)
      + (BitVec.ofNat 64 (i.val%2) <<< (4:Nat)))+BitVec.ofNat 64 72=_
    rw [shr i.val 1 small,shifted]
    change ((BitVec.ofNat 64 rowBase+ (BitVec.ofNat 64 (i.val/2)*BitVec.ofNat 64 184))+BitVec.ofNat 64 ((i.val%2)*2^4))+BitVec.ofNat 64 72=_
    rw [←BitVec.ofNat_mul,←BitVec.ofNat_add,←BitVec.ofNat_add,←BitVec.ofNat_add]
    apply congrArg (BitVec.ofNat 64);unfold saltAddress;omega
  · intro r h6 h7 h9 h14
    apply (reg r).trans
    cases r <;> first | rfl | contradiction
end CommitGolfCandidate.Chained.BinaryMachine.Open
