import CommitGolfCandidate.Stage3cCapMarks
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (Levels SaltTape node gapOffset)

def vacantOps : List Calc := [.srli .x6 .x22 1,.slli .x29 .x6 1,.add .x29 .x29 .x6,.slli .x29 .x29 5,
  .andi .x6 .x22 1,.slli .x6 .x6 5,.add .x6 .x29 .x6,.add .x10 .x15 .x6]
def touchedOps : List Calc := [.slli .x6 .x22 1,.add .x6 .x6 .x22,.slli .x6 .x6 5,.add .x10 .x14 .x6]
def capOps (hit : Bool) := if hit then touchedOps else vacantOps
def capLookup (hit : Bool) := if hit then 343 else 334
def secondSide (l r : Bool) : Nat := if l && !r then 1 else 0
def slotLevel (l r : Bool) := if l || r then 15 else 16
def slotIndex (p : Nat) (l r : Bool) := if l || r then 2*p+secondSide l r else p
theorem slot_fits (p : Nat) (small : p<256) (l r : Bool) : slotIndex p l r<levelCount (slotLevel l r) := by
  cases l <;> cases r <;> first | exact small | (change 2*p+1<512;omega) | (change 2*p+0<512;omega)
private theorem addr_plain (p : Nat) (small : p<256) :
    W (layerBase 16)+(((((W p >>> 1) <<< 1)+(W p >>> 1)) <<< 5)+((W p &&& 1) <<< 5))=W (nodeAddress 16 p) := by
  have low : (W p &&& 1)=W (p%2) := by change (BitVec.ofNat 64 p &&& BitVec.ofNat 64 (2^1-1))=_;rw [←BitVec.ofNat_and,Nat.and_two_pow_sub_one_eq_mod];rfl
  rw [low];unfold W;rw [shr p 1 (by omega),shifted,←BitVec.ofNat_add,shifted,shifted,←BitVec.ofNat_add,←BitVec.ofNat_add]
  apply congrArg (BitVec.ofNat 64);change layerBase 16+((p/2*2+p/2)*32+p%2*32)=layerBase 16+(96*(p/2)+32*(p%2));omega

theorem cap_calc (s : MachineState) (hit : Bool) (p : Nat) (small : p<256) (pc : s.pc=pcAt (capLookup hit))
    (pos : s.getReg .x22=W p) (lbase : s.getReg .x14=W (layerBase 15)) (ubase : s.getReg .x15=W (layerBase 16)) :
    let t:=evaluated (capOps hit) s
    let count:=if hit then 4 else 8
    Runs s t count count ∧ t.pc=pcAt (if hit then 347 else 342) ∧ t.mem=s.mem ∧
      t.getReg .x10=W (if hit then nodeAddress 15 (2*p) else nodeAddress 16 p) ∧
      ∀ r,r≠.x6 → r≠.x29 → r≠.x10 → t.getReg r=s.getReg r := by
  have init : live s s original:=by intro r;cases r <;> rfl
  have law:=evaluate_block (capOps hit) (capLookup hit) s s original init rfl pc (by cases hit <;> decide)
    (fun c m=>bne_iff_ne.mp (List.all_eq_true.mp ((by decide +kernel : ∀ b : Bool,(capOps b).all fun c=>c.dst != .x0) hit) c m))
    (by cases hit <;> change ∀ a∈([] : List Expr),_ <;> simp)
    (fun j hj=>by
      have codes : ∀ b : Bool,∀ i : Fin (capOps b).length,decodeInstruction (openWord (capLookup b+i.val))=
        some (.base ((capOps b)[i.val]?.getD (.addi .x0 .x0 0)).instr) :=by decide +kernel
      simpa only [List.getElem?_eq_getElem hj,Option.getD_some] using codes hit ⟨j,hj⟩)
  obtain ⟨run,regs,mem,endPC⟩:=law
  refine ⟨?_,?_,mem,?_,?_⟩
  · cases hit <;> exact run
  · cases hit <;> exact endPC
  · apply (regs .x10).trans
    cases hit
    · change s.getReg .x15+(((((s.getReg .x22 >>> 1) <<< 1)+(s.getReg .x22 >>> 1)) <<< 5)+((s.getReg .x22 &&& 1) <<< 5))=_
      rw [ubase,pos];exact addr_plain p small
    · change s.getReg .x14+(((s.getReg .x22 <<< 1)+s.getReg .x22) <<< 5)=_
      rw [lbase,pos];unfold W;rw [shifted,←BitVec.ofNat_add,shifted,←BitVec.ofNat_add]
      apply congrArg (BitVec.ofNat 64);change layerBase 15+(p*2+p)*32=layerBase 15+(96*(2*p/2)+32*(2*p%2));omega
  · intro r h₁ h₂ h₃;apply (regs r).trans;cases hit <;> cases r <;> first | rfl | contradiction
end CommitGolfCandidate.Chained.BinaryMachine.Open
