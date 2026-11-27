import CommitGolfCandidate.Stage3cPathAddress
import CommitGolfCandidate.Stage3cOperations
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open CommitGolfCandidate.Late (gapOffset)

inductive Lookup | batch (level : Fin 15) | ordinary (level : Fin 24)
deriving DecidableEq, Fintype
def Lookup.level : Lookup → Nat | .batch j=>j | .ordinary j=>j
def Lookup.pc : Lookup → Nat | .batch j=>140+12*j.val | .ordinary j=>477+19*j.val
def Lookup.dst : Lookup → Reg | .batch _=>.x10 | .ordinary _=>.x6

def Lookup.ops (k : Lookup) : List Calc :=
  [.ld .x4 .x3 (BitVec.ofNat 12 (8*k.level)),.andi .x7 .x14 1,.srli .x14 .x14 1,.xori .x7 .x7 1,
   .slli .x6 .x14 1,.add .x6 .x6 .x14,.slli .x6 .x6 5,.add .x4 .x4 .x6,.slli .x6 .x7 5,.add k.dst .x4 .x6]

private theorem lookup_layout : ∀ k : Lookup,k.pc+10≤939 ∧ (k.ops.all fun c=>c.dst != .x0) ∧
    ∀ j : Fin 10, decodeInstruction (openWord (k.pc+j.val))=some (.base (k.ops[j.val]?.getD (.addi .x0 .x0 0)).instr) := by
  decide +kernel

def Lookup.after (k : Lookup) (s : MachineState) := evaluated k.ops s

theorem sibling_lookup (s : MachineState) (k : Lookup) (pos : Nat) (bound : pos<2^64)
    (pc : s.pc=pcAt k.pc) (table : s.getReg .x3=W 2048) (idx : s.getReg .x14=W pos)
    (layer : wordAt s (2048+8*k.level)=W (layerBase k.level)) :
    let t:=k.after s
    Runs s t 10 10 ∧ t.pc=pcAt (k.pc+10) ∧ t.mem=s.mem ∧ t.getReg .x14=W (pos/2) ∧
      t.getReg k.dst=W (nodeAddress k.level (pos ^^^ 1)) ∧
      ∀ r, r ≠ .x4 → r ≠ .x7 → r ≠ .x6 → r ≠ .x14 → r ≠ k.dst → t.getReg r=s.getReg r := by
  obtain ⟨hi,nz,code⟩:=lookup_layout k
  have off := (by decide +kernel : ∀ j : Fin 24, signExtend12 (BitVec.ofNat 12 (8*j.val))=W (8*j.val))
  have imm : signExtend12 (BitVec.ofNat 12 (8*k.level))=W (8*k.level) :=
    off ⟨k.level,by cases k with | batch i=>exact i.isLt.trans (by decide) | ordinary i=>exact i.isLt⟩
  have ea : s.getReg .x3 + signExtend12 (BitVec.ofNat 12 (8*k.level)) = W (2048+8*k.level) := by
    rw [table,imm];exact (BitVec.ofNat_add ..).symm
  let a := (.op .add (.reg .x3) (.lit (signExtend12 (BitVec.ofNat 12 (8*k.level)))) : Expr)
  have safe : accessValid (a.eval s) 8=true := by
    change accessValid (s.getReg .x3+signExtend12 (BitVec.ofNat 12 (8*k.level))) 8=true
    rw [ea]
    apply access_ok <;> have lt : k.level<24 := by cases k <;> simp [Lookup.level] <;> omega
    all_goals first | omega | (change _≤2^36;omega)
  have regs : live s s original := by intro r;cases r <;> rfl
  have run:=evaluate_block k.ops k.pc s s original regs rfl pc hi
    (fun c m=>bne_iff_ne.mp (List.all_eq_true.mp nz c m))
    (by change ∀ v∈[a],_;simpa using safe)
    (fun j hj=>by have e:=code ⟨j,hj⟩;simpa only [List.getElem?_eq_getElem hj,Option.getD_some] using e)
  obtain ⟨cost,liveOut,mem,last⟩:=run
  have priceOK : price k.ops=10 := by cases k <;> rfl
  rw [priceOK] at cost
  refine ⟨cost,last,mem,?_,?_,?_⟩
  · have h:=liveOut .x14
    have value : ((k.ops.foldl bump original) .x14).eval s=s.getReg .x14 >>> 1 := by cases k <;> rfl
    exact h.trans (value.trans (idx ▸ shr pos 1 bound))
  · have h:=liveOut k.dst
    have v : ((k.ops.foldl bump original) k.dst).eval s =
        s.getMem (s.getReg .x3+signExtend12 (BitVec.ofNat 12 (8*k.level))) +
        ((((s.getReg .x14 >>> 1) <<< 1) + (s.getReg .x14 >>> 1)) <<< 5) +
        (((s.getReg .x14 &&& 1) ^^^ 1) <<< 5) := by cases k <;> rfl
    rw [v,idx,ea,show s.getMem (W (2048+8*k.level))=_ from layer,table_sibling_address _ _ bound] at h
    exact h
  · intro r r4 r7 r6 r14 rd
    apply (liveOut r).trans
    cases k <;> cases r <;> first | rfl | contradiction | exact False.elim (rd rfl)

end CommitGolfCandidate.Chained.BinaryMachine.Open
