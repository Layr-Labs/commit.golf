import CommitGolfCandidate.CapBMachine
import CommitGolfCandidate.GroupOpenImage
namespace CommitGolfCandidate.CapB
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Layout2Helpers
open TwoPermutationPrototype.GroupedOpening (openingImage)
set_option maxRecDepth 20000
set_option maxHeartbeats 1800000
def decodeBase (v : BitVec 32) : Option Instr := match decodeInstruction v with | some (.base op)=>some op | _=>none
def Slice (I : Image) (w : Nat) (xs : List Instr) : Prop :=
  ((I.code.drop w).take xs.length).map decodeBase=xs.map some
instance (I w xs) : Decidable (Slice I w xs) := by unfold Slice;infer_instance

theorem slice_code {I w xs} (h : Slice I w xs) : CodeAt I w xs := by
  intro i
  have eq:=congrArg (fun s : List (Option Instr)=>s[i.val]?) h
  simp only [List.getElem?_map,List.getElem?_take,i.isLt,ite_true,List.getElem?_drop,List.getElem?_eq_getElem i.isLt,Option.map_some] at eq
  cases v : I.code[w+i.val]? with
  | none => simp [v] at eq
  | some v' =>
    simp only [v,Option.map_some,Option.some.injEq] at eq
    unfold decodeBase at eq;cases h : decodeInstruction v' with
    | none => simp [h] at eq
    | some t => cases t <;> simp_all

def prepLayout : Layout := ⟨fun _=>.reg .x26,fun | .dst=>64 | .src=>0⟩
def magic : Expr := let x:=Expr.add (.lit 16908288) (.lit 1032); .bor (.shl x 32) (.shl x 4)
def markExpr (c : Nat) := Expr.shr (.mul (.mem .dst (32+c)) magic) 56
def treeExpr (n : Nat) : Nat → Expr
  | 0 => markExpr (n-32)
  | h+1 => .bor (treeExpr (2*n) h) (treeExpr (2*n+1) h)
def height (n : Nat) := if n<2 then 5 else if n<4 then 4 else if n<8 then 3 else if n<16 then 2 else if n<32 then 1 else 0
def prepRows : List Row := [
  .lui .x5 4128, .addi .x5 .x5 1032, .shl .x6 .x5 4, .shl .x5 .x5 32,
  .bor .x5 .x5 .x6, .ld .x6 .x26 .dst 32, .mul .x6 .x6 .x5, .shr .x6 .x6 56,
  .sd .x6 .x26 32, .ld .x7 .x26 .dst 33, .mul .x7 .x7 .x5, .shr .x7 .x7 56,
  .sd .x7 .x26 33, .bor .x28 .x6 .x7, .sd .x28 .x26 16, .ld .x6 .x26 .dst 34,
  .mul .x6 .x6 .x5, .shr .x6 .x6 56, .sd .x6 .x26 34, .ld .x7 .x26 .dst 35,
  .mul .x7 .x7 .x5, .shr .x7 .x7 56, .sd .x7 .x26 35, .bor .x29 .x6 .x7,
  .sd .x29 .x26 17, .bor .x30 .x28 .x29, .sd .x30 .x26 8, .ld .x6 .x26 .dst 36,
  .mul .x6 .x6 .x5, .shr .x6 .x6 56, .sd .x6 .x26 36, .ld .x7 .x26 .dst 37,
  .mul .x7 .x7 .x5, .shr .x7 .x7 56, .sd .x7 .x26 37, .bor .x28 .x6 .x7,
  .sd .x28 .x26 18, .ld .x6 .x26 .dst 38, .mul .x6 .x6 .x5, .shr .x6 .x6 56,
  .sd .x6 .x26 38, .ld .x7 .x26 .dst 39, .mul .x7 .x7 .x5, .shr .x7 .x7 56,
  .sd .x7 .x26 39, .bor .x29 .x6 .x7, .sd .x29 .x26 19, .bor .x31 .x28 .x29,
  .sd .x31 .x26 9, .bor .x10 .x30 .x31, .sd .x10 .x26 4, .ld .x6 .x26 .dst 40,
  .mul .x6 .x6 .x5, .shr .x6 .x6 56, .sd .x6 .x26 40, .ld .x7 .x26 .dst 41,
  .mul .x7 .x7 .x5, .shr .x7 .x7 56, .sd .x7 .x26 41, .bor .x28 .x6 .x7,
  .sd .x28 .x26 20, .ld .x6 .x26 .dst 42, .mul .x6 .x6 .x5, .shr .x6 .x6 56,
  .sd .x6 .x26 42, .ld .x7 .x26 .dst 43, .mul .x7 .x7 .x5, .shr .x7 .x7 56,
  .sd .x7 .x26 43, .bor .x29 .x6 .x7, .sd .x29 .x26 21, .bor .x30 .x28 .x29,
  .sd .x30 .x26 10, .ld .x6 .x26 .dst 44, .mul .x6 .x6 .x5, .shr .x6 .x6 56,
  .sd .x6 .x26 44, .ld .x7 .x26 .dst 45, .mul .x7 .x7 .x5, .shr .x7 .x7 56,
  .sd .x7 .x26 45, .bor .x28 .x6 .x7, .sd .x28 .x26 22, .ld .x6 .x26 .dst 46,
  .mul .x6 .x6 .x5, .shr .x6 .x6 56, .sd .x6 .x26 46, .ld .x7 .x26 .dst 47,
  .mul .x7 .x7 .x5, .shr .x7 .x7 56, .sd .x7 .x26 47, .bor .x29 .x6 .x7,
  .sd .x29 .x26 23, .bor .x31 .x28 .x29, .sd .x31 .x26 11, .bor .x11 .x30 .x31,
  .sd .x11 .x26 5, .ld .x6 .x26 .dst 48, .mul .x6 .x6 .x5, .shr .x6 .x6 56,
  .sd .x6 .x26 48, .ld .x7 .x26 .dst 49, .mul .x7 .x7 .x5, .shr .x7 .x7 56,
  .sd .x7 .x26 49, .bor .x28 .x6 .x7, .sd .x28 .x26 24, .ld .x6 .x26 .dst 50,
  .mul .x6 .x6 .x5, .shr .x6 .x6 56, .sd .x6 .x26 50, .ld .x7 .x26 .dst 51,
  .mul .x7 .x7 .x5, .shr .x7 .x7 56, .sd .x7 .x26 51, .bor .x29 .x6 .x7,
  .sd .x29 .x26 25, .bor .x30 .x28 .x29, .sd .x30 .x26 12, .ld .x6 .x26 .dst 52,
  .mul .x6 .x6 .x5, .shr .x6 .x6 56, .sd .x6 .x26 52, .ld .x7 .x26 .dst 53,
  .mul .x7 .x7 .x5, .shr .x7 .x7 56, .sd .x7 .x26 53, .bor .x28 .x6 .x7,
  .sd .x28 .x26 26, .ld .x6 .x26 .dst 54, .mul .x6 .x6 .x5, .shr .x6 .x6 56,
  .sd .x6 .x26 54, .ld .x7 .x26 .dst 55, .mul .x7 .x7 .x5, .shr .x7 .x7 56,
  .sd .x7 .x26 55, .bor .x29 .x6 .x7, .sd .x29 .x26 27, .bor .x31 .x28 .x29,
  .sd .x31 .x26 13, .bor .x12 .x30 .x31, .sd .x12 .x26 6, .ld .x6 .x26 .dst 56,
  .mul .x6 .x6 .x5, .shr .x6 .x6 56, .sd .x6 .x26 56, .ld .x7 .x26 .dst 57,
  .mul .x7 .x7 .x5, .shr .x7 .x7 56, .sd .x7 .x26 57, .bor .x28 .x6 .x7,
  .sd .x28 .x26 28, .ld .x6 .x26 .dst 58, .mul .x6 .x6 .x5, .shr .x6 .x6 56,
  .sd .x6 .x26 58, .ld .x7 .x26 .dst 59, .mul .x7 .x7 .x5, .shr .x7 .x7 56,
  .sd .x7 .x26 59, .bor .x29 .x6 .x7, .sd .x29 .x26 29, .bor .x30 .x28 .x29,
  .sd .x30 .x26 14, .ld .x6 .x26 .dst 60, .mul .x6 .x6 .x5, .shr .x6 .x6 56,
  .sd .x6 .x26 60, .ld .x7 .x26 .dst 61, .mul .x7 .x7 .x5, .shr .x7 .x7 56,
  .sd .x7 .x26 61, .bor .x28 .x6 .x7, .sd .x28 .x26 30, .ld .x6 .x26 .dst 62,
  .mul .x6 .x6 .x5, .shr .x6 .x6 56, .sd .x6 .x26 62, .ld .x7 .x26 .dst 63,
  .mul .x7 .x7 .x5, .shr .x7 .x7 56, .sd .x7 .x26 63, .bor .x29 .x6 .x7,
  .sd .x29 .x26 31, .bor .x31 .x28 .x29, .sd .x31 .x26 15, .bor .x13 .x30 .x31,
  .sd .x13 .x26 7, .bor .x6 .x10 .x11, .sd .x6 .x26 2, .bor .x7 .x12 .x13,
  .sd .x7 .x26 3, .bor .x6 .x6 .x7, .sd .x6 .x26 1
]
def prepModel := prepRows.foldl advance initial
theorem prep_code : Slice openingImage 6960 (prepRows.map op) := by decide +kernel
theorem prep_valid : checked prepLayout initial prepRows=true ∧ prepRows.length=195 ∧ price prepRows=291 ∧
    (∀ j : Fin 64,prepModel.out j.val=if j.val=0 then .mem .dst 0 else treeExpr j.val (height j.val)) ∧
    (∀ r : Reg,r∉[.x5,.x6,.x7,.x28,.x29,.x30,.x31,.x10,.x11,.x12,.x13] → prepModel.reg r=.reg r) := by
  refine ⟨by decide +kernel,by decide,by decide,by decide +kernel,?_⟩
  intro r;cases r <;> decide +kernel
end CommitGolfCandidate.CapB
