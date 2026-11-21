import CommitGolfCandidate.GroupOpenWholeLayout
import CommitGolfCandidate.GroupOpenShifted32

namespace TwoPermutationPrototype.GroupedOpening.Whole
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 PackedOpening
open Wide Shifted30 CapCopy
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
abbrev pcAt := AlignedFields.pcAt
def Slice (w : Nat) (xs : List Instr) : Prop :=
  ((openingImage.code.drop w).take xs.length).map Opening.decodeBase = xs.map some
instance (w : Nat) (xs : List Instr) : Decidable (Slice w xs) := by unfold Slice; infer_instance
theorem codeOfSlice {w : Nat} {xs : List Instr} (h : Slice w xs) : CodeAt w xs := by
  intro j
  have e := congrArg (fun ys : List (Option Instr) => ys[j.val]?) h
  simp only [List.getElem?_map, List.getElem?_take, j.isLt, ite_true,
    List.getElem?_drop, List.getElem?_eq_getElem j.isLt, Option.map_some] at e
  cases hit : openingImage.code[w+j.val]? with
  | none => simp [hit] at e
  | some v =>
    simp only [hit, Option.map_some, Option.some.injEq] at e
    simpa [Decodes, hit] using e

def pairRows (n width : Nat) (src : Reg) (p dst : Nat) : List Instr :=
  List.ofFn fun j : Fin (2*n) => if j.val%2=0 then wideLoad width src (p+width*(j.val/2))
    else wideStore width (dst+width*(j.val/2))

theorem pairsOfSlice {w n width p dst : Nat} {src : Reg} (h : Slice w (pairRows n width src p dst)) :
    PairsAt w n width src p dst := by
  have size : (pairRows n width src p dst).length=2*n := by simp [pairRows]
  intro j hj
  have a := codeOfSlice h ⟨2*j,by omega⟩
  have b := codeOfSlice h ⟨2*j+1,by omega⟩
  simp only [pairRows,List.getElem_ofFn] at a b
  refine ⟨?_,?_⟩
  · simpa [show 2*j%2=0 by omega,show 2*j/2=j by omega] using a
  · simpa [show (2*j+1)%2=1 by omega,show (2*j+1)/2=j by omega,Nat.add_assoc] using b

def sixRows (src : Reg) (off p : Nat) : List Instr :=
  [.LD .x31 src (BitVec.ofNat 12 p),.SH .x21 .x31 (BitVec.ofNat 12 (off+p)),
   .SRLI .x31 .x31 16,.SW .x21 .x31 (BitVec.ofNat 12 (off+p+2))]

def RawCode (q : Shape) (w : Nat) (src : Reg) (off : Nat) : Prop := match q with
  | .d16 => Slice (w+0) (pairRows 2 8 src 0 (off+0))
  | .w16 => Slice (w+0) (pairRows 4 4 src 0 (off+0))
  | .s16 => Slice (w+0) (Shifted32.chunkCode src off 0) ∧ Slice (w+6) (Shifted32.chunkCode src off 8)
  | .d28 => Slice (w+0) (pairRows 3 8 src 0 (off+0)) ∧ Slice (w+6) (pairRows 1 4 src 24 (off+24))
  | .w28 => Slice (w+0) (pairRows 7 4 src 0 (off+0))
  | .s28 => Slice (w+0) (Shifted32.chunkCode src off 0) ∧ Slice (w+6) (Shifted32.chunkCode src off 8) ∧ Slice (w+12) (Shifted32.chunkCode src off 16) ∧ Slice (w+18) (pairRows 2 2 src 24 (off+24))
  | .d30 => Slice (w+0) (pairRows 3 8 src 0 (off+0)) ∧ Slice (w+6) (pairRows 1 4 src 24 (off+24)) ∧ Slice (w+8) (pairRows 1 2 src 28 (off+28))
  | .w30 => Slice (w+0) (pairRows 7 4 src 0 (off+0)) ∧ Slice (w+14) (pairRows 1 2 src 28 (off+28))
  | .s30 => Slice (w+0) (Shifted32.chunkCode src off 0) ∧ Slice (w+6) (Shifted32.chunkCode src off 8) ∧ Slice (w+12) (Shifted32.chunkCode src off 16) ∧ Slice (w+18) (sixRows src off 24)
  | .d32 => Slice (w+0) (pairRows 4 8 src 0 (off+0))
  | .w32 => Slice (w+0) (pairRows 8 4 src 0 (off+0))
  | .s32 => Slice (w+0) (Shifted32.chunkCode src off 0) ∧ Slice (w+6) (Shifted32.chunkCode src off 8) ∧ Slice (w+12) (Shifted32.chunkCode src off 16) ∧ Slice (w+18) (Shifted32.chunkCode src off 24)

instance (q : Shape) (w : Nat) (src : Reg) (off : Nat) : Decidable (RawCode q w src off) := by
  cases q <;> unfold RawCode <;> infer_instance

theorem raw_code (c : Fin 4) (f : Fin 18) : RawCode (shape c f) (rawStart c f) (source f) (offset f) := by
  revert f; fin_cases c <;> decide +kernel

def rawState (q : Shape) (src : Reg) (off : Nat) (s : MachineState) : MachineState := match q with
  | .d16 => (pairsRun 8 src 0 (off+0) 0 2 s)
  | .w16 => (pairsRun 4 src 0 (off+0) 0 4 s)
  | .s16 => (execCode (execCode s (Shifted32.chunkCode src off 0)) (Shifted32.chunkCode src off 8))
  | .d28 => (pairsRun 4 src 24 (off+24) 0 1 (pairsRun 8 src 0 (off+0) 0 3 s))
  | .w28 => (pairsRun 4 src 0 (off+0) 0 7 s)
  | .s28 => (pairsRun 2 src 24 (off+24) 0 2 (execCode (execCode (execCode s (Shifted32.chunkCode src off 0)) (Shifted32.chunkCode src off 8)) (Shifted32.chunkCode src off 16)))
  | .d30 => (pairsRun 2 src 28 (off+28) 0 1 (pairsRun 4 src 24 (off+24) 0 1 (pairsRun 8 src 0 (off+0) 0 3 s)))
  | .w30 => (pairsRun 2 src 28 (off+28) 0 1 (pairsRun 4 src 0 (off+0) 0 7 s))
  | .s30 => (execCode (execCode (execCode (execCode s (Shifted32.chunkCode src off 0)) (Shifted32.chunkCode src off 8)) (Shifted32.chunkCode src off 16)) (sixRows src off 24))
  | .d32 => (pairsRun 8 src 0 (off+0) 0 4 s)
  | .w32 => (pairsRun 4 src 0 (off+0) 0 8 s)
  | .s32 => (execCode (execCode (execCode (execCode s (Shifted32.chunkCode src off 0)) (Shifted32.chunkCode src off 8)) (Shifted32.chunkCode src off 16)) (Shifted32.chunkCode src off 24))

def TargetAligned (q : Shape) (T : Nat) : Prop := match q with
  | .d16 | .d28 | .d30 | .d32 => T%8=0
  | .w16 | .w28 | .w30 | .w32 => T%8=4
  | _ => T%4=2

instance (q : Shape) (T : Nat) : Decidable (TargetAligned q T) := by
  cases q <;> unfold TargetAligned <;> infer_instance

theorem target_aligned (c : Fin 4) (f : Fin 18) (T : Nat) (r : T%8=destResidue c f) :
    TargetAligned (shape c f) T := by
  have h : ∀ a : Fin 4, ∀ b : Fin 18, TargetAligned (shape a b) (destResidue a b) := by
    decide
  have ht := h c f
  cases eq : shape c f <;> rw [eq] at ht <;> simp only [TargetAligned,←r,Nat.mod_mod] at * <;> omega

theorem placed (c : Fin 4) (f : Fin 18) :
    rawStart c f+(shape c f).cycles ≤ 6144 ∧ (shape c f).size=width f ∧
    source f≠.x31 ∧ offset f+32≤2048 := by
  revert c f; decide

end TwoPermutationPrototype.GroupedOpening.Whole
