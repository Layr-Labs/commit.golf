import CommitGolfCandidate.Layout2Writer2Program

/-! Fused opener (Layout 2 V2 Increment 4b): the record writer of a phase, as Astra's V2a writer model
(`Layout2Writer2.rows`) run on different registers.

Compared with the V2b body (`Layout2Writer2.listing`):
- the head is three instructions `andi a0,t1,3 ; slli a0,a0,5 ; add t3,s5,a0` (no `ld t2,16(s5)`): the saved L22
  pointer is in `s2` (`x18`), kept there by the fused loop's head, and the four L22 loads read `0..24(s2)`;
- the band-B carry lives in `tp` (`x4`) instead of `a1` (`x11`, which keeps the oracle width 200).

The model rows are V2a's (`rows p q`); only the instruction of a row (`op3`) and the starting model (`start3`: `x7`
holds nothing yet) change. `correct3 p q` is checked by the kernel (`Layout2Writer3Phase*`). -/
namespace CommitGolfCandidate.Layout2Writer3
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Layout2Phase Layout2Writer Layout2Writer2
set_option maxRecDepth 16000
set_option maxHeartbeats 1800000

/-- Registers of the model's names in the fused writer: the carry `c` is `tp`. -/
def reg3 : T → Reg | .n=>.x6 | .ptr=>.x7 | .a=>.x10 | .c=>.x4 | .aux=>.x28 | .d=>.x31

/-- The instruction of a model row: L22 loads (field 4) read through `s2`, everything else as V2a with `reg3`. -/
def op3 : Row → Instr
  | .store t j => if routed j then .SD .x28 (reg3 t) (BitVec.ofNat 12 (8*(9+(j-9)%4)))
                   else .SD .x21 (reg3 t) (BitVec.ofNat 12 (8*j))
  | .load d b f j => .LD (reg3 d) (if f=4 then .x18 else reg3 b) (BitVec.ofNat 12 (8*j))
  | .shl d t n => .SLLI (reg3 d) (reg3 t) (BitVec.ofNat 6 n)
  | .shr d t n => .SRLI (reg3 d) (reg3 t) (BitVec.ofNat 6 n)
  | .bor d x y => .OR (reg3 d) (reg3 x) (reg3 y)
  | r => instruction r

/-- The model after the fused head: `x7` holds no field address yet. -/
def start3 : Model := ⟨fun t=>match t with | .n=>.pos | .c=>.carry | x=>.orig x,fun _=>none⟩

/-- Row premises: as V2a's `need`, except that an L22 load (field 4) needs no field address in a model register
(it reads `s2`). -/
def need3 (q p : Nat) (m : Model) (r : Row) : Prop :=
  match r with
  | .store _ j => 8*j+8≤stride p ∧ (routed j=true → m.reg .aux=.orig .aux ∧ 9+4*q≤j ∧ j<13+4*q)
  | .load d b f j => 4≤f ∧ (if f=4 then 8*j+8≤width 4 else pre p m (.load d b f j))
  | .quartet | .root | .ascend .. | .flip .. | .scale .. | .sibling .. | .shl .. | .shr .. | .bor .. => pre p m r
  | _ => False

instance (q p m r) : Decidable (need3 q p m r) := by
  cases r <;> unfold need3 <;> infer_instance

def valid3 (q p : Nat) (m : Model) : List Row→Bool
  | [] => true
  | r::rs => decide (need3 q p m r) && valid3 q p (advance m r) rs

def finalModel3 (p q : Nat) := (rows p q).foldl advance start3

def correct3 (p q : Nat) : Prop :=
  valid3 q p start3 (rows p q)=true ∧ 3+(rows p q).length+1=Layout2Phase2.bodyLen p ∧
    (finalModel3 p q).reg .c=(symStream p).1 ∧ (finalModel3 p q).reg .n=.node 13 ∧
    ∀ d : Fin (stride p/8), (finalModel3 p q).out d.val =
      if Layout2Phase2.written q d.val then some ((expected p).getD (Layout2Phase2.v1Dword d.val) (.data 0)) else none

instance (p q) : Decidable (correct3 p q) := by unfold correct3;infer_instance

def headOps3 : List Instr := [.ANDI .x10 .x6 3,.SLLI .x10 .x10 5,.ADD .x28 .x21 .x10]
def listing3 (p q : Nat) := headOps3 ++ (rows p q).map op3

/-- Number of instructions of the fused writer of phase `p` (one fewer than V2b's body). -/
def writerLen (p : Nat) : Nat := Layout2Phase2.bodyLen p-1

theorem same_listing3 : ∀ p q : Fin 4, listing3 p q=listing3 p 0 := by decide +kernel

theorem listing3_length : ∀ p : Fin 4, (listing3 p 0).length=writerLen p := by decide +kernel

end CommitGolfCandidate.Layout2Writer3
