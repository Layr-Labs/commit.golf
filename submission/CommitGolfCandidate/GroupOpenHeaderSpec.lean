import CommitGolfCandidate.GroupOpenPass

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open Opening (RecordMarks)
set_option maxRecDepth 22000
set_option maxHeartbeats 2000000

def layoutRows : List Row :=
  [(0,.ADDI .x20 .x15 0),(1,.ADDI .x21 .x15 0),(2,.BEQ .x16 .x0 2828),(3,.JAL .x0 2840),
   (713,.ADDI .x8 .x13 0),(714,.ADDI .x9 .x12 0),(715,.ADDI .x18 .x16 0),(716,.LUI .x19 1024),
   (717,.LUI .x24 278528),(718,.ADD .x24 .x9 .x24),(719,.LUI .x6 376832),(720,.ADD .x22 .x24 .x6),
   (721,.ADDI .x23 .x0 1),(722,.ADDI .x25 .x9 0),(723,.LUI .x26 1),(724,.ADDI .x27 .x0 256)]
def configRows : List Row :=
  [(725,.ADDI .x10 .x0 1024),(726,.ADDI .x12 .x0 1536),(727,.ADDI .x11 .x0 200),(728,.ADDI .x13 .x0 1),
   (729,.ADDI .x4 .x0 368),(730,.ADDI .x14 .x8 0),(731,.ADDI .x17 .x18 0),(732,.ADDI .x29 .x0 11)]
def keyRows : List Row :=
  [(733,.LD .x31 .x22 8),(734,.SD .x10 .x31 8),(735,.LD .x31 .x22 16),(736,.SD .x10 .x31 16),
   (737,.LD .x31 .x22 24),(738,.SD .x10 .x31 24)]
def headerRows := layoutRows++configRows++keyRows
def header (s : MachineState) := walkRows s headerRows

def keyOf (td : BitVec (8*actual.sizes.trapdoor)) := td.extractLsb' (8*2684354568) 192

theorem nested_slice {n outer width start len : Nat} (word : BitVec n) (bound : start+len≤width) :
    (word.extractLsb' outer width).extractLsb' start len=word.extractLsb' (outer+start) len := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have mid : start+j<width := by omega
  simp [mid,hj,Nat.add_assoc]

structure HeaderFacts : Prop where
  ready : ∀ (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions), 0<p.card → Ready td p (keyOf td) (header (actual.initialState .opening (td,p))) 0
  run : ∀ (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions), 0<p.card → ∀ fuel, let s:=actual.initialState .opening (td,p)
    execute openingImage (30+fuel) s true=(do let z ←execute openingImage fuel (header s) true;return z.charge 30 0)

end TwoPermutationPrototype.GroupedOpening
