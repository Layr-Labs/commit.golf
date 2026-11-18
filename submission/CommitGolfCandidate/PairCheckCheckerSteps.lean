-- Pair-heads copy of TwoPermutationPackedCheckerSteps (stack/check/work/mkcopy.py); edits below are marked PAIR.
import CommitGolfCandidate.PairCheckImage
import CommitGolfCandidate.PairCheckNamespaces

namespace TwoPermutationPrototype.PairCk.Packed.Checker
open TwoPermutationPrototype.Packed TwoPermutationPrototype.Packed.Checker TwoPermutationPrototype.PairCk.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp

/-- PAIR: `cap_image_fetch` for indices below 1024 (the pair image has 543 words). -/
theorem pair_image_fetch (image : Image) (state : MachineState)
    (index : Nat) (instruction : Instr) (bounded : index < 1024)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * index))
    (decoded : (image.code[index]?).bind decodeInstruction = some (.base instruction)) :
    fetch image state = some (.base instruction) := by
  have numeric : state.pc.toNat = 4096 + 4 * index := by
    rw [pc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    omega
  rw [fetch, numeric, ite_eq_left (by omega), show (4096 + 4 * index - 4096) / 4 = index by omega]
  cases entry : image.code[index]? with
  | none => simp [entry] at decoded
  | some word => simpa only [entry, Option.bind_some] using decoded

theorem fetch_at (s : MachineState) (index : Nat) (instruction : Instr)
    (bounded : index < 494) (pc : s.pc = BitVec.ofNat 64 (4096+4*index))
    (decoded : (pairImage.code[index]?).bind decodeInstruction = some (.base instruction)) :
    fetch pairImage s = some (.base instruction) :=
  pair_image_fetch pairImage s index instruction (by omega) pc decoded

/-- PAIR: fetch anywhere in the 543-word pair image (the even leaf path sits at 494–542). -/
theorem fetch_wide (s : MachineState) (index : Nat) (instruction : Instr)
    (bounded : index < 543) (pc : s.pc = BitVec.ofNat 64 (4096+4*index))
    (decoded : (pairImage.code[index]?).bind decodeInstruction = some (.base instruction)) :
    fetch pairImage s = some (.base instruction) :=
  pair_image_fetch pairImage s index instruction (by omega) pc decoded

/-- Ordinary packed checker code with separately accounted fuel and cycle cost. -/
def Hop (s t : MachineState) (steps cycles : Nat) : Prop :=
  ∀ fuel, execute pairImage (steps+fuel) s false = do
    let result ← execute pairImage fuel t false
    return result.charge cycles 0

abbrev GroupHop (s t : MachineState) (cost : Nat) : Prop := Hop s t cost cost

attribute [local irreducible] execute

theorem Hop.thenDo {s t u : MachineState} {a b c d : Nat}
    (first : Hop s t a c) (last : Hop t u b d) : Hop s u (a+b) (c+d) := by
  intro fuel
  rw [Nat.add_assoc,first,last]
  simp only [bind_assoc,pure_bind,Execution.charge,Nat.zero_add,← Nat.add_assoc]

theorem GroupHop.thenDo {s t u : MachineState} {a b : Nat}
    (first : GroupHop s t a) (last : GroupHop t u b) : GroupHop s u (a+b) :=
  Hop.thenDo first last

end TwoPermutationPrototype.PairCk.Packed.Checker
