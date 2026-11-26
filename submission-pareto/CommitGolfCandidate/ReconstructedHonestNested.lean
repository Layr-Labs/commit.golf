import CommitGolfCandidate.ReconstructedHonestCuts

namespace CommitGolfCandidate.Reconstruction.HonestNested
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp HonestCuts

/-- A partial segment after the most recent inner checkpoint. -/
inductive Prefix (im : Image) (coins : Bool) (cut : Word → Bool) : MachineState → MachineState → Prop
  | empty (s : MachineState) : Prefix im coins cut s s
  | snoc {s t : MachineState} {r : Execution} (start : Prefix im coins cut s t)
      (run : r ∈ support (execute im 1 t coins)) (cont : r.exit=.unfinished)
      (inside : cut r.state.pc=false) : Prefix im coins cut s r.state

theorem join {im : Image} {coins : Bool} {cut : Word → Bool} {s t u : MachineState}
    (pre : Prefix im coins cut s t) (tail : Reaches im coins cut t u) : Reaches im coins cut s u := by
  induction pre with
  | empty => exact tail
  | snoc _ run cont inside ih => exact ih (.more run cont inside tail)

/-- Refining a loop-body checkpoint into smaller independently checked segments
preserves every conclusion about the original concrete endpoint. -/
theorem carry {im : Image} {coins : Bool} {outer inner : Word → Bool}
    (sub : ∀ pc, outer pc=true → inner pc=true) (Start End : MachineState → Prop)
    (edge : ∀ s t, Start s → Reaches im coins inner s t →
      (outer t.pc=true → End t) ∧ (outer t.pc=false → Start t))
    {s t : MachineState} (start : Start s) (walk : Reaches im coins outer s t) : End t := by
  suffices result : ∀ origin, Start origin → Prefix im coins inner origin s → End t from
    result _ start (.empty s)
  clear start
  induction walk with
  | hit run cont done =>
    intro origin marked pre
    exact (edge _ _ marked (join pre (.hit run cont (sub _ done)))).1 done
  | @more s t out run cont inside tail ih =>
    intro origin marked pre
    cases cut : inner out.state.pc with
    | true =>
      have moved := (edge _ _ marked (join pre (.hit run cont cut))).2 inside
      exact ih _ moved (.empty _)
    | false => exact ih _ marked (.snoc pre run cont cut)

end CommitGolfCandidate.Reconstruction.HonestNested
