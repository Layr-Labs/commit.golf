import CommitGolfCandidate.QuadCommitPentaRoot

/-! The tree phase of the penta commit image from any leaf-entry state with the right registers:
leaves, clearing the last level-0 group, levels 1 .. 20, the root node, root copy and HALT. -/
namespace TwoPermutationPrototype.Quad.Commit
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling Penta
set_option maxRecDepth 8192
set_option maxHeartbeats 400000
attribute [local irreducible] image execute rootPrefix writeBits

/-! Entry conditions of a level pass at word index `W`. -/
structure Entry (W : Nat) (s : MachineState) : Prop where
  pc : s.pc=BitVec.ofNat 64 (4096+4*W)
  heap : s.getReg .x9=4294971424
  out : s.getReg .x8=4294971392
  selector : s.getReg .x5=0
  size : s.getReg .x11=200
  primitive : s.getReg .x13=1

theorem entry_post {k : Nat} (L : Layout k) (s : MachineState) (e : Entry L.W s)
    {out : MachineState} (hit : out ∈ support (levelTrace L s)) : Entry (L.T+3*L.r+L.z) out := by
  obtain ⟨pc,keep⟩ := level_post L s e.pc e.heap e.selector e.size e.primitive hit
  exact ⟨pc,(keep .x9 (by decide) (by decide) (by decide)).trans e.heap,
    (keep .x8 (by decide) (by decide) (by decide)).trans e.out,
    (keep .x5 (by decide) (by decide) (by decide)).trans e.selector,
    (keep .x11 (by decide) (by decide) (by decide)).trans e.size,
    (keep .x13 (by decide) (by decide) (by decide)).trans e.primitive⟩

theorem chain_level {k : Nat} (L : Layout k) (s : MachineState) (e : Entry L.W s) (rest fuel C N : Nat)
    (cont : MachineState → OracleComp World MachineState)
    (later : ∀ out, Entry (L.T+3*L.r+L.z) out →
      execute image (rest+fuel) out true =
        (do let o ← cont out
            let result ← execute image fuel o true
            return result.charge C N)) :
    execute image (levelSteps L+rest+fuel) s true =
      (do let o ← (levelTrace L s >>= cont)
          let result ← execute image fuel o true
          return result.charge (levelCycles L+C) (pentaCount (k+1)+N)) := by
  rw [Nat.add_assoc,level_run L s e.pc e.heap e.selector e.size e.primitive]
  simp only [bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro out hit
  rw [later out (entry_post L s e hit)]
  simp only [bind_assoc,pure_bind]
  apply bind_congr;intro o
  apply bind_congr;intro result
  simp only [Execution.charge]
  congr 2 <;> omega

def levels (s : MachineState) : OracleComp World MachineState := do
  let s1 ← levelTrace layout1 s
  let s2 ← levelTrace layout2 s1
  let s3 ← levelTrace layout3 s2
  let s4 ← levelTrace layout4 s3
  let s5 ← levelTrace layout5 s4
  let s6 ← levelTrace layout6 s5
  let s7 ← levelTrace layout7 s6
  let s8 ← levelTrace layout8 s7
  let s9 ← levelTrace layout9 s8
  let s10 ← levelTrace layout10 s9
  let s11 ← levelTrace layout11 s10
  let s12 ← levelTrace layout12 s11
  let s13 ← levelTrace layout13 s12
  let s14 ← levelTrace layout14 s13
  let s15 ← levelTrace layout15 s14
  let s16 ← levelTrace layout16 s15
  let s17 ← levelTrace layout17 s16
  let s18 ← levelTrace layout18 s17
  let s19 ← levelTrace layout19 s18
  let s20 ← levelTrace layout20 s19
  pure s20

theorem levels_run (s : MachineState) (e : Entry 45217 s) (fuel : Nat) :
    execute image (12886012+fuel) s true =
      (do let out ← levels s
          let result ← execute image fuel out true
          return result.charge 42950865 4294979) := by
  have finish (out : MachineState) (e : Entry 213663 out) :
      execute image (0+fuel) out true =
        (do let o ← pure out
            let result ← execute image fuel o true
            return result.charge 0 0) := by
    simp [Execution.charge]
  have s20 := fun s e => chain_level layout20 s e 0 fuel 0 0 pure finish
  have s19 := fun s e => chain_level layout19 s e _ fuel _ _ _ (fun out e' => s20 out e')
  have s18 := fun s e => chain_level layout18 s e _ fuel _ _ _ (fun out e' => s19 out e')
  have s17 := fun s e => chain_level layout17 s e _ fuel _ _ _ (fun out e' => s18 out e')
  have s16 := fun s e => chain_level layout16 s e _ fuel _ _ _ (fun out e' => s17 out e')
  have s15 := fun s e => chain_level layout15 s e _ fuel _ _ _ (fun out e' => s16 out e')
  have s14 := fun s e => chain_level layout14 s e _ fuel _ _ _ (fun out e' => s15 out e')
  have s13 := fun s e => chain_level layout13 s e _ fuel _ _ _ (fun out e' => s14 out e')
  have s12 := fun s e => chain_level layout12 s e _ fuel _ _ _ (fun out e' => s13 out e')
  have s11 := fun s e => chain_level layout11 s e _ fuel _ _ _ (fun out e' => s12 out e')
  have s10 := fun s e => chain_level layout10 s e _ fuel _ _ _ (fun out e' => s11 out e')
  have s9 := fun s e => chain_level layout9 s e _ fuel _ _ _ (fun out e' => s10 out e')
  have s8 := fun s e => chain_level layout8 s e _ fuel _ _ _ (fun out e' => s9 out e')
  have s7 := fun s e => chain_level layout7 s e _ fuel _ _ _ (fun out e' => s8 out e')
  have s6 := fun s e => chain_level layout6 s e _ fuel _ _ _ (fun out e' => s7 out e')
  have s5 := fun s e => chain_level layout5 s e _ fuel _ _ _ (fun out e' => s6 out e')
  have s4 := fun s e => chain_level layout4 s e _ fuel _ _ _ (fun out e' => s5 out e')
  have s3 := fun s e => chain_level layout3 s e _ fuel _ _ _ (fun out e' => s4 out e')
  have s2 := fun s e => chain_level layout2 s e _ fuel _ _ _ (fun out e' => s3 out e')
  have s1 := chain_level layout1 s e _ fuel _ _ _ (fun out e' => s2 out e')
  have steps : 12886012=levelSteps layout1+(levelSteps layout2+(levelSteps layout3+(levelSteps layout4+(levelSteps layout5+(levelSteps layout6+(levelSteps layout7+(levelSteps layout8+(levelSteps layout9+(levelSteps layout10+(levelSteps layout11+(levelSteps layout12+(levelSteps layout13+(levelSteps layout14+(levelSteps layout15+(levelSteps layout16+(levelSteps layout17+(levelSteps layout18+(levelSteps layout19+(levelSteps layout20+0))))))))))))))))))) := by decide
  have cycles : levelCycles layout1+(levelCycles layout2+(levelCycles layout3+(levelCycles layout4+(levelCycles layout5+(levelCycles layout6+(levelCycles layout7+(levelCycles layout8+(levelCycles layout9+(levelCycles layout10+(levelCycles layout11+(levelCycles layout12+(levelCycles layout13+(levelCycles layout14+(levelCycles layout15+(levelCycles layout16+(levelCycles layout17+(levelCycles layout18+(levelCycles layout19+(levelCycles layout20+0)))))))))))))))))))=42950865 := by decide
  have calls : pentaCount (0+1)+(pentaCount (1+1)+(pentaCount (2+1)+(pentaCount (3+1)+(pentaCount (4+1)+(pentaCount (5+1)+(pentaCount (6+1)+(pentaCount (7+1)+(pentaCount (8+1)+(pentaCount (9+1)+(pentaCount (10+1)+(pentaCount (11+1)+(pentaCount (12+1)+(pentaCount (13+1)+(pentaCount (14+1)+(pentaCount (15+1)+(pentaCount (16+1)+(pentaCount (17+1)+(pentaCount (18+1)+(pentaCount (19+1)+0)))))))))))))))))))=4294979 := by
    decide
  rw [cycles,calls] at s1
  rw [steps]
  exact s1

end TwoPermutationPrototype.Quad.Commit
