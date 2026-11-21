import CommitGolfCandidate.K3OpenChainRows

/-! Opener chain block (rows 777..795 and the link block 896..929), the links: `exit_legal`, `link_run`. -/
namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open CommitGolfCandidate.Permutation.CounterSalt (coord)
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000
set_option pp.deepTerms false

attribute [local simp] Opening.getReg_setReg Opening.getReg_setMem MachineState.getReg_setPC pc_of_set mem_of_set
  mem_of_reg
attribute [local simp] chain_zero_reg

/-- The (empty) exit rows are legal. -/
theorem exit_legal (b : MachineState) (_pc : b.pc=address linkEnd) : legal chainExitRows b := trivial

/-- `c` links (one `ecall` per word up to `linkEnd`), falling through to the salt rows. -/
theorem link_run : ∀ (c : Nat) (s : MachineState), LinkReady s c → c<34 → ∀ fuel,
    execute openingImage (c+fuel) s true =
      (do let t ← linkTrace c s; let z ← execute openingImage fuel (walkRows t chainExitRows) true
          return z.charge (8*c) c)
  | 0,s,_,_,fuel => by
    simp [linkTrace,chainExitRows,walkRows,Execution.charge]
  | c+1,s,r,hc,fuel => by
    rw [show c+1+fuel=(c+fuel)+1 by omega,
      execute_permutation_call openingImage _ s true 192 192 (by decide) (by decide) r.input r.output r.selector
        r.width r.primitive (link_fetch _ (c+1) (by omega) hc r.pc)]
    simp only [linkTrace,bind_assoc,pure_bind]
    apply bind_congr; intro z
    have regs (x : Reg) : (writeBits s (wordAddress 192) z).getReg x=s.getReg x := writeBits_register ..
    have next : LinkReady (writeBits s (wordAddress 192) z) c :=
      ⟨by rw [write_pc,r.pc,address_succ]; congr 1; unfold linkEnd; omega,
        (regs _).trans r.input,(regs _).trans r.output,(regs _).trans r.selector,(regs _).trans r.width,
        (regs _).trans r.primitive⟩
    rw [link_run c _ next (by omega) fuel]
    simp only [bind_assoc,pure_bind]
    apply bind_congr; intro t
    apply bind_congr; intro y; apply congrArg pure
    simp [Execution.charge]
    first | omega | (constructor <;> omega)

end TwoPermutationPrototype.GroupedOpening
