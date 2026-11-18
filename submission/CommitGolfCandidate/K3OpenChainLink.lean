import CommitGolfCandidate.K3OpenChainRows

/-! Opener chain block (rows 777..795 and the link calls at rows 896..929), the link phase: `Runs` segments
`rows_then`, `call_then`, `keyed_then`, `calls_then`. Owner: O (draft by S9-L2; 33-call chain). -/
namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open CommitGolfCandidate.Permutation.CounterSalt (coord)
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000
set_option pp.deepTerms false

attribute [local simp] Opening.getReg_setReg Opening.getReg_setMem MachineState.getReg_setPC pc_of_set mem_of_set
  mem_of_reg
attribute [local simp] chain_zero_reg

/-- `n` steps from `s` run the oracle program `T`, charging `C` cycles and `K` calls. -/
def Runs (n : Nat) (s : MachineState) (T : OracleComp World MachineState) (C K : Nat) : Prop :=
  ∀ fuel, execute openingImage (n+fuel) s true =
    (do let t ← T; let z ← execute openingImage fuel t true; return z.charge C K)

theorem link_charge_charge (z : Execution) (a b c d : Nat) : (z.charge a b).charge c d=z.charge (c+a) (d+b) := by
  cases z; simp only [Execution.charge,Nat.add_assoc]

theorem Runs.congr {n n' C C' K K' : Nat} {s : MachineState} {T : OracleComp World MachineState}
    (h : Runs n s T C K) (hn : n=n') (hC : C=C') (hK : K=K') : Runs n' s T C' K' := by
  subst hn hC hK; exact h

/-- Ordinary rows, then a segment from the state they reach. -/
theorem rows_then (s : MachineState) (rows : List Row) (valid : legal rows s) (code : presentRows rows)
    {T : OracleComp World MachineState} {m D L : Nat} (h : Runs m (walkRows s rows) T D L) :
    Runs (rows.length+m) s T (price rows+D) L := by
  intro fuel
  rw [Nat.add_assoc,walk_rows_run s rows valid code (m+fuel) true,h fuel]
  simp only [bind_assoc,pure_bind]
  apply bind_congr; intro t; apply bind_congr; intro y
  rw [link_charge_charge,Nat.zero_add]

/-- The empty segment. -/
theorem runs_pure (s : MachineState) : Runs 0 s (pure s) 0 0 := by
  intro fuel
  have e (z : Execution) : z.charge 0 0=z := by cases z; simp only [Execution.charge,Nat.zero_add]
  simp only [Nat.zero_add,pure_bind,e,bind_pure]

/-- Ordinary rows that end the segment. -/
theorem runs_rows (s : MachineState) (rows : List Row) (valid : legal rows s) (code : presentRows rows) :
    Runs rows.length s (pure (walkRows s rows)) (price rows) 0 :=
  (rows_then s rows valid code (runs_pure _)).congr rfl rfl rfl

theorem CallRegs.write {bits : Nat} {s : MachineState} (r : CallRegs s) (dst : Word) (z : BitVec bits) :
    CallRegs (writeBits s dst z) :=
  ⟨(writeBits_register ..).trans r.input,(writeBits_register ..).trans r.output,
    (writeBits_register ..).trans r.selector,(writeBits_register ..).trans r.width,
    (writeBits_register ..).trans r.primitive⟩

/-- A link call at one of the call rows, then a segment from each written state. -/
theorem call_then (s : MachineState) (n : Nat) (lo : 896≤n) (hi : n<929) (pc : s.pc=address n)
    (regs : CallRegs s) {U : MachineState → OracleComp World MachineState} {m D L : Nat}
    (h : ∀ {bits : Nat} (z : BitVec bits), Runs m (writeBits s (wordAddress 192) z) (U (writeBits s (wordAddress 192) z)) D L) :
    Runs (1+m) s (callTrace s >>= U) (8+D) (1+L) := by
  intro fuel
  rw [show 1+m+fuel=(m+fuel)+1 by omega,execute_permutation_call openingImage (m+fuel) s true 192 192 (by decide)
    (by decide) regs.input regs.output regs.selector regs.width regs.primitive (call_fetch s n lo hi pc)]
  simp only [callTrace,bind_assoc,pure_bind]
  apply bind_congr; intro z
  rw [h z fuel]
  simp only [bind_assoc,pure_bind]
  apply bind_congr; intro t; apply bind_congr; intro y
  rw [link_charge_charge]

/-- The keyed generator call at row 789, then the continuation on the written state. -/
def keyedTrace (h : MachineState) (U : MachineState → OracleComp World MachineState) :
    OracleComp World MachineState := do
  let z ← World.query (.inr (.inr (.inl (keyedQuery h))))
  U (writeBits (chainBefore h) (wordAddress 192) z)

/-- The keyed generator call at row 789, then a segment from each written state. -/
theorem keyed_then (h : MachineState) (i : Index) (e : ChainEntry h i)
    {U : MachineState → OracleComp World MachineState} {m D L : Nat}
    (k : ∀ {bits : Nat} (z : BitVec bits),
      Runs m (writeBits (chainBefore h) (wordAddress 192) z) (U (writeBits (chainBefore h) (wordAddress 192) z)) D L) :
    Runs (1+m) (chainBefore h) (keyedTrace h U) (8+D) (1+L) := by
  obtain ⟨_,bpc,_,_,_,bkeep⟩ := chain_before h i e
  have breg (x : Reg) (a : x≠.x7) (b : x≠.x28) (c : x≠.x30) (d : x≠.x31) := bkeep x a b c d
  intro fuel
  rw [show 1+m+fuel=(m+fuel)+1 by omega,
    execute_permutation_call openingImage (m+fuel) (chainBefore h) true 128 192 (by decide) (by decide)
      ((breg _ (by decide) (by decide) (by decide) (by decide)).trans e.input)
      ((breg _ (by decide) (by decide) (by decide) (by decide)).trans e.output)
      ((breg _ (by decide) (by decide) (by decide) (by decide)).trans e.selector)
      ((breg _ (by decide) (by decide) (by decide) (by decide)).trans e.width)
      ((breg _ (by decide) (by decide) (by decide) (by decide)).trans e.primitive) (keyed_fetch _ bpc)]
  simp only [keyedTrace,bind_assoc,pure_bind]
  apply bind_congr; intro z
  rw [k z fuel]
  simp only [bind_assoc,pure_bind]
  apply bind_congr; intro t; apply bind_congr; intro y
  rw [link_charge_charge]

theorem write_regs {bits : Nat} (s : MachineState) (z : BitVec bits) (x : Reg) :
    (writeBits s (wordAddress 192) z).getReg x=s.getReg x := writeBits_register ..

theorem write_at {bits : Nat} (s : MachineState) (z : BitVec bits) (n : Nat) (pc : s.pc=address n) :
    (writeBits s (wordAddress 192) z).pc=address (n+1) := by
  rw [write_pc,pc]; exact address_succ n

/-- `c` consecutive link calls from row `929 - c`, then a segment from any state at row 929. -/
theorem calls_then (c : Nat) : ∀ (s : MachineState), s.pc=address (929-c) → c≤33 → CallRegs s →
    ∀ {U : MachineState → OracleComp World MachineState} {m D L : Nat},
    (∀ b, b.pc=address 929 → CallRegs b → Runs m b (U b) D L) →
    Runs (c+m) s (callsTrace c s >>= U) (8*c+D) (c+L) := by
  induction c with
  | zero =>
    intro s pc _ regs U m D L h
    have e : callsTrace 0 s >>= U=U s := pure_bind _ _
    rw [e]
    exact (h s pc regs).congr (by omega) (by omega) (by omega)
  | succ c ih =>
    intro s pc hc regs U m D L h
    have e : callsTrace (c+1) s >>= U=(callTrace s >>= fun a => callsTrace c a >>= U) := by
      simp only [callsTrace,bind_assoc]
    rw [e]
    refine (call_then s (929-(c+1)) (by omega) (by omega) pc regs (m:=c+m) (D:=8*c+D) (L:=c+L)
      fun z => ih _ ?_ (by omega) (regs.write _ _) h).congr (by omega) (by omega) (by omega)
    rw [write_at _ _ _ pc]; congr 1; omega

end TwoPermutationPrototype.GroupedOpening
