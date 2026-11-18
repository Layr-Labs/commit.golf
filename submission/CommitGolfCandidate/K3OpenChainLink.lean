import CommitGolfCandidate.K3OpenChainRows

/-! Opener chain block (rows 777..795 and the link groups at rows 4..14), the link loop: `Runs` segments
`rows_then`, `call_then`, `keyed_then`, `group_then`, `rest_then`. Owner: O (draft by S9-L2; 4-unrolled links). -/
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
  r.keep (fun x _ => writeBits_register ..)

/-- A link call at one of the call rows, then a segment from each written state. -/
theorem call_then (s : MachineState) (n : Nat) (hn : n=6 ∨ n=7 ∨ n=8 ∨ n=9 ∨ n=13) (pc : s.pc=address n)
    (regs : CallRegs s) {U : MachineState → OracleComp World MachineState} {m D L : Nat}
    (h : ∀ {bits : Nat} (z : BitVec bits), Runs m (writeBits s (wordAddress 192) z) (U (writeBits s (wordAddress 192) z)) D L) :
    Runs (1+m) s (callTrace s >>= U) (8+D) (1+L) := by
  intro fuel
  rw [show 1+m+fuel=(m+fuel)+1 by omega,execute_permutation_call openingImage (m+fuel) s true 192 192 (by decide)
    (by decide) regs.input regs.output regs.selector regs.width regs.primitive (call_fetch s n hn pc)]
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

/-- `q` groups of four calls from the group head with `4q + c` links to go, then a segment from any state at the
group head with `c` links to go. -/
theorem group_then (q : Nat) : ∀ (c : Nat) (s : MachineState), LinkGroupReady s (4*q+c) → 4*q+c<34 →
    ∀ {U : MachineState → OracleComp World MachineState} {m D L : Nat},
    (∀ g, LinkGroupReady g c → Runs m g (U g) D L) →
    Runs (7*q+m) s (linkGroupTrace q s >>= U) (35*q+D) (4*q+L) := by
  induction q with
  | zero =>
    intro c s r _ U m D L h
    have r' : LinkGroupReady s c := by simpa using r
    have e : linkGroupTrace 0 s >>= U=U s := pure_bind _ _
    rw [e]
    exact (h s r').congr (by omega) (by omega) (by omega)
  | succ q ih =>
    intro c s r hc U m D L h
    obtain ⟨tl,tp⟩ := test_rows s _ (by omega) hc r.pc r.count
    have t30 : (walkRows s groupTestRows).getReg .x30=BitVec.ofNat 64 (4*q+c) := by
      rw [tp.r30]; congr 1; omega
    have regs1 : CallRegs (walkRows s groupTestRows) := r.regs.keep tp.keep
    have e : linkGroupTrace (q+1) s >>= U=(callTrace (walkRows s groupTestRows) >>= fun a => callTrace a >>= fun b =>
        callTrace b >>= fun c' => callTrace c' >>= fun d => linkGroupTrace q (walkRows d groupBackRows) >>= U) := by
      simp only [linkGroupTrace,bind_assoc]
    rw [e]
    refine (rows_then s groupTestRows tl group_test_fetch
      (call_then _ 6 (by decide) tp.pc regs1 (m:=1+(1+(1+(1+(7*q+m))))) (D:=8+(8+(8+(1+(35*q+D)))))
        (L:=1+(1+(1+(4*q+L)))) fun z1 => ?_)).congr
      (by rw [test_len]; omega) (by rw [test_price]; omega) (by omega)
    let a := writeBits (walkRows s groupTestRows) (wordAddress 192) z1
    refine call_then a 7 (by decide) (write_at _ _ 6 tp.pc) (regs1.write _ _) (m:=1+(1+(1+(7*q+m))))
      (D:=8+(8+(1+(35*q+D)))) (L:=1+(1+(4*q+L))) fun z2 => ?_
    let b := writeBits a (wordAddress 192) z2
    refine call_then b 8 (by decide) (write_at _ _ 7 (write_at _ _ 6 tp.pc)) ((regs1.write _ _).write _ _)
      (m:=1+(1+(7*q+m))) (D:=8+(1+(35*q+D))) (L:=1+(4*q+L)) fun z3 => ?_
    let c3 := writeBits b (wordAddress 192) z3
    refine call_then c3 9 (by decide) (write_at _ _ 8 (write_at _ _ 7 (write_at _ _ 6 tp.pc)))
      (((regs1.write _ _).write _ _).write _ _) (m:=1+(7*q+m)) (D:=1+(35*q+D)) (L:=4*q+L) fun z4 => ?_
    let d := writeBits c3 (wordAddress 192) z4
    have dpc : d.pc=address 10 := write_at _ _ 9 (write_at _ _ 8 (write_at _ _ 7 (write_at _ _ 6 tp.pc)))
    have dregs : CallRegs d := (((regs1.write _ _).write _ _).write _ _).write _ _
    have d30 : d.getReg .x30=BitVec.ofNat 64 (4*q+c) := by
      simp only [d,c3,b,a,write_regs]; exact t30
    obtain ⟨bl,bp⟩ := back_rows d dpc
    have ready : LinkGroupReady (walkRows d groupBackRows) (4*q+c) :=
      ⟨bp.pc,bp.r30.trans d30,dregs.keep bp.keep⟩
    exact (rows_then d groupBackRows bl group_back_fetch (ih c _ ready (by omega) h)).congr
      (by rw [back_len]) (by rw [back_price]) (by omega)

/-- `r` single links, then a segment from any state at the exit row. -/
theorem rest_then (r : Nat) : ∀ (s : MachineState), RestReady s r → r<34 →
    ∀ {U : MachineState → OracleComp World MachineState} {m D L : Nat},
    (∀ b : MachineState, b.pc=address 795 → Runs m b (U b) D L) →
    Runs (4*r+m) s (restTrace r s >>= U) (11*r+D) (r+L) := by
  induction r with
  | zero =>
    intro s rr _ U m D L h
    have e : restTrace 0 s >>= U=U s := pure_bind _ _
    rw [e]
    have pc : s.pc=address 795 := by simpa using rr.pc
    exact (h s pc).congr (by omega) (by omega) (by omega)
  | succ r ih =>
    intro s rr hc U m D L h
    have pc : s.pc=address 13 := by simpa using rr.pc
    have e : restTrace (r+1) s >>= U=(callTrace s >>= fun a => restTrace r (walkRows a restRows) >>= U) := by
      simp only [restTrace,bind_assoc]
    rw [e]
    refine (call_then s 13 (by decide) pc rr.regs (m:=3+(4*r+m)) (D:=3+(11*r+D)) (L:=r+L) fun z => ?_).congr
      (by omega) (by omega) (by omega)
    let a := writeBits s (wordAddress 192) z
    have a30 : a.getReg .x30=BitVec.ofNat 64 (r+1) := (write_regs _ _ _).trans rr.count
    obtain ⟨rl,rp⟩ := rest_rows a r hc (write_at _ _ 13 pc) a30
    have ready : RestReady (walkRows a restRows) r := ⟨rp.pc,rp.r30,(rr.regs.write _ _).keep rp.keep⟩
    exact (rows_then a restRows rl rest_fetch (ih _ ready (by omega) h)).congr
      (by rw [rest_len]) (by rw [rest_price]) (by omega)

end TwoPermutationPrototype.GroupedOpening
