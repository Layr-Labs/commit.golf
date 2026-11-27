import CommitGolfCandidate.Stage3cHeaders
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

structure Common (s : MachineState) : Prop where
  mode : s.getReg .x5=0
  len : s.getReg .x11=96
  kind : s.getReg .x13=0
  base : s.getReg .x18=4294975488
  root : s.getReg .x9=4294971392
  scratch : s.getReg .x24=7516200960
  stride₁ : s.getReg .x25=4096
  stride₂ : s.getReg .x26=2944
  stride₃ : s.getReg .x27=0

theorem seed_inputs (s : MachineState) (c : Common s) : Agrees phaseSeed s := by
  intro r v eq;cases r <;> simp only [phaseSeed,Option.some.injEq,reduceCtorEq] at eq <;>
    subst v <;> first | rfl | exact c.mode | exact c.len | exact c.kind | exact c.base | exact c.root |
      exact c.scratch | exact c.stride₁ | exact c.stride₂ | exact c.stride₃

private theorem common_outputs : ∀ d : Height,
    completeHeader d .x5=some 0 ∧ completeHeader d .x11=some 96 ∧ completeHeader d .x13=some 0 ∧
    completeHeader d .x18=some 4294975488 ∧ completeHeader d .x9=some 4294971392 ∧
    completeHeader d .x24=some 7516200960 ∧ completeHeader d .x25=some 4096 ∧
    completeHeader d .x26=some 2944 ∧ completeHeader d .x27=some 0 := by decide +kernel

structure EnteredFrame (s : MachineState) (d : Height) : Prop extends Common s where
  pc : s.pc=pcAt (bodyEntry d)
  chainSrc : chained d → s.getReg .x21=BitVec.ofNat 64 (nodeAddress d.val 0+cursorBias d)
  chainDst : chained d → s.getReg .x22=BitVec.ofNat 64 (nodeAddress (d.val+1) 0+cursorBias d)
  ptrSrc : ¬chained d → s.getReg .x10=BitVec.ofNat 64 (nodeAddress d.val 0)
  ptrDst : ¬chained d → s.getReg .x12=BitVec.ofNat 64 (nodeAddress (d.val+1) 0)
  counter : tileSize d≠0 → s.getReg .x20=BitVec.ofNat 64 (tiles d)
  tag : chained d → s.getReg .x29=BitVec.ofNat 64 (2^63+256*(d.val+1))
  mask : chained d → s.getReg .x30=BitVec.ofNat 64 (2^(wireWidth d-224)-1)

theorem entered_frame (d : Height) (s : MachineState) (atStart : s.pc=pcAt (pureEntry d)) (c : Common s) :
    EnteredFrame (entered s d) d ∧ (entered s d).mem=s.mem := by
  obtain ⟨legal,size,chain,plain⟩:=header_facts d
  have ok:=fun op mem=>List.all_eq_true.mp legal op mem
  have known : Agrees (completeHeader d) (entered s d):=known_header _ _ _ ok (seed_inputs s c)
  obtain ⟨mem,pc⟩:=header_properties (headerOps d) s ok
  obtain ⟨q5,q11,q13,q18,q9,q24,q25,q26,q27⟩:=common_outputs d
  refine ⟨⟨⟨known _ _ q5,known _ _ q11,known _ _ q13,known _ _ q18,known _ _ q9,
    known _ _ q24,known _ _ q25,known _ _ q26,known _ _ q27⟩,?_,
    fun h=>known _ _ (chain h).1,fun h=>known _ _ (chain h).2.1,
    fun h=>known _ _ (plain h).1,fun h=>known _ _ (plain h).2.1,
    fun h=>if hc:chained d then known _ _ (chain hc).2.2.1 else known _ _ ((plain (by simpa using hc)).2.2 h),
    fun h=>known _ _ (chain h).2.2.2.1,fun h=>known _ _ (chain h).2.2.2.2⟩,mem⟩
  change (List.foldl execInstrBr s (headerOps d)).pc=_
  rw [pc,atStart,←size,pcAt,pcAt,←BitVec.ofNat_add];apply congrArg (BitVec.ofNat 64);omega
end CommitGolfCandidate.Chained.BinaryMachine
