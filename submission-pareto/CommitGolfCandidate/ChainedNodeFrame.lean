import CommitGolfCandidate.ChainedNodeStep

/-! Support-wise cursor, ABI and memory invariants of a complete delivered node. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
attribute [local irreducible] cursorPrefix branchState

theorem node_source (s out : MachineState) (h : Height) (reached : out ∈ support (nodeTrace h s)) :
    out.getReg .x6 = s.getReg .x6-64 := by
  simp only [nodeTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
  obtain ⟨stored,last,rfl⟩ := reached
  rw [branch_register,cursor_source,store_register s stored h last .x6 (by decide)]

theorem node_target (s out : MachineState) (h : Height) (reached : out ∈ support (nodeTrace h s)) :
    out.getReg .x7 = s.getReg .x7-32 := by
  simp only [nodeTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
  obtain ⟨stored,last,rfl⟩ := reached
  rw [branch_register,cursor_target,store_register s stored h last .x7 (by decide)]

theorem node_register (s out : MachineState) (h : Height) (reached : out ∈ support (nodeTrace h s))
    (reg : Reg)
    (kept : reg ∉ ([.x1,.x6,.x7,.x14,.x18,.x19,.x20,.x21,.x22,.x23,.x24,.x25,.x26,.x27,.x28,.x29,.x30] : List Reg)) :
    out.getReg reg = s.getReg reg := by
  simp only [nodeTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
  obtain ⟨stored,last,rfl⟩ := reached
  rw [branch_register,cursor_register _ reg (by simp_all) (by simp_all),
    store_register s stored h last reg (by simp_all)]

theorem LoopArgs.node {s out : MachineState} (args : LoopArgs s 256) (h : Height)
    (reached : out ∈ support (nodeTrace h s)) : LoopArgs out 256 :=
  ⟨(node_register s out h reached .x10 (by decide)).trans args.source,
    (node_register s out h reached .x12 (by decide)).trans args.target,
    (node_register s out h reached .x5 (by decide)).trans args.selector,
    (node_register s out h reached .x11 (by decide)).trans args.size,
    (node_register s out h reached .x13 (by decide)).trans args.kind,
    args.aligned,args.inputValid,args.outputValid,args.access⟩

theorem node_memory_outside (s out : MachineState) (h : Height) (args : LoopArgs s 256)
    (reached : out ∈ support (nodeTrace h s)) (query : Word) (outside : OutsideScratch query)
    (avoid : ∀ j : Fin 4, query ≠ s.getReg .x7+BitVec.ofNat 64 (8*j.val)) :
    out.getMem query = s.getMem query := by
  simp only [nodeTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
  obtain ⟨stored,last,rfl⟩ := reached
  rw [branch_memory,cursor_memory]
  exact store_memory_outside s stored h args last query outside avoid

end CommitGolfCandidate.Chained.Native
