import CommitGolfCandidate.R1bParentTraceContent
namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
open CommitGolfCandidate (read_buffer_slice read_buffer_memory_congr checkEvaluation check_evaluation_bind
  check_evaluation_pure check_evaluation_public_bind write_bits_read_outside write_bits_digest)
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
attribute [local irreducible] writeBits checkEvaluation parentsTrace packedParentsTrace packedParentGroups hybridLowerFor hybridUpper hybridParentPhase readBuffer R1bParents.trace

private theorem frameContent (heap : Nat → BitVec 256) (salts : Index → BitVec 128) (a b : MachineState) (n : Nat) (mem : a.mem=b.mem) (initial : ParentContent b heap salts n) :
    ParentContent a heap salts n := by
  constructor
  · intro j lo hi;unfold nodeDigest;rw [read_buffer_memory_congr _ b mem];exact initial.nodes j lo hi
  · intro i;unfold nonceBuffer;rw [read_buffer_memory_congr _ b mem];exact initial.nonces i

private theorem upper_content_at (oracle : Oracle) (mid : MachineState) (heap : Nat → BitVec 256)
    (salts : Index → BitVec 128)
    (masked : ∀ (i : Nat), 0 < i → i ≤ hybridCut → heap i=R1bParents.retained i (oracle.compression (heap (2*i+1) ++ heap (2*i))))
    (prior : ParentContent mid heap salts hybridCut) (regs : ParentRegs mid hybridCut) :
    ParentContent (checkEvaluation oracle (hybridUpper (mid.setPC 4180))).1 heap salts 0 := by
  have preserved : (R1bParents.setup (mid.setPC 4180) 5).mem=mid.mem := rfl
  have shifted : ParentRegs (mid.setPC 4180) hybridCut :=
    ⟨regs.source,regs.target,regs.selector,regs.size,regs.primitive,regs.heap⟩
  unfold hybridUpper
  exact new_trace_content oracle _ heap salts hybridCut le_rfl masked (frameContent heap salts _ mid hybridCut preserved prior)
    (R1bParents.setupReady (mid.setPC 4180) rfl shifted)

private theorem join_content (oracle : Oracle) (s : MachineState) (heap : Nat → BitVec 256)
    (salts : Index → BitVec 128) (span groups : Nat) (bound : hybridCut+span*groups<LENGTH)
    (raw : ∀ (i : Nat), hybridCut < i → i < LENGTH → heap i=oracle.compression (heap (2*i+1) ++ heap (2*i)))
    (masked : ∀ (i : Nat), 0 < i → i ≤ hybridCut → heap i=R1bParents.retained i (oracle.compression (heap (2*i+1) ++ heap (2*i))))
    (prior : ParentContent s heap salts (hybridCut+span*groups)) (regs : ParentRegs s (hybridCut+span*groups)) :
    ParentContent (checkEvaluation oracle (hybridLowerFor span groups s >>= fun mid=>hybridUpper (mid.setPC 4180))).1 heap salts 0 := by
  have lo:=hybrid_lower_content oracle s heap salts span groups bound raw prior regs
  exact content_bound oracle (hybridLowerFor span groups s) (fun t=>hybridUpper (t.setPC 4180)) heap salts 0
    (upper_content_at oracle _ heap salts masked lo.1 lo.2)

theorem hybrid_parent_content (oracle : Oracle) (s : MachineState) (heap : Nat → BitVec 256)
    (salts : Index → BitVec 128)
    (raw : ∀ (i : Nat), hybridCut < i → i < LENGTH → heap i=oracle.compression (heap (2*i+1) ++ heap (2*i)))
    (masked : ∀ (i : Nat), 0 < i → i ≤ hybridCut → heap i=R1bParents.retained i (oracle.compression (heap (2*i+1) ++ heap (2*i))))
    (prior : ParentContent s heap salts (2^24-1)) (regs : ParentRegs s (2^24-1)) :
    ParentContent (checkEvaluation oracle (hybridParentPhase s)).1 heap salts 0 := by
  have start : ParentContent (hybridStart s) heap salts (2^24-1) := frameContent heap salts _ s _ rfl prior
  unfold hybridParentPhase
  exact join_content oracle (hybridStart s) heap salts fullSpan 256 (by decide) raw masked start
    (hybrid_start_regs s _ regs)

theorem counted_lower (oracle : Oracle) (s : MachineState) (n : Nat) :
    RunPublic oracle (hybridLower n s) (fullSpan*n) := by
  induction n generalizing s with
  | zero => simpa only [hybridLower,hybridLowerFor,Nat.mul_zero] using run_pure_public oracle s
  | succ n ih =>
    rw [hybridLower,hybridLowerFor,show fullSpan*(n+1)=fullSpan+fullSpan*n by rw [Nat.mul_succ,Nat.add_comm]]
    exact run_bind_public oracle _ _ fullSpan (fullSpan*n) (counted_parents ..) (fun out => ih _)

private theorem counted_upper (oracle : Oracle) (n : Nat) (s : MachineState) : RunPublic oracle (R1bParents.trace n s) n := by
  induction n generalizing s with
  | zero => rw [R1bParents.trace];exact run_pure_public _ _
  | succ n ih =>
    rw [R1bParents.trace,show n+1=1+n by omega]
    apply run_bind_public _ _ _ 1 n (run_query_public ..)
    intro v;exact ih _

theorem counted_hybrid_phase (oracle : Oracle) (state : MachineState) :
    RunPublic oracle (hybridParentPhase state) 16777215 := by
  unfold hybridParentPhase
  apply run_bind_public _ _ _ 8388608 8388607 (counted_lower oracle _ 256)
  intro out
  unfold hybridUpper
  exact counted_upper oracle _ _

end TwoPermutationPrototype.RV64
