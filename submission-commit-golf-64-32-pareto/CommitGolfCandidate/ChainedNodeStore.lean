import CommitGolfCandidate.ChainedLevelBody
import CommitGolfCandidate.ChainedHeapCopyContent
import CommitGolfCandidate.ChainedHashMemory

/-! A repeated node call stores the canonical chained digest in the heap. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
attribute [local irreducible] execute

def storeTrace (h : Height) (s : MachineState) : OracleComp World MachineState := do
  let hashed ← bodyHashTrace h s
  return copyPrefix hashed 8

theorem store_execution (s : MachineState) (h : Height) (args : LoopArgs s 256)
    (pc : s.pc = bodyPC h)
    (inputs : ∀ k : Fin 8, accessValid (s.getReg .x6+BitVec.ofNat 64 (8*k.val)) 8 = true)
    (outputs : ∀ k : Fin 4, accessValid (s.getReg .x7+BitVec.ofNat 64 (8*k.val)) 8 = true)
    (fuel : Nat) (coins : Bool) :
    execute chainedCommitImage (46+continuationInstructions (calls h-1)+fuel) s coins =
      (do let out ← storeTrace h s
          let result ← execute chainedCommitImage fuel out coins
          return result.charge (53+continuationCycles (calls h-1)) (calls h)) := by
  rw [show 46+continuationInstructions (calls h-1)+fuel =
    38+continuationInstructions (calls h-1)+(8+fuel) by omega,body_hash_execution s h args pc inputs]
  simp only [storeTrace,bind_assoc,pure_bind]
  apply bind_congr_of_forall_mem_support
  intro hashed reached
  have source : hashed.getReg .x10 = 256 :=
    (body_hash_register s hashed h reached .x10 (by decide)).trans args.source
  have target : hashed.getReg .x7 = s.getReg .x7 := body_hash_register s hashed h reached .x7 (by decide)
  have validInputs : ∀ k : Fin 4, accessValid (hashed.getReg .x10+BitVec.ofNat 64 (8*k.val)) 8 = true := by
    rw [source]
    intro k
    fin_cases k <;> decide
  have validOutputs : ∀ k : Fin 4, accessValid (hashed.getReg .x7+BitVec.ofNat 64 (8*k.val)) 8 = true := by
    rw [target]
    exact outputs
  rw [copy_execution hashed h (body_hash_return_pc s hashed h pc reached) validInputs validOutputs]
  simp [Execution.charge,←Nat.add_assoc,
    show 45+continuationCycles (calls h-1)+8 = 53+continuationCycles (calls h-1) by omega]

theorem store_pc (s out : MachineState) (h : Height) (pc : s.pc = bodyPC h)
    (reached : out ∈ support (storeTrace h s)) : out.pc = copyPC h+32 := by
  simp only [storeTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
  obtain ⟨hashed,last,rfl⟩ := reached
  rw [copy_prefix_pc _ 8 (by decide),body_hash_return_pc s hashed h pc last]
  rfl

theorem store_register (s out : MachineState) (h : Height) (reached : out ∈ support (storeTrace h s))
    (reg : Reg)
    (kept : reg ∉ ([.x1,.x14,.x18,.x19,.x20,.x21,.x22,.x23,.x24,.x25,.x26,.x27,.x28,.x29,.x30] : List Reg)) :
    out.getReg reg = s.getReg reg := by
  simp only [storeTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
  obtain ⟨hashed,last,rfl⟩ := reached
  rw [copy_register _ reg (by simp_all),body_hash_register s hashed h last reg kept]

theorem store_memory_outside (s out : MachineState) (h : Height) (args : LoopArgs s 256)
    (reached : out ∈ support (storeTrace h s)) (query : Word) (outside : OutsideScratch query)
    (avoid : ∀ j : Fin 4, query ≠ s.getReg .x7+BitVec.ofNat 64 (8*j.val)) :
    out.getMem query = s.getMem query := by
  simp only [storeTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
  obtain ⟨hashed,last,rfl⟩ := reached
  have target : hashed.getReg .x7 = s.getReg .x7 := body_hash_register s hashed h last .x7 (by decide)
  rw [copy_memory_outside _ query (by rw [target]; exact avoid) 8 (by decide)]
  exact (hash_trace_memory _ _ hashed (args.bodyCalled h) last query outside).trans (body_memory s h query)

theorem body_hash_content (s : MachineState) (h : Height) (args : LoopArgs s 256)
    (left right : BitVec 238) (height : s.getReg .x17 = BitVec.ofNat 64 h.val)
    (mask : s.getReg .x16 = finalMask h)
    (inputs : ∀ k : Fin 8, s.getMem (s.getReg .x6+BitVec.ofNat 64 (8*k.val)) =
      if k.val < 4 then childWord left k.val else childWord right (k.val-4)) :
    (do let out ← bodyHashTrace h s; pure (readBuffer out 256 32)) =
      (do let answer ← (liftM (World.query (.inr (.inl (canonicalEncoding.first h (right ++ left))))) :
            OracleComp World Output)
          let value ← continuationTrace h 0 (calls h-1) answer
          pure (finalValue h value)) := by
  have small : calls h-1 ≤ 7 := by have := calls_bound h; omega
  have data : ∀ k : Fin 8,
      (bodyPrefix s h 3).getMem ((bodyPrefix s h 3).getReg .x14+BitVec.ofNat 64 (8*k.val)) =
        if k.val < 4 then childWord left k.val else childWord right (k.val-4) := by
    intro k
    rw [body_called_source,body_memory]
    exact inputs k
  simpa only [bodyHashTrace] using hash_content (calls h-1) small (bodyPrefix s h 3)
    (args.bodyCalled h) h left right ((body_register s h .x17 (by decide)).trans height)
    ((body_register s h .x16 (by decide)).trans mask) data

theorem store_content (s : MachineState) (h : Height) (args : LoopArgs s 256)
    (left right : BitVec 238) (height : s.getReg .x17 = BitVec.ofNat 64 h.val)
    (mask : s.getReg .x16 = finalMask h)
    (inputs : ∀ k : Fin 8, s.getMem (s.getReg .x6+BitVec.ofNat 64 (8*k.val)) =
      if k.val < 4 then childWord left k.val else childWord right (k.val-4))
    (aligned : (s.getReg .x7).toNat % 8 = 0)
    (separate : ∀ a b : Fin 4, (256 : Word)+BitVec.ofNat 64 (8*a.val) ≠ s.getReg .x7+BitVec.ofNat 64 (8*b.val)) :
    (do let out ← storeTrace h s; pure (readBuffer out (s.getReg .x7).toNat 32)) =
      (do let answer ← (liftM (World.query (.inr (.inl (canonicalEncoding.first h (right ++ left))))) :
            OracleComp World Output)
          let value ← continuationTrace h 0 (calls h-1) answer
          pure (finalValue h value)) := by
  trans (do let hashed ← bodyHashTrace h s; pure (readBuffer hashed 256 32))
  · simp only [storeTrace,bind_assoc,pure_bind]
    apply bind_congr_of_forall_mem_support
    intro hashed reached
    have source : hashed.getReg .x10 = 256 :=
      (body_hash_register s hashed h reached .x10 (by decide)).trans args.source
    have target : hashed.getReg .x7 = s.getReg .x7 := body_hash_register s hashed h reached .x7 (by decide)
    have readback := copy_value hashed (by rw [source]; decide) (by rw [target]; exact aligned)
      (by rw [source,target]; exact separate)
    rw [source,target] at readback
    exact congrArg pure (by simpa only [show (256 : Word).toNat = 256 from rfl] using readback)
  · exact body_hash_content s h args left right height mask inputs

end CommitGolfCandidate.Chained.Native
