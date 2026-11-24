import CommitGolfCandidate.ChainedHashExecution

/-! Canonical first query of the delivered shared call. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
attribute [local irreducible] firstPackPrefix

theorem hash_pack_input (s : MachineState) (args : LoopArgs s 256) (h : Height)
    (left right : BitVec 238) (height : s.getReg .x17 = BitVec.ofNat 64 h.val)
    (inputs : ∀ k : Fin 8, s.getMem (s.getReg .x14+BitVec.ofNat 64 (8*k.val)) =
      if k.val < 4 then childWord left k.val else childWord right (k.val-4)) :
    readBuffer (hashPacked s) 256 64 = canonicalEncoding.first h (right ++ left) := by
  have pack := first_pack_input (hashPackStart s) h left right height
    (by rw [args.packStart.source]; decide) inputs
  simpa only [hashPacked,args.packStart.source,show (256 : Word).toNat = 256 from rfl] using pack

theorem hash_trace_first (remaining : Nat) (s : MachineState) (args : LoopArgs s 256)
    (h : Height) (left right : BitVec 238) (height : s.getReg .x17 = BitVec.ofNat 64 h.val)
    (inputs : ∀ k : Fin 8, s.getMem (s.getReg .x14+BitVec.ofNat 64 (8*k.val)) =
      if k.val < 4 then childWord left k.val else childWord right (k.val-4)) :
    hashTrace remaining s =
      (do let answer ← (liftM (World.query (.inr (.inl (canonicalEncoding.first h (right ++ left))))) :
            OracleComp World Output)
          continuationFullTrace 186752 256 remaining (hashContinued s answer)) := by
  rw [hashTrace,hash_pack_input s args h left right height inputs]

end CommitGolfCandidate.Chained.Native
