import CommitGolfCandidate.ChainedCheckerCapSchedule

/-! The delivered cap wrapper prepares its heap children before the word2915 hash. -/
namespace CommitGolfCandidate.Chained.Native.CheckerCap
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64
set_option maxRecDepth 8192
attribute [local irreducible] execute
attribute [local simp] MachineState.getReg_setPC MachineState.getReg_setReg_eq MachineState.getReg_setReg_ne
@[local simp] private theorem cap_pc_set (s : MachineState) (pc : Word) : (s.setPC pc).pc=pc := rfl
@[local simp] private theorem cap_zero_reg (s : MachineState) : s.getReg .x0=0#64 := rfl

def capSource (node : Fin 256) : Word := BitVec.ofNat 64 (16384+64*node.val)
def capDestination (node : Fin 256) : Word := BitVec.ofNat 64 (16384+32*node.val)

theorem cap_source_word (node : Fin 256) (word : Fin 8) :
    capSource node+BitVec.ofNat 64 (8*word.val)=wordAddress (2048+8*node.val+word.val) := by
  unfold capSource wordAddress
  rw [←BitVec.ofNat_add]
  congr 1
  omega
theorem cap_source_access (node : Fin 256) (word : Fin 8) :
    accessValid (capSource node+BitVec.ofNat 64 (8*word.val)) 8=true := by
  rw [cap_source_word]
  exact RecordLeaf.aligned_access _ (by omega)
theorem cap_source_first (node : Fin 256) : accessValid (capSource node+signExtend12 24) 8=true := by
  simpa only [show signExtend12 24=BitVec.ofNat 64 (8*3) from by decide +kernel] using cap_source_access node ⟨3,by decide⟩
theorem cap_source_last (node : Fin 256) : accessValid (capSource node+signExtend12 56) 8=true := by
  simpa only [show signExtend12 56=BitVec.ofNat 64 (8*7) from by decide +kernel] using cap_source_access node ⟨7,by decide⟩

@[irreducible] def capMasked (s : MachineState) : MachineState :=
  checkerChildMaskPrefix .cap (checkerSnapshotPrefix 31 s) 9

theorem cap_snapshot_pc (s : MachineState) (pc : s.pc=4096+4*2861) :
    (checkerSnapshotPrefix 31 s).pc=4096+4*2892 := by
  rw [checker_snapshot_pc _ _ (by omega),pc]
  decide +kernel
theorem cap_masked_pc (s : MachineState) (pc : s.pc=4096+4*2861) : (capMasked s).pc=4096+4*2901 := by
  rw [capMasked,checker_child_mask_pc _ _ _ (by omega),cap_snapshot_pc s pc]
  decide +kernel
theorem cap_masked_register (s : MachineState) (reg : Reg) (source : reg≠.x14) (temp : reg≠.x20) :
    (capMasked s).getReg reg=s.getReg reg := by
  rw [capMasked,checker_child_mask_register _ _ _ (by omega) reg source temp,checker_snapshot_register _ _ (by omega)]
theorem cap_masked_source (s : MachineState) : (capMasked s).getReg .x14=s.getReg .x10 := by
  rw [capMasked,checker_child_mask_source _ _ _ (by omega) (by omega),checker_snapshot_register _ _ (by omega)]
  rfl

theorem cap_abi_at : OpsAt chainedCheckerImage (4096+4*2910) checkerHashABIOps :=
  chained_checker_slice_at 2910 5 _ (by rw [chained_checker_ops_length]; decide) (by decide +kernel)
theorem cap_abi_pc (s : MachineState) (pc : s.pc=4096+4*2910) :
    (checkerHashABIPrefix s 5).pc=CheckerHashSite.cap.base := by
  simp [checkerHashABIPrefix,checkerHashABIOps,execInstrBr,pc,CheckerHashSite.base,CheckerHashSite.index]
theorem cap_abi_execution (s : MachineState) (pc : s.pc=4096+4*2910) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (5+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerHashABIPrefix s 5) coins
          return result.charge 5 0) := by
  rw [checking_manifest_image]
  have zero : checkerHashABIPrefix s 0=s := by rw [checkerHashABIPrefix]; rfl
  conv_lhs => rw [←zero]
  apply execute_unit_steps (states := checkerHashABIPrefix s)
  intro i inside
  refine ⟨.base (checkerHashABIOps.getD i .EBREAK),?_,?_,?_⟩
  · apply cap_abi_at i inside
    interval_cases i <;> simp [checkerHashABIPrefix,checkerHashABIOps,execInstrBr,pc,BitVec.add_assoc]
  · interval_cases i <;> rw [checkerHashABIPrefix,checkerHashABIPrefix] <;> rfl
  · interval_cases i <;> rfl

@[irreducible] def capPrepared (height : Fin 8) (s : MachineState) : MachineState :=
  checkerHashABIPrefix (capScheduled height (capMasked s)) 5

structure CapPreparedReady (level : Fin 8) (s : MachineState) : Prop where
  pc : s.pc=CheckerHashSite.cap.base
  args : LoopArgs s 256
  counter : s.getReg .x18=BitVec.ofNat 64 0
  height : s.getReg .x17=BitVec.ofNat 64 (capHeight level).val
  mask : s.getReg .x16=finalMask (capHeight level)
  inputs : ∀ word : Fin 8, accessValid (s.getReg .x14+BitVec.ofNat 64 (8*word.val)) 8=true

theorem cap_prepared_source (height : Fin 8) (s : MachineState) : (capPrepared height s).getReg .x14=s.getReg .x10 := by
  rw [capPrepared,checker_hash_abi_register _ .x14 (by decide) (by decide) (by decide) (by decide) (by decide),
    cap_scheduled_register _ _ .x14 (by decide) (by decide) (by decide) (by decide),cap_masked_source]

theorem cap_prepared_ready (height : Fin 8) (node : Fin 256) (range : CapNodeRange height node)
    (s : MachineState) (pc : s.pc=4096+4*2861) (parent : s.getReg .x6=BitVec.ofNat 64 node.val)
    (source : s.getReg .x10=capSource node) : CapPreparedReady height (capPrepared height s) := by
  have maskedParent : (capMasked s).getReg .x6=BitVec.ofNat 64 node.val :=
    (cap_masked_register s .x6 (by decide) (by decide)).trans parent
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [capPrepared]
    exact cap_abi_pc _ (cap_scheduled_pc height node range _ (cap_masked_pc s pc) maskedParent)
  · rw [capPrepared]
    exact checker_hash_abi_args _
  · rw [capPrepared,checker_hash_abi_register _ .x18 (by decide) (by decide) (by decide) (by decide) (by decide),cap_scheduled_calls]
    rfl
  · rw [capPrepared,checker_hash_abi_register _ .x17 (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact cap_scheduled_height height node range _ (cap_masked_pc s pc) maskedParent
  · rw [capPrepared,checker_hash_abi_register _ .x16 (by decide) (by decide) (by decide) (by decide) (by decide),
      cap_scheduled_mask,cap_canonical_mask]
  · intro word
    rw [cap_prepared_source,source]
    exact cap_source_access node word

theorem cap_prepared_execution (height : Fin 8) (node : Fin 256) (range : CapNodeRange height node)
    (s : MachineState) (pc : s.pc=4096+4*2861) (parent : s.getReg .x6=BitVec.ofNat 64 node.val)
    (source : s.getReg .x10=capSource node) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (52+4*capDepth height+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (capPrepared height s) coins
          return result.charge (52+4*capDepth height) 0) := by
  have maskedParent : (capMasked s).getReg .x6=BitVec.ofNat 64 node.val :=
    (cap_masked_register s .x6 (by decide) (by decide)).trans parent
  have snapshotSource : (checkerSnapshotPrefix 31 s).getReg CheckerHashSite.cap.childReg=capSource node :=
    (checker_snapshot_register 31 s (by omega) .x10).trans source
  have maskedPC := cap_masked_pc s pc
  have scheduledPC := cap_scheduled_pc height node range _ maskedPC maskedParent
  rw [show 52+4*capDepth height+fuel=31+(9+((7+4*capDepth height)+(5+fuel))) by omega,
    checker_snapshot_execution .cap s pc,
    checker_child_mask_execution_at .cap _ (capSource node) (cap_snapshot_pc s pc) snapshotSource
      (cap_source_first node) (cap_source_last node)]
  rw [←capMasked,cap_schedule_execution height node range _ maskedPC maskedParent,cap_abi_execution _ scheduledPC,capPrepared]
  simp [Execution.charge,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
  rw [show 5+(7+(9+(31+4*capDepth height)))=52+4*capDepth height by omega]

def capParentTrace (height : Fin 8) (s : MachineState) : OracleComp World MachineState :=
  checkerHashTrace .cap 0 (capPrepared height s)

theorem cap_parent_execution (height : Fin 8) (node : Fin 256) (range : CapNodeRange height node)
    (s : MachineState) (pc : s.pc=4096+4*2861) (parent : s.getReg .x6=BitVec.ofNat 64 node.val)
    (source : s.getReg .x10=capSource node) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (91+4*capDepth height+fuel) s coins=
      (do let out ← capParentTrace height s
          let result ← execute (Artifact.submission.image .check) fuel out coins
          return result.charge (98+4*capDepth height) 1) := by
  have ready := cap_prepared_ready height node range s pc parent source
  rw [show 91+4*capDepth height+fuel=52+4*capDepth height+(34+continuationInstructions 0+fuel) by
      change 91+4*capDepth height+fuel=52+4*capDepth height+(34+5+fuel); omega,
    cap_prepared_execution height node range s pc parent source,
    artifact_checking_hash .cap 0 (by omega) _ ready.args ready.pc ready.counter ready.inputs]
  simp [capParentTrace,continuationCycles,Execution.charge,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
  rw [show 46+(52+4*capDepth height)=98+4*capDepth height by omega]

theorem cap_parent_pc (height : Fin 8) (node : Fin 256) (range : CapNodeRange height node)
    (s out : MachineState) (pc : s.pc=4096+4*2861) (parent : s.getReg .x6=BitVec.ofNat 64 node.val)
    (source : s.getReg .x10=capSource node) (reached : out∈support (capParentTrace height s)) :
    out.pc=4096+4*2918 := by
  have ready := cap_prepared_ready height node range s pc parent source
  exact checker_hash_return_pc .cap 0 _ out ready.pc reached

theorem cap_parent_bounded (height : Fin 8) (s : MachineState) : PublicQueryBound (capParentTrace height s) 1 :=
  checker_hash_trace_bounded .cap 0 _

theorem cap_parent_content (height : Fin 8) (node : Fin 256) (range : CapNodeRange height node)
    (s : MachineState) (pc : s.pc=4096+4*2861) (parent : s.getReg .x6=BitVec.ofNat 64 node.val)
    (source : s.getReg .x10=capSource node) (left right : BitVec 238)
    (children : ∀ word : Fin 8,
      (capPrepared height s).getMem ((capPrepared height s).getReg .x14+BitVec.ofNat 64 (8*word.val))=
        if word.val<4 then childWord left word.val else childWord right (word.val-4)) :
    (do let out ← capParentTrace height s; pure (readBuffer out 256 32))=
    (do let answer ← (liftM (World.query (.inr (.inl (canonicalEncoding.first (capHeight height) (right ++ left))))) :
          OracleComp World Output)
        let value ← continuationTrace (capHeight height) 0 0 answer
        pure (finalValue (capHeight height) value)) := by
  have ready := cap_prepared_ready height node range s pc parent source
  exact checker_hash_content .cap 0 (by omega) _ ready.args (capHeight height) left right ready.height ready.mask children

end CommitGolfCandidate.Chained.Native.CheckerCap
