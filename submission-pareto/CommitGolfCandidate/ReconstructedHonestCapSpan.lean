import CommitGolfCandidate.ReconstructedHonestPhysical
import CommitGolfCandidate.ReconstructedHonestCapInvariant

namespace CommitGolfCandidate.Reconstruction.HonestCapSpan
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp HonestRanges HonestProtected HonestRegionStep
open HonestCapState HonestCapStages HonestCapRam HonestCapPlan
open HonestRecordMemory (context constant)
open CommitBlocks (addr)

set_option maxRecDepth 32768
attribute [local irreducible] ArtifactEncoding.decode

def flags : Range := ⟨activeBase,activeBase+1023⟩

def check (clock : Nat) (pc : Word) (a : Abstract) : Bool := match clock with
  | 0 => false
  | k+1 => match HonestBlocks.readOp Artifact.openingCode pc with
    | none => false
    | some op => HonestRegionBlocks.callable a op && HonestFlow.direct op &&
      (writes a op).all (HonestPhysical.misses flags) &&
      (HonestAbstract.destinations pc (exactFile a.regs) op).all (fun target =>
        stops target || check k target (advance a op))

theorem frame (clock : Nat) (pc : Word) (a : Abstract) (cert : check clock pc a=true)
    (s t : MachineState) (coins : Bool) (atPc : s.pc=pc) (meaning : Models s a) (path : Path coins s t) :
    ∀ q, Contains flags q → t.getByte q=s.getByte q := by
  induction clock generalizing pc a s with
  | zero => cases cert
  | succ k ih =>
    cases opAt : HonestBlocks.readOp Artifact.openingCode pc with
    | none => simp [check,opAt] at cert
    | some op =>
      simp only [check,opAt,Bool.and_eq_true] at cert
      obtain ⟨⟨⟨call,dir⟩,write⟩,edges⟩ := cert
      have pub : op=.base .ECALL → s.getReg .x5=0 := by
        rintro rfl
        simp only [HonestRegionBlocks.callable,isQuery,Bool.not_true,Bool.false_or,beq_iff_eq] at call
        exact singleton_ok (meaning.1 _) call
      have read := HonestBlocks.fetch_op Artifact.openingCode (Artifact.submission.image .opening)
        (Eq.refl (ArtifactEncoding.decode 32 _)) (by decide) s op (atPc ▸ opAt)
      cases path with
      | hit run cont _ => exact HonestPhysical.same_bytes _ s coins a op meaning read pub _ run cont flags write
      | @more _ _ out run cont inside tail =>
        obtain ⟨target,next⟩ := one _ s coins a op meaning read dir pub out run cont
        rw [atPc] at target
        have edge := List.all_eq_true.mp edges _ target
        simp only [inside,Bool.false_or] at edge
        intro q present
        exact (ih _ _ edge _ rfl next tail q present).trans
          (HonestPhysical.same_bytes _ s coins a op meaning read pub out run cont flags write q present)

private theorem table (idx fee : Nat) (hit : (idx,fee)∈HonestCapFrame.prices) (plain : idx≠1470) :
    check fee (addr idx) ((⟨needed idx,[]⟩ : Shape).model context)=true := by
  simp only [HonestCapFrame.prices,List.mem_cons,List.not_mem_nil,or_false] at hit
  rcases hit with h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> cases h <;> first | contradiction | decide +kernel

theorem outsideScan (v : Node) (s t : MachineState) (coins : Bool) (known : Matches v s)
    (ext : HonestCapInvariant.Extra v s) (ok : legal v) (live : v.phase≠.returned)
    (other : pc v.phase≠1470) (path : Path coins s t) : ∀ q, Contains flags q → t.getByte q=s.getByte q := by
  have someRegs := HonestCapInvariant.needing ok live known ext
  have holds : Holds context ⟨needed (pc v.phase),[]⟩ s := ⟨someRegs,(by intro q x h; cases h),ext.frozen⟩
  exact frame _ _ _ (table _ _ (registered _ live) other) _ _ _ known.atPc (models_shape holds) path

def suffixFacts : RegFacts := [(.x20,⟨0,256⟩),(.x9,constant HonestCapTables.scratch)]
def emptyContext : Context := ⟨[],fun _ => any,[]⟩

theorem afterStore (s t : MachineState) (coins : Bool) (atPc : s.pc=addr 1475)
    (counter : (s.getReg .x20).toNat≤256) (scratch : s.getReg .x9=HonestCapTables.w HonestCapTables.scratch)
    (path : Path coins s t) : ∀ q, Contains flags q → t.getByte q=s.getByte q := by
  have holds : Holds emptyContext ⟨suffixFacts,[]⟩ s := by
    refine ⟨?_,(by intro _ _ h; cases h),(by intro _ h; cases h)⟩
    intro r v h
    simp only [suffixFacts,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with h|h <;> cases h
    · exact ⟨Nat.zero_le _,counter⟩
    · rw [scratch]; exact precise _
  exact frame 15 _ _ (by decide +kernel) _ _ _ atPc (models_shape holds) path

end CommitGolfCandidate.Reconstruction.HonestCapSpan
