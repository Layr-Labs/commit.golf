import CommitGolfCandidate.ChainedCheckerControllerFetch
import CommitGolfCandidate.ChainedHashState

/-! Opaque states and projected ABI frames for both checking hash-call sites. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
attribute [local irreducible] firstPackPrefix writeBits

inductive CheckerHashSite where | lower | cap

def CheckerHashSite.index : CheckerHashSite → Nat | .lower => 2817 | .cap => 2915
def CheckerHashSite.packJump : CheckerHashSite → BitVec 21 | .lower => 568 | .cap => 176
def CheckerHashSite.nextJump : CheckerHashSite → BitVec 21 | .lower => 684 | .cap => 292
def CheckerHashSite.base (site : CheckerHashSite) : Word := BitVec.ofNat 64 (4096+4*site.index)
def CheckerHashSite.resume (site : CheckerHashSite) : Word := site.base+12
def checkerPackBase : Word := 4096+4*2959
def checkerContinuationBase : Word := 4096+4*2990

theorem checker_hash_site_at (site : CheckerHashSite) :
    OpsAt chainedCheckerImage site.base [.JAL .x1 site.packJump,.ECALL,.JAL .x1 site.nextJump] := by
  cases site
  · exact chained_checker_slice_at 2817 3 _ (by rw [chained_checker_ops_length]; decide) (by decide +kernel)
  · exact chained_checker_slice_at 2915 3 _ (by rw [chained_checker_ops_length]; decide) (by decide +kernel)

@[irreducible] def checkerHashPackStart (site : CheckerHashSite) (s : MachineState) : MachineState :=
  execInstrBr s (.JAL .x1 site.packJump)

theorem checker_hash_pack_start_eq (site : CheckerHashSite) (s : MachineState) :
    checkerHashPackStart site s=execInstrBr s (.JAL .x1 site.packJump) := by rw [checkerHashPackStart]

@[irreducible] def checkerHashPacked (site : CheckerHashSite) (s : MachineState) : MachineState :=
  firstPackPrefix (checkerHashPackStart site s) 31

theorem checker_hash_packed_eq (site : CheckerHashSite) (s : MachineState) :
    checkerHashPacked site s=firstPackPrefix (checkerHashPackStart site s) 31 := by rw [checkerHashPacked]

@[irreducible] def checkerHashContinued (site : CheckerHashSite) (s : MachineState) (answer : Output) : MachineState :=
  execInstrBr (writeBits (checkerHashPacked site s) 256 answer) (.JAL .x1 site.nextJump)

theorem checker_hash_continued_eq (site : CheckerHashSite) (s : MachineState) (answer : Output) :
    checkerHashContinued site s answer=
      execInstrBr (writeBits (checkerHashPacked site s) 256 answer) (.JAL .x1 site.nextJump) := by
  rw [checkerHashContinued]

private theorem jal_register (s : MachineState) (offset : BitVec 21) (query : Reg) (kept : query ≠ .x1) :
    (execInstrBr s (.JAL .x1 offset)).getReg query=s.getReg query := by
  cases query <;> first | exact (kept rfl).elim | rfl

theorem checker_hash_pack_start_register (site : CheckerHashSite) (s : MachineState) (query : Reg)
    (kept : query ≠ .x1) : (checkerHashPackStart site s).getReg query=s.getReg query := by
  rw [checker_hash_pack_start_eq,jal_register s site.packJump query kept]

theorem checker_hash_pack_start_memory (site : CheckerHashSite) (s : MachineState) (query : Word) :
    (checkerHashPackStart site s).getMem query=s.getMem query := by
  rw [checker_hash_pack_start_eq]
  rfl

theorem checker_hash_pack_start_link (site : CheckerHashSite) (s : MachineState) :
    (checkerHashPackStart site s).getReg .x1=s.pc+4 := by
  rw [checker_hash_pack_start_eq]
  rfl

theorem checker_hash_pack_start_pc (site : CheckerHashSite) (s : MachineState) (pc : s.pc=site.base) :
    (checkerHashPackStart site s).pc=checkerPackBase := by
  rw [checker_hash_pack_start_eq]
  change s.pc+signExtend21 site.packJump=checkerPackBase
  rw [pc]
  cases site <;> decide +kernel

theorem checker_hash_packed_pc (site : CheckerHashSite) (s : MachineState) (pc : s.pc=site.base) :
    (checkerHashPacked site s).pc=site.base+4 := by
  rw [checker_hash_packed_eq,first_pack_return_pc,checker_hash_pack_start_link,pc]
  cases site <;> decide +kernel

theorem checker_hash_packed_register (site : CheckerHashSite) (s : MachineState) (query : Reg)
    (kept : query ∉ ([.x1,.x20,.x21,.x22,.x23,.x24,.x25,.x26,.x27,.x28,.x29] : List Reg)) :
    (checkerHashPacked site s).getReg query=s.getReg query := by
  rw [checker_hash_packed_eq,first_pack_register _ query (by simp_all),
    checker_hash_pack_start_register _ _ _ (by simp_all)]

theorem LoopArgs.checkerPackStart {s : MachineState} (site : CheckerHashSite) (args : LoopArgs s 256) :
    LoopArgs (checkerHashPackStart site s) 256 := by
  have frame := checker_hash_pack_start_register site s
  exact ⟨(frame .x10 (by decide)).trans args.source,(frame .x12 (by decide)).trans args.target,
    (frame .x5 (by decide)).trans args.selector,(frame .x11 (by decide)).trans args.size,
    (frame .x13 (by decide)).trans args.kind,args.aligned,args.inputValid,args.outputValid,args.access⟩

theorem LoopArgs.checkerPacked {s : MachineState} (site : CheckerHashSite) (args : LoopArgs s 256) :
    LoopArgs (checkerHashPacked site s) 256 := by
  have frame := checker_hash_packed_register site s
  exact ⟨(frame .x10 (by decide)).trans args.source,(frame .x12 (by decide)).trans args.target,
    (frame .x5 (by decide)).trans args.selector,(frame .x11 (by decide)).trans args.size,
    (frame .x13 (by decide)).trans args.kind,args.aligned,args.inputValid,args.outputValid,args.access⟩

theorem checker_hash_continued_register (site : CheckerHashSite) (s : MachineState) (answer : Output)
    (query : Reg) (kept : query ≠ .x1) :
    (checkerHashContinued site s answer).getReg query=(checkerHashPacked site s).getReg query := by
  rw [checker_hash_continued_eq,jal_register _ _ _ kept,writeBits_register]

theorem checker_write_pc (s : MachineState) (answer : Output) :
    (writeBits s 256 answer).pc=s.pc+4 := by
  rw [writeBits]
  rfl

theorem checker_hash_continued_pc (site : CheckerHashSite) (s : MachineState) (answer : Output)
    (pc : s.pc=site.base) : (checkerHashContinued site s answer).pc=checkerContinuationBase := by
  rw [checker_hash_continued_eq]
  change (writeBits (checkerHashPacked site s) 256 answer).pc+signExtend21 site.nextJump=checkerContinuationBase
  rw [checker_write_pc,checker_hash_packed_pc site s pc]
  cases site <;> decide +kernel

theorem checker_hash_continued_link (site : CheckerHashSite) (s : MachineState) (answer : Output)
    (pc : s.pc=site.base) : (checkerHashContinued site s answer).getReg .x1=site.resume := by
  rw [checker_hash_continued_eq]
  change (writeBits (checkerHashPacked site s) 256 answer).pc+4=site.resume
  rw [checker_write_pc,checker_hash_packed_pc site s pc]
  cases site <;> decide +kernel

theorem LoopArgs.checkerContinued {s : MachineState} (site : CheckerHashSite) (args : LoopArgs s 256)
    (answer : Output) : LoopArgs (checkerHashContinued site s answer) 256 := by
  have frame := checker_hash_continued_register site s answer
  have packed := args.checkerPacked site
  exact ⟨(frame .x10 (by decide)).trans packed.source,(frame .x12 (by decide)).trans packed.target,
    (frame .x5 (by decide)).trans packed.selector,(frame .x11 (by decide)).trans packed.size,
    (frame .x13 (by decide)).trans packed.kind,args.aligned,args.inputValid,args.outputValid,args.access⟩

end CommitGolfCandidate.Chained.Native
