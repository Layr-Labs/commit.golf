import CommitGolfCandidate.LateOpenPath

namespace CommitGolfCandidate.Late.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def recordSize (d : Nat) := 24+32*d
def recordAddr (d r : Nat) := proofBase+recordSize d*r

theorem record_aligned (d r : Nat) : recordAddr d r%8=0 := by
  simp [recordAddr,recordSize,proofBase,Nat.add_mod,Nat.mul_mod]

theorem record_fits (d r : Nat) (depth : d≤LOG_LENGTH) (small : r≤LENGTH) :
    recordAddr d r + recordSize d ≤ MEMORY_BYTES := by
  change d ≤ 24 at depth;change r≤16777216 at small
  have mul := Nat.mul_le_mul (show recordSize d≤792 by unfold recordSize;omega) small
  unfold recordAddr proofBase MEMORY_BYTES;unfold recordSize at *;omega

theorem word_zero (x : Word) : x + (0 : Word) = x := BitVec.add_zero x

def record_prep (s : MachineState) :=
  Part.pathStart.after (copyWords (Part.saltSource.after s) 3)

structure Prepared (s : MachineState) (i : Index) (k d r : Nat) (salt : Salt) : Prop where
  run : Runs s (record_prep s) 19 19
  pc : (record_prep s).pc=pcAt 38
  anchor : Anchor (record_prep s) k d r
  path : PathFrame (record_prep s) i d 0 (recordAddr d r+24)
  bytes : Written s (record_prep s) (recordAddr d r) (bytes (n:=24) salt)

theorem prepare_record (s : MachineState) (tree : Levels) (salts : SaltTape) (xs : List Index)
    (d r : Nat) (pc : s.pc=pcAt 19) (anchor : Anchor s xs.length d r) (dest : s.getReg .x25=W (recordAddr d r))
    (present : r<xs.length) (depth : d≤LOG_LENGTH) (size : xs.length≤LENGTH) (src : Sources s xs tree salts) :
    Prepared s (ix xs r) xs.length d r (salts (ix xs r)) := by
  let i := ix xs r
  let a := Part.saltSource.after s
  let c := copyWords a 3
  let dst := recordAddr d r
  have kb : xs.length≤16777216 := size
  have loadAddr : accessValid (s.getReg .x24) 8=true := by
    rw [anchor.cursor];apply access_at <;> simp only [indexBase,MEMORY_BYTES] <;> omega
  have first := block_result .saltSource s pc (by
    intro e he
    change e ∈ [_] at he
    rcases List.mem_singleton.mp he with rfl
    change accessValid (s.getReg .x24+0) 8=true
    rw [word_zero];exact loadAddr)
  have loaded : s.getMem (s.getReg .x24) = W i.val := by rw [anchor.cursor];exact src.index _ present
  have id : a.getReg .x20=W i.val := by
    have eq := first.regs .x20
    change _ = s.getMem (s.getReg .x24+0) at eq
    exact eq.trans ((congrArg s.getMem (word_zero _)).trans loaded)
  have ptr : a.getReg .x23 = W (saltAddress i) := by
    have eq := first.regs .x23
    change _ = s.getReg .x18 + (((s.getMem (s.getReg .x24+0) <<< 1) + s.getMem (s.getReg .x24+0)) <<< 5) +
      (((s.getMem (s.getReg .x24+0) &&& 1) + 18446744073709551615) &&& 72) at eq
    rw [word_zero,loaded,anchor.row] at eq
    exact eq.trans (salt_ptr i)
  have dp := (first.keep .x25 rfl).trans dest
  have sb := (salt_ok i).2.1
  have fits := record_fits d r depth (by omega)
  have high : proofBase ≤ dst := by dsimp only [dst,recordAddr];omega
  have sa : AddrOK (saltAddress i) (8*3) := ⟨(salt_ok i).2.2,by unfold indexBase at sb;unfold MEMORY_BYTES;omega⟩
  have da : AddrOK dst (8*3) := ⟨record_aligned _ _,by change dst+(24+32*d)≤_ at fits;omega⟩
  have sep : saltAddress i+8*3 ≤ dst := by unfold indexBase at sb;unfold proofBase at high;omega
  have copyRun := copy_run .salt a first.pc _ _ ptr dp 3 (by decide) sa da
  have write := copied_bytes (copied a _ _ ptr dp 3 (by decide) sa da sep) sa.1 da.1 (salts i)
    ((read_congr_mem _ _ _ _ first.mem).trans (src.salts i))
  have cp : c.pc=pcAt 34 := by change (copyWords a 3).pc=_;rw [copy_pc,first.pc];rfl
  have after := no_load .pathStart c cp rfl
  have keep := (first.keeps (by decide)).then (copy_anchors a 3)
  have common := anchor.transport keep
  have ci := (copy_keeps a 3 .x20 (by decide)).trans id
  have cd := (copy_keeps a 3 .x25 (by decide)).trans dp
  refine ⟨(first.runs.trans copyRun).trans after.runs, after.pc, common.transport (after.keeps (by decide)),?_,
    write.congr_mem first.mem.symm after.mem⟩
  constructor
  · have eq := after.regs .x25
    change _ = c.getReg .x25+24 at eq
    rw [cd] at eq
    exact eq.trans (BitVec.ofNat_add dst 24).symm
  · rw [show indexAbove (ix xs r) 0=i.val by simp [indexAbove,i]]
    change (Part.pathStart.after c).getReg .x20 = W i.val
    exact (after.keep .x20 rfl).trans ci
  · have eq := after.regs .x22; change _ = c.getReg .x9+0 at eq
    rw [word_zero,common.base] at eq
    exact eq
  · have eq := after.regs .x17;change _=c.getReg .x29+0 at eq
    rw [word_zero,common.span] at eq;exact eq
  · have eq := after.regs .x28;change _=c.getReg .x30+0 at eq
    rw [word_zero,common.depth] at eq;exact eq

end CommitGolfCandidate.Late.Open
