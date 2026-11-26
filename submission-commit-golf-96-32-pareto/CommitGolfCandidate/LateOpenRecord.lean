import CommitGolfCandidate.LateOpenRecordHead

namespace CommitGolfCandidate.Late.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def recordStep (s : MachineState) (d : Nat) :=
  Test.moreRecords.after (Part.recordNext.after (walk d (record_prep s)))

structure RecordFrame (s : MachineState) (k d r : Nat) extends Anchor s k d r : Prop where
  dest : s.getReg .x25=W (recordAddr d r)

structure RecordResult (s : MachineState) (tree : Levels) (salts : SaltTape) (xs : List Index) (d r : Nat) : Prop where
  runs : Runs s (recordStep s d) (22+19*d) (22+19*d)
  frame : RecordFrame (recordStep s d) xs.length d (r+1)
  pc : (recordStep s d).pc=pcAt (if r+1<xs.length then 19 else 60)
  data : Written s (recordStep s d) (recordAddr d r) (record tree salts d (ix xs r))

theorem full_record (s : MachineState) (tree : Levels) (salts : SaltTape) (xs : List Index) (d r : Nat)
    (pc : s.pc=pcAt 19) (fr : RecordFrame s xs.length d r) (present : r<xs.length)
    (pos : 0<d) (depth : d≤LOG_LENGTH) (size : xs.length≤LENGTH) (src : Sources s xs tree salts) :
    RecordResult s tree salts xs d r := by
  let i := ix xs r
  let a := record_prep s
  let b := walk d a
  let c := Part.recordNext.after b
  let dest := recordAddr d r
  have high : proofBase≤dest := by dsimp [dest,recordAddr];omega
  have al := record_aligned d r
  have fits := record_fits d r depth (by omega)
  change dest+(24+32*d)≤MEMORY_BYTES at fits
  have head := prepare_record s tree salts xs d r pc fr.toAnchor fr.dest present depth size src
  have slen : (bytes (n:=24) (salts i)).length=24 := by simp only [bytes,List.length_ofFn]
  have aSrc := src.after size dest _ head.bytes.outside high al (by change (bytes (n:=24) (salts i)).length%8=0;omega)
  have hpc : a.pc=pcAt (if 0<d then 38 else 57) := by rw [if_pos pos];exact head.pc
  have path := walk_path a tree salts xs i d 0 (dest+24) d (by omega) depth hpc head.path aSrc size
    (by omega) (by dsimp [dest] at *;omega) (by omega)
  have bpc : b.pc=pcAt 57 := by simpa only [Nat.zero_add,lt_self_iff_false,if_false] using path.pc
  have tail := no_load .recordNext b bpc rfl
  have prior : Anchor b xs.length d r := head.anchor.transport path.anchor
  have rb := test_run .moreRecords c tail.pc
  have idx := tail.regs .x24; change c.getReg .x24 = b.getReg .x24+8 at idx
  have rem := tail.regs .x27; change c.getReg .x27 = b.getReg .x27+18446744073709551615 at rem
  rw [prior.cursor] at idx
  rw [prior.left,W,decrement (xs.length-r) (by omega)] at rem
  have diff : xs.length-r-1=xs.length-(r+1) := by omega
  rw [diff] at rem
  have keep (reg : Reg) (law : Part.recordNext.equation reg=original reg) : (recordStep s d).getReg reg=b.getReg reg :=
    (show (Test.moreRecords.after c).getReg reg=c.getReg reg from MachineState.getReg_setPC).trans (tail.keep reg law)
  have taken : Test.moreRecords.taken c=decide (r+1<xs.length) := by
    change (c.getReg .x27 != 0)=_
    rw [rem,count_test (xs.length-(r+1)) (by change xs.length≤16777216 at size;omega)]
    by_cases yes : r+1<xs.length <;> simp [yes,show (xs.length-(r+1)≠0) ↔ r+1<xs.length by omega]
  refine ⟨?_,⟨⟨⟨(keep _ rfl).trans prior.base,(keep _ rfl).trans prior.count,(keep _ rfl).trans prior.row,
    (keep _ rfl).trans prior.span,(keep _ rfl).trans prior.depth⟩,?_,?_⟩,?_⟩,?_,?_⟩
  · have run := ((head.run.trans path.run).trans tail.runs).trans rb
    have e : 19+19*d+2+1=22+19*d := by omega
    exact e ▸ run
  · apply MachineState.getReg_setPC.trans (idx.trans _)
    exact (BitVec.ofNat_add _ 8).symm.trans (congrArg W (by omega))
  · exact MachineState.getReg_setPC.trans rem
  · apply (keep .x25 rfl).trans
    apply path.frame.ptr.trans
    apply congrArg W
    unfold recordAddr recordSize; dsimp only [dest]
    unfold recordAddr recordSize
    rw [Nat.mul_succ];omega
  · change pcAt (if Test.moreRecords.taken c then _ else _) = _
    rw [taken];by_cases e : r+1<xs.length <;> simp [e,Test.target,Test.start]
  · have a2 : Written a b (dest+(bytes (n:=24) (salts i)).length) (pathBytes tree i 0 d) := by
      rw [slen];simpa only [Nat.mul_zero,Nat.add_zero] using path.bytes
    have all := head.bytes.append a2 (by rw [slen];dsimp [dest] at *;omega)
      (by rw [path_len];omega) (by rw [slen];omega)
    rw [record_eq]
    exact all.congr_mem rfl tail.mem

end CommitGolfCandidate.Late.Open
