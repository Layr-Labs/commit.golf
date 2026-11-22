import CommitGolfCandidate.Layout2Records

/-! Layout 2 V2a opener: the whole record loop. From the state at word 4096 (`L2Start`, the end of the pass), the
records `0 ..< k` by induction (header, phase body, tail), then the exit stub of phase `(k+3) % 4` with the
6/4/2/0-byte flush, to the cap preparation at word 1097 (`L2Done`). -/
namespace TwoPermutationPrototype.GroupedOpening.Layout2
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate
open CommitGolfCandidate.Layout2Phase (stride phaseBase writerByte writerCarry recordSource streamRun)
open CommitGolfCandidate.Layout2Phase2 (bodyWord bodyLen tailWord PhaseFacts PhaseEntry)
open Opening (sortedIndex RecordMarks groupsBefore machineMarks)
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000

theorem runs_cost {a b : MachineState} {c c' : Nat} (run : RunsOpeningBlock a b c) (e : c=c') :
    RunsOpeningBlock a b c' := e ▸ run

theorem runs_zero (a : MachineState) : RunsOpeningBlock a a 0 := by
  intro fuel coins
  simp [Execution.charge]

theorem loop_mono (j n : Nat) : loopCost j ≤ loopCost (j+n) := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih => rw [← Nat.add_assoc, loopCost]; omega

/-- Records `j ..< k` from the boundary of record `j` (its header, or the exit stub when `j = k`). -/
theorem records_from (phases : ∀ p<4, PhaseFacts openingImage p) (s : Submission) (layout : OpeningLayout s)
    (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions) (pass : MachineState) :
    ∀ (n j : Nat) (st : MachineState), j+n=positions.card →
      L2Frame s trapdoor positions pass st j →
      st.pc=address (if j=positions.card then exitWord ((j+3)%4) else hdrWord (j%4)) →
      st.getReg .x21=BitVec.ofNat 64 (destOf j) →
      (j%4 ≠ 0 → st.getReg .x11=carryAt (s.initialState .opening (trapdoor, positions)) positions j) →
      ∃ u, RunsOpeningBlock st u (loopCost (j+n)-loopCost j) ∧ L2Frame s trapdoor positions pass u positions.card ∧
        u.pc=address (exitWord ((positions.card+3)%4)) ∧ u.getReg .x21=BitVec.ofNat 64 (destOf positions.card) ∧
        (positions.card%4 ≠ 0 →
          u.getReg .x11=carryAt (s.initialState .opening (trapdoor, positions)) positions positions.card) := by
  intro n
  induction n with
  | zero =>
    intro j st total fr pc dest carry
    have e : j=positions.card := by omega
    subst e
    refine ⟨st, runs_cost (runs_zero st) (by simp), fr, ?_, dest, carry⟩
    rw [pc, if_pos rfl]
  | succ n ih =>
    intro j st total fr pc dest carry
    have hj : j<positions.card := by omega
    rw [if_neg (by omega)] at pc
    obtain ⟨u, r1, fu, pu, du, cu⟩ := record_step phases s layout trapdoor positions pass st j hj fr pc dest carry
    rw [show j%4=(j+1+3)%4 by omega] at pu
    obtain ⟨v, r2, fv, pv, dv, cv⟩ := ih (j+1) u (by omega) fu pu du cu
    refine ⟨v, runs_cost (r1.next r2) ?_, fv, pv, dv, cv⟩
    have m := loop_mono (j+1) n
    have step : loopCost (j+1)=loopCost j+bodyLen (j%4)+8 := rfl
    rw [show j+1+n=j+(n+1) by omega] at m ⊢
    omega

/-- The state at the cap preparation (word 1097) after the record loop. -/
structure L2Done (s : Submission) (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions)
    (pass state : MachineState) : Prop where
  pc : state.pc=address 1097
  heap : state.getReg .x9=BitVec.ofNat 64 trapdoorBase
  index : state.getReg .x8=BitVec.ofNat 64 (indicesBase+8*positions.card)
  nonce : state.getReg .x22=BitVec.ofNat 64 nonceBase
  dest : state.getReg .x21=BitVec.ofNat 64 (proofBase+534*positions.card)
  leaves : state.getReg .x19=BitVec.ofNat 64 4194304
  slots : state.getReg .x24=BitVec.ofNat 64 groupSlots
  endIndex : state.getReg .x17=BitVec.ofNat 64 (indicesBase+8*positions.card)
  marks : state.getReg .x26=BitVec.ofNat 64 Opening.markBase
  one : state.getReg .x23=1#64
  capHeap : state.getReg .x25=BitVec.ofNat 64 trapdoorBase
  capLeaves : state.getReg .x27=256#64
  proofBegin : state.getReg .x20=BitVec.ofNat 64 proofBase
  input : SameOpeningInput (s.initialState .opening (trapdoor, positions)) state
  marked : RecordMarks positions state positions.card
  bytes : L2Bytes (s.initialState .opening (trapdoor, positions)) pass positions state positions.card
  /-- The pending stream bytes of the last phase (none after a phase-3 record). -/
  flush : ∀ b<flushLen ((positions.card+3)%4), state.getByte (BitVec.ofNat 64 (destOf positions.card+b))=
    (carryAt (s.initialState .opening (trapdoor, positions)) positions positions.card).extractLsb' (8*b) 8

private theorem ofNat_ne (a b : Nat) (h : a<b) (hb : b<2^64) : BitVec.ofNat 64 a ≠ BitVec.ofNat 64 b := by
  intro e
  have := congrArg BitVec.toNat e
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hb] at this
  omega

/-- The record loop: `l2RecordsCost k` cycles from word 4096 to word 1097. -/
theorem records_run (phases : ∀ p<4, PhaseFacts openingImage p) (s : Submission) (layout : OpeningLayout s)
    (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions) (begin : MachineState)
    (positive : 0<positions.card) (start : L2Start s trapdoor positions begin) :
    ∃ lower, RunsOpeningBlock begin lower (l2RecordsCost positions.card) ∧ L2Done s trapdoor positions begin lower := by
  have card := card_bound positions
  obtain ⟨v, r2, fv, pv, dv, cv⟩ := records_from phases s layout trapdoor positions begin positions.card 0 begin
    (by omega) start.frame (by rw [if_neg (by omega)]; exact start.pc) (by rw [start.dest]; rfl)
    (fun h => absurd rfl h)
  have hp : (positions.card+3)%4<4 := Nat.mod_lt _ (by decide)
  have bound := dest_bound positions.card
  have pb : proofBase=13824430176 := by decide
  have mem : MEMORY_BYTES=68719476736 := rfl
  obtain ⟨r3, pc3, x21, flushed, bytes3, mem3, regs3⟩ := exit_step ((positions.card+3)%4) hp v (destOf positions.card) (v.getReg .x11) pv dv
    (dest_aligned positions.card) (by omega) rfl
  let lower := walkRows v (exitRows ((positions.card+3)%4))
  have kr (r : Reg) (a : r ≠ .x21) (b : r ≠ .x11) : lower.getReg r=v.getReg r := regs3 r a b
  have far (x : Nat) (h : x<proofBase) : lower.getMem (BitVec.ofNat 64 x)=v.getMem (BitVec.ofNat 64 x) :=
    mem3 _ (ofNat_ne _ _ (by omega) (by omega))
  refine ⟨lower, runs_cost (r2.next r3) ?_, ⟨pc3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩⟩
  · rw [show 0+positions.card=positions.card by omega]
    unfold l2RecordsCost
    simp [loopCost]
  · exact (kr .x9 (by decide) (by decide)).trans fv.heap
  · exact (kr .x8 (by decide) (by decide)).trans fv.index
  · exact (kr .x22 (by decide) (by decide)).trans fv.nonce
  · rw [x21, dest_flush positions.card positive]
  · exact (kr .x19 (by decide) (by decide)).trans fv.leaves
  · exact (kr .x24 (by decide) (by decide)).trans fv.slots
  · exact (kr .x17 (by decide) (by decide)).trans fv.endIndex
  · exact (kr .x26 (by decide) (by decide)).trans fv.marks
  · exact (kr .x23 (by decide) (by decide)).trans fv.one
  · exact (kr .x25 (by decide) (by decide)).trans fv.capHeap
  · exact (kr .x27 (by decide) (by decide)).trans fv.capLeaves
  · exact (kr .x20 (by decide) (by decide)).trans fv.proofBegin
  · intro a lo hi al
    exact (far a hi).trans (fv.input a lo hi al)
  · intro node bounded
    have tb : trapdoorBase ≤ proofBase := by decide
    have mk : Opening.markBase+8*node<trapdoorBase := by
      have : trapdoorBase=4294971424 := by decide
      unfold Opening.markBase; omega
    unfold machineMarks
    rw [far _ (by omega)]
    exact fv.marked node bounded
  · intro j hj b hb
    have mono := dest_mono j positions.card hj
    rw [bytes3 _ (by omega) (Or.inl (by omega))]
    exact fv.bytes j hj b hb
  · intro b hb
    rw [flushed b hb]
    by_cases z : positions.card%4=0
    · exfalso
      have : (positions.card+3)%4=3 := by omega
      rw [this] at hb
      unfold flushLen at hb
      simp at hb
    · rw [cv z]

end TwoPermutationPrototype.GroupedOpening.Layout2
