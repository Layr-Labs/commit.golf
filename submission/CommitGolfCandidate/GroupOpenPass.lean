import CommitGolfCandidate.GroupOpenEffect
import CommitGolfCandidate.GroupOpenInitial
import CommitGolfCandidate.GroupOpenRecordRun
import CommitGolfCandidate.GroupOpenRecords

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open Opening (sortedIndex RecordMarks machineMarks groupsBefore)
open TwoPermutationPrototype.Grouped (rank)
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def pos (p : Positions) (j : Nat) : Index := ((p.sort (·≤·))[j]?).getD ⟨0,by decide⟩
theorem pos_present (p : Positions) (j : Nat) (hj : j<p.card) : pos p j=sortedIndex p j hj := by
  unfold pos sortedIndex;rw [List.getElem?_eq_getElem (by simpa using hj)];rfl

structure Base (s : MachineState) (p : Positions) : Prop where
  indices : s.getReg .x8=BitVec.ofNat 64 indicesBase
  heap : s.getReg .x9=BitVec.ofNat 64 trapdoorBase
  count : s.getReg .x18=BitVec.ofNat 64 p.card
  leaves : s.getReg .x19=4194304
  start : s.getReg .x20=BitVec.ofNat 64 proofBase
  dest : s.getReg .x21=BitVec.ofNat 64 proofBase
  mark : s.getReg .x23=1
  slots : s.getReg .x24=BitVec.ofNat 64 groupSlots
  cap : s.getReg .x25=BitVec.ofNat 64 trapdoorBase
  capLeaves : s.getReg .x27=256

def Preserved (u s : MachineState) :=
  ∀ w<2^33, (w<128 ∨ 153≤w) → (w<192 ∨ 217≤w) →
    (w<872415748 ∨ 905970180≤w) → memoryView s w=memoryView u w

def StoredKey (s : MachineState) (k : BitVec 192) :=
  ∀ j, 0<j → j<25 → memoryView s (128+j)=Grouped.keyBlock k j

def passPC (p : Positions) (j : Nat) := if j=p.card then address 15 else address 739

structure Ready (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (key : BitVec 192)
    (s : MachineState) (j : Nat) : Prop extends Registers s j (p.card-j), Base s p where
  pc : s.pc=passPC p j
  frame : Preserved (actual.initialState .opening (td,p)) s
  keyFrame : StoredKey s key

theorem input_of_ready (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (key : BitVec 192)
    (s : MachineState) (j : Nat) (r : Ready td p key s j) (hj : j<p.card) :
    Input s (pos p j) j (p.card-j) := by
  have card : p.card≤16777216 := by change p.card≤LENGTH;simpa [Index] using Finset.card_le_univ p
  have ea : indexAt j=wordAddress (905970180+j) := by unfold indexAt wordAddress;congr 1 <;> omega
  refine ⟨r.toRegisters,by simpa [passPC,Nat.ne_of_lt hj] using r.pc,?_,?_⟩
  · have same := r.frame (905970180+j) (by omega) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
    have orig := input_index actual actual_layout td p j hj
    rw [pos_present p j hj]
    exact (show s.getMem (indexAt j)=(actual.initialState .opening (td,p)).getMem (indexAt j) by
      simpa only [ea,memoryView] using same).trans orig
  · unfold indexAt;apply Opening.aligned_access
    · omega
    · change _≤2^36;omega

theorem next_ready (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (key : BitVec 192)
    (s : MachineState) (j : Nat) (r : Ready td p key s j) (hj : j<p.card) (y : BitVec 1600) :
    Ready td p key (finishOne s (pos p j) (p.card-j) y) (j+1) := by
  let i:=pos p j
  have ix : i.val<16777216:=i.isLt
  have card : p.card≤16777216:=by change p.card≤LENGTH;simpa [Index] using Finset.card_le_univ p
  have inp:=input_of_ready td p key s j r hj
  have ⟨reg,pc,_⟩:=finish_regs s i j _ (by omega) (by omega) inp y
  have keep (a : Reg) (safe : Saved a := by unfold Saved;decide) := finish_keep s i (p.card-j) y a safe
  have same := outside_writes s i j (p.card-j) (by omega) (by omega) inp y
  refine ⟨by simpa only [show p.card-j-1=p.card-(j+1) by omega] using reg,
    ⟨(keep .x8).trans r.indices,(keep .x9).trans r.heap,(keep .x18).trans r.count,
     (keep .x19).trans r.leaves,(keep .x20).trans r.start,(keep .x21).trans r.dest,(keep .x23).trans r.mark,
     (keep .x24).trans r.slots,(keep .x25).trans r.cap,(keep .x27).trans r.capLeaves⟩,?_,?_,?_⟩
  · rw [pc];unfold finalPC passPC;split <;> rename_i h <;> simp [show j+1=p.card ↔ p.card-j=1 by omega,h]
  · intro w fit one two three
    exact (same w fit ⟨by omega,two⟩ ⟨by omega,by omega⟩).trans (r.frame _ fit one two three)
  · intro k lo hi
    exact (same (128+k) (by omega) ⟨by omega,Or.inl (by omega)⟩ ⟨by omega,by omega⟩).trans (r.keyFrame _ lo hi)

def passTrace (p : Positions) : Nat → Nat → MachineState → OracleComp World MachineState
  | 0,_,s => pure s
  | n+1,j,s => do let t ← perTrace s (pos p j) (p.card-j);passTrace p n (j+1) t

def passSteps (p : Positions) : Nat → Nat → Nat
  | 0,_ => 0
  | n+1,j => perSteps (pos p j) (p.card-j)+passSteps p n (j+1)

theorem step_support (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (key : BitVec 192)
    (s t : MachineState) (j : Nat) (r : Ready td p key s j) (hj : j<p.card)
    (hit : t∈support (perTrace s (pos p j) (p.card-j))) : Ready td p key t (j+1) := by
  simp only [perTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at hit
  obtain ⟨y,_,rfl⟩:=hit;exact next_ready td p key s j r hj y

theorem pass_post (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (key : BitVec 192)
    (s t : MachineState) (n j : Nat) (r : Ready td p key s j) (bound : j+n≤p.card)
    (hit : t∈support (passTrace p n j s)) : Ready td p key t (j+n) := by
  induction n generalizing j s with
  | zero => simp only [passTrace,support_pure,Set.mem_singleton_iff] at hit;subst t;exact r
  | succ n ih =>
    rw [passTrace,mem_support_bind_iff] at hit;obtain ⟨u,one,rest⟩:=hit
    exact (show j+(n+1)=(j+1)+n by omega) ▸ ih _ _ (step_support _ _ _ _ _ _ r (by omega) one) (by omega) rest

theorem pass_run (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (key : BitVec 192)
    (s : MachineState) (n j fuel : Nat) (r : Ready td p key s j) (bound : j+n≤p.card) :
    execute openingImage (passSteps p n j+fuel) s true=(do
      let t ← passTrace p n j s;let z ← execute openingImage fuel t true
      return z.charge (passSteps p n j+10*n) n) := by
  induction n generalizing j s with
  | zero => simp [passSteps,passTrace,Execution.charge]
  | succ n ih =>
    have card : p.card≤16777216 := by change p.card≤LENGTH;simpa [Index] using Finset.card_le_univ p
    rw [passSteps,Nat.add_assoc,per_run s (pos p j) j _ _ (by omega) (by omega) (input_of_ready _ _ _ _ _ r (by omega))]
    simp only [passTrace,bind_assoc]
    apply bind_congr_of_forall_mem_support;intro u hit
    rw [ih u (j+1) (step_support _ _ _ _ _ _ r (by omega) hit) (by omega)]
    simp only [bind_assoc,pure_bind]
    apply bind_congr;intro t;apply bind_congr;intro z;apply congrArg (fun x : Execution => (pure x : OracleComp World Execution))
    cases z;simp [Execution.charge,passSteps,perCycles,Nat.mul_succ] <;> omega

theorem pass_steps_bound (p : Positions) (n j : Nat) (bound : j+n≤p.card) : passSteps p n j≤22*n+1 := by
  induction n generalizing j with
  | zero => simp [passSteps]
  | succ n ih =>
    rw [passSteps]
    have h:=ih (j+1) (by omega)
    unfold perSteps
    by_cases last : p.card-j=1
    · have empty : n=0 := by omega
      subst n;simp [last,passSteps];split <;> omega
    · simp only [if_neg last];split <;> omega

end TwoPermutationPrototype.GroupedOpening
