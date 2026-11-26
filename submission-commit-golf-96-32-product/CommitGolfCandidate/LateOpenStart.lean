import CommitGolfCandidate.LateOpenRecord
import CommitGolfCandidate.OPBatchRecord

namespace CommitGolfCandidate.Late.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def depth (k : Nat) := if k=128 then 16 else 24

structure ABI (s : MachineState) (k : Nat) : Prop where
  pc : s.pc=pcAt 0
  td : s.getReg .x12=W tdBase
  idx : s.getReg .x13=W indexBase
  proof : s.getReg .x15=W proofBase
  count : s.getReg .x16=W k

theorem opening_abi (td : Trapdoor) (p : Positions) : ABI (initial td p) p.card :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩

private structure Seed (s : MachineState) (k : Nat) : Prop where
  base : s.getReg .x9=W tdBase
  count : s.getReg .x16=W k
  row : s.getReg .x18=W rowBase
  span : s.getReg .x29=W (stride 0)
  cursor : s.getReg .x24=W indexBase
  left : s.getReg .x27=W k
  dest : s.getReg .x25=W proofBase

private def seedRegs : List Reg := [.x9,.x16,.x18,.x29,.x24,.x27,.x25]
private theorem Seed.trans {s t : MachineState} {k} (a : Seed s k)
    (keep : ∀r∈seedRegs,t.getReg r=s.getReg r) : Seed t k :=
  ⟨(keep _ (by decide)).trans a.base,(keep _ (by decide)).trans a.count,(keep _ (by decide)).trans a.row,
    (keep _ (by decide)).trans a.span,(keep _ (by decide)).trans a.cursor,(keep _ (by decide)).trans a.left,
    (keep _ (by decide)).trans a.dest⟩

private theorem init_seed (s : MachineState) (k : Nat) (f : ABI s k) (b : BlockResult .init s) : Seed (Part.init.after s) k := by
  have mv (r : Reg) (fromReg : Reg) (eq : Part.init.equation r=.op .add (.reg fromReg) (.lit 0)) :
      (Part.init.after s).getReg r=s.getReg fromReg := by
    rw [b.regs,eq];exact word_zero _
  exact ⟨(mv _ _ rfl).trans f.td,(b.keep _ rfl).trans f.count,b.regs .x18,b.regs .x29,
    (mv _ _ rfl).trans f.idx,(mv _ _ rfl).trans f.count,(mv _ _ rfl).trans f.proof⟩

theorem eq_test (a b : Nat) (ha : a<2^64) (hb : b<2^64) :
    (W a == W b) = decide (a=b) := by
  by_cases eq : a=b
  · subst b;simp
  · have ne : W a ≠ W b := by
      intro e;have v:=congrArg BitVec.toNat e
      simp only [W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] at v
      exact eq v
    simp [ne,eq]

def dispatch (s : MachineState) := Test.empty.after (Part.init.after s)
def chooseDepth (s : MachineState) := Test.depth.after (Part.depth.after (dispatch s))
def begun (s : MachineState) (_k : Nat) := chooseDepth s
/-- The batch path: word 18 jumps to the appended batch code at word 140. -/
def jumped (s : MachineState) := (chooseDepth s).setPC (pcAt 140)

theorem start_empty (s : MachineState) (f : ABI s 0) :
    Runs s (dispatch s) 15 15 ∧ (dispatch s).pc=pcAt 60 ∧ (dispatch s).getReg .x16=0 ∧
      (dispatch s).mem=s.mem := by
  have b := no_load .init s f.pc rfl
  have rs := init_seed s 0 f b
  have e : Test.empty.taken (Part.init.after s) = true := by
    change ((Part.init.after s).getReg .x27 == (0 : Word))=true;rw [rs.left];rfl
  exact ⟨b.runs.trans (test_run .empty _ b.pc),by change pcAt (if Test.empty.taken _ then _ else _)=_;rw [e];rfl,
    MachineState.getReg_setPC.trans rs.count,b.mem⟩

private theorem seed_after {b : Part} {s : MachineState} {k} (r : BlockResult b s) (seed : Seed s k)
    (pres : seedRegs.all (fun i => decide (b.equation i=original i))=true) : Seed (b.after s) k :=
  seed.trans (fun i hi => r.keep i (of_decide_eq_true (List.all_eq_true.mp pres i hi)))

private theorem seed_branch (b : Test) (s : MachineState) (k : Nat) (f : Seed s k) : Seed (b.after s) k :=
  f.trans (fun _ _ => MachineState.getReg_setPC)

private theorem frame_of_seed (s : MachineState) (k d : Nat) (f : Seed s k) (hd : s.getReg .x30=W d) :
    RecordFrame s k d 0 :=
  ⟨⟨⟨f.base,f.count,f.row,f.span,hd⟩,by simpa only [Nat.mul_zero,Nat.add_zero] using f.cursor,
    by simpa only [Nat.sub_zero] using f.left⟩,by simpa only [recordAddr,Nat.mul_zero,Nat.add_zero] using f.dest⟩

theorem start_records (s : MachineState) (k : Nat) (nonempty : 0<k) (small : k≤LENGTH) (f : ABI s k)
    (normal : k≠128) :
    Runs s (begun s k) 18 18 ∧
    (begun s k).pc=pcAt 19 ∧ RecordFrame (begun s k) k (depth k) 0 ∧ (begun s k).mem=s.mem := by
  have kb : k≤16777216 := small
  let a := Part.init.after s
  let b := dispatch s
  let c := Part.depth.after b
  let t := chooseDepth s
  have ba := no_load .init s f.pc rfl
  have sa := init_seed _ _ f ba
  have neq : Test.empty.taken a=false := by
    change (a.getReg .x27 == W 0)=false
    rw [sa.left,eq_test _ _ (by omega) (by decide)]
    simp [show k≠0 by omega]
  have pb : b.pc=pcAt 15 := by change pcAt (if Test.empty.taken a then _ else _)=_;rw [neq];rfl
  have bc := no_load .depth b pb rfl
  have sc := seed_after bc (seed_branch .empty a k sa) (by decide)
  have curr : c.getReg .x6=W 128 := bc.regs .x6
  have selected : Test.depth.taken c=decide (k≠128) := by
    change (c.getReg .x27 != c.getReg .x6)=_
    rw [sc.left,curr]
    change (!(W k == W 128))=_
    rw [eq_test _ _ (by omega) (by decide)];by_cases eq:k=128 <;> simp [eq]
  have run := ((ba.runs.trans (test_run .empty _ ba.pc)).trans bc.runs).trans (test_run .depth c bc.pc)
  have keep := seed_branch .depth c k sc
  have mem : t.mem=s.mem := bc.mem.trans ba.mem
  have pc : t.pc=pcAt 19 := by change pcAt (if Test.depth.taken c then _ else _)=_;rw [selected];simp [normal,Test.target]
  simp only [begun,depth,if_neg normal]
  exact ⟨run,pc,frame_of_seed t k 24 keep (MachineState.getReg_setPC.trans (bc.regs .x30)),mem⟩

theorem start_batch (s : MachineState) (f : ABI s 128) :
    Runs s (jumped s) 19 19 ∧ (jumped s).pc=pcAt 140 ∧ BAnchor (jumped s) 0 ∧ (jumped s).mem=s.mem := by
  let a := Part.init.after s
  let b := dispatch s
  let c := Part.depth.after b
  let t := chooseDepth s
  have ba := no_load .init s f.pc rfl
  have sa := init_seed _ _ f ba
  have neq : Test.empty.taken a=false := by
    change (a.getReg .x27 == W 0)=false
    rw [sa.left,eq_test _ _ (by decide) (by decide)]
    decide
  have pb : b.pc=pcAt 15 := by change pcAt (if Test.empty.taken a then _ else _)=_;rw [neq];rfl
  have bc := no_load .depth b pb rfl
  have sc := seed_after bc (seed_branch .empty a 128 sa) (by decide)
  have curr : c.getReg .x6=W 128 := bc.regs .x6
  have selected : Test.depth.taken c=false := by
    change (c.getReg .x27 != c.getReg .x6)=_
    rw [sc.left,curr]; decide
  have run := ((ba.runs.trans (test_run .empty _ ba.pc)).trans bc.runs).trans (test_run .depth c bc.pc)
  have keep := seed_branch .depth c 128 sc
  have mem : t.mem=s.mem := bc.mem.trans ba.mem
  have pc : t.pc=pcAt 18 := by change pcAt (if Test.depth.taken c then _ else _)=_; rw [selected];rfl
  have jr := jump_run t pc
  have kj := seed_branch .depth c 128 sc
  refine ⟨run.trans jr,rfl,?_,mem⟩
  have g (r : Reg) : (jumped s).getReg r = t.getReg r := MachineState.getReg_setPC
  exact ⟨(g _).trans keep.base,(g _).trans keep.count,(g _).trans keep.row,(g _).trans keep.span,
    by simpa only [Nat.mul_zero,Nat.add_zero] using (g _).trans keep.cursor,
    by simpa only [Nat.sub_zero] using (g _).trans keep.left,
    by simpa only [bRecAddr,Nat.mul_zero,Nat.add_zero] using (g _).trans keep.dest⟩

end CommitGolfCandidate.Late.Open
