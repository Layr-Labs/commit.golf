import CommitGolfCandidate.GroupedQImage
import CommitGolfCandidate.GroupedQMeaning

/-!
# The commit tail: level-21 loop, heap bands A and B, root parent, root copy and halt

`tail_run`: from the first tail word, 14,942,621 steps cost 44,302,742 cycles and 4,194,303 public
calls (2^21 level-21 parents, 2^21 - 2^17 band-A parents, 2^17 - 2 band-B parents, the root).
`tail_content`: the final state holds every heap node below `2^22` (level 21 full, levels 17..20 at
240 bits, levels 0..16 at 238 bits) and leaves everything from block `B_0` upwards untouched.
-/

namespace TwoPermutationPrototype.Grouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open TwoPermutationPrototype.Sampling (pad238)
open TwoPermutationPrototype.GroupedUpper (packedWideCommitImage l21StartPrefix heapStartPrefix l21Start_run heapStart_run)
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
attribute [local irreducible] execute l21Groups bandGroups rootPrefix GroupedUpper.l21StartPrefix
  GroupedUpper.heapStartPrefix midState t238Mask checkEvaluation

/-- The root parent and the root copy. -/
def rootTrace (b : MachineState) : OracleComp World MachineState := do
  let answer ← (liftM (World.query (.inr (.inl (parentInput b 1)))) : OracleComp World (BitVec 256))
  return rootPrefix (t238Mask b 1 answer) 10

def tailBody (s : MachineState) : OracleComp World MachineState := do
  let lv ← l21Groups GroupedUpper.l21Base GroupedUpper.l21Span GroupedUpper.l21Passes
    (l21StartPrefix s GroupedUpper.l21SetupLen)
  let a ← bandGroups recordKind GroupedUpper.bandABase GroupedUpper.bandASpan 131071 GroupedUpper.bandAPasses
    (heapStartPrefix lv 7)
  let b ← bandGroups t238Kind GroupedUpper.bandBBase GroupedUpper.bandBSpan 1 GroupedUpper.bandBPasses (midState a)
  rootTrace b

theorem tail_run (s : MachineState) (e : TailEntry s) (fuel : Nat) :
    execute packedWideCommitImage (14943221+fuel) s true =
      (do let t ← tailBody s; return ⟨.success,t,44303342,4194303⟩) := by
  have regs := l21_start_regs s e
  have startPC := l21_start_pc s e
  rw [show 14943221+fuel=7+(6291967+(7+(7864703+(1+(786521+(4+(11+fuel))))))) by omega,l21Start_run s e.pc,
    l21_loop_run _ _ regs startPC]
  unfold tailBody
  simp only [bind_assoc];apply bind_congr_of_forall_mem_support
  intro lv path
  obtain ⟨lregs,lpc⟩ := l21_loop_post _ regs startPC path
  have hregs := heap_start_regs lv lregs
  have hpc := heap_start_pc lv lpc
  rw [heapStart_run lv lpc,bandA_run _ _ hregs hpc]
  simp only [bind_assoc];apply bind_congr_of_forall_mem_support
  intro a pathA
  obtain ⟨aregs,apc⟩ := bandA_post _ hregs hpc pathA
  rw [mid_run a apc,bandB_run _ _ (mid_regs a aregs) (mid_pc a apc)]
  simp only [bind_assoc];apply bind_congr_of_forall_mem_support
  intro b pathB
  obtain ⟨bregs,bpc⟩ := bandB_post _ (mid_regs a aregs) (mid_pc a apc) pathB
  unfold rootTrace
  rw [root_parent_run b _ bregs bpc]
  simp only [bind_assoc];apply bind_congr_of_forall_mem_support
  intro answer _
  have out : (t238Mask b 1 answer).getReg .x8=4294971392 :=
    (mask_keeps_register _ _ _ _ (by decide)).trans
      ((band_keep _ _ _ _ _ _ .x8 (by decide) (by decide) (by decide) pathB).trans
        ((mid_x8 a).trans ((band_keep _ _ _ _ _ _ .x8 (by decide) (by decide) (by decide) pathA).trans
          ((heap_start_x8 lv).trans ((l21_groups_keeps_register _ _ _ _ .x8 (by decide) (by decide) path).trans
            ((l21_start_x8 s).trans e.out))))))
  have heap : (t238Mask b 1 answer).getReg .x9=4294971424 :=
    (mask_keeps_register _ _ _ _ (by decide)).trans bregs.heap
  rw [GroupedUpper.execute_packed_root _ (root_parent_pc b answer bpc) heap out]
  simp only [bind_assoc,pure_bind,Execution.charge]

/-- Cycles of the whole commit run (odd-quartet image, budget_q). -/
def commitCycles : Nat := 1368670236
/-- Public oracle calls of the whole commit run. -/
def commitCalls : Nat := 43470847

def packedOutput (o : Oracle) (leaves : MachineState) : Execution :=
  ⟨.success,(checkEvaluation o (tailBody leaves)).1,commitCycles,commitCalls⟩

private theorem output_eq (o : Oracle) (leaves : MachineState) :
    packedOutput o leaves=⟨.success,(checkEvaluation o (tailBody leaves)).1,commitCycles,commitCalls⟩ := rfl

private theorem state_of_output (s : MachineState) :
    (⟨.success,s,commitCycles,commitCalls⟩ : Execution).state=s := rfl

attribute [local irreducible] packedOutput

private theorem bind_fst (o : Oracle) {α β : Type} (comp : OracleComp World α) (cont : α → OracleComp World β) :
    (checkEvaluation o (comp >>= cont)).1=(checkEvaluation o (cont (checkEvaluation o comp).1)).1 := by
  rw [check_evaluation_bind]

theorem root_eval (o : Oracle) (b : MachineState) :
    (checkEvaluation o (rootTrace b)).1=rootPrefix (t238Mask b 1 (o.compression (parentInput b 1))) 10 := by
  unfold rootTrace
  rw [bind_fst,check_evaluation_pure]
  have evaluated : checkEvaluation o (liftM (World.query (.inr (.inl (parentInput b 1)))) : OracleComp World (BitVec 256)) =
      (o.compression (parentInput b 1),1) := CommitGolfCandidate.check_evaluation_public o _
  rw [evaluated]

theorem eval_tail (o : Oracle) (leaves : MachineState) :
    let lv := (checkEvaluation o (l21Groups GroupedUpper.l21Base GroupedUpper.l21Span GroupedUpper.l21Passes
      (l21StartPrefix leaves GroupedUpper.l21SetupLen))).1
    let a := (checkEvaluation o (bandGroups recordKind GroupedUpper.bandABase GroupedUpper.bandASpan 131071
      GroupedUpper.bandAPasses (heapStartPrefix lv 7))).1
    let b := (checkEvaluation o (bandGroups t238Kind GroupedUpper.bandBBase GroupedUpper.bandBSpan 1
      GroupedUpper.bandBPasses (midState a))).1
    (packedOutput o leaves).state=rootPrefix (t238Mask b 1 (o.compression (parentInput b 1))) 10 := by
  intro lv a b
  refine (congrArg Execution.state (output_eq o leaves)).trans ((state_of_output _).trans ?_)
  unfold tailBody
  simp only [bind_fst]
  exact root_eval o b

theorem tail_counted (o : Oracle) (s : MachineState) : RunPublic o (tailBody s) 4194303 := by
  unfold tailBody
  apply run_bind_public _ _ _ 2097152 2097151 (counted_l21_groups ..);intro lv
  apply run_bind_public _ _ _ 1966080 131071 (counted_band ..);intro a
  apply run_bind_public _ _ _ 131070 1 (counted_band ..);intro b
  unfold rootTrace
  exact run_bind_public _ _ _ 1 0 (run_query_public ..) (fun _ => run_pure_public ..)

private theorem tail_content_mem (s t : MachineState) (heap : Nat → BitVec 256) (before : Memory) (n : Nat)
    (same : t.mem=s.mem) (r : TailContent s heap before n) : TailContent t heap before n := by
  refine ⟨?_,?_⟩
  · intro j lo hi
    rw [nodeDigest,read_buffer_memory_congr _ s same]
    exact r.nodes j lo hi
  · intro w lo hi
    exact (show memoryView t w=memoryView s w by unfold memoryView MachineState.getMem; rw [same]).trans (r.high w lo hi)

/-- The heap and the untouched upper memory after the tail (before the root copy). -/
theorem tail_content (o : Oracle) (s : MachineState) (e : TailEntry s) (heap : Nat → BitVec 256)
    (level21 : ∀ U < 2097152, heap (2097152+U)=o.compression (heap (4194304+(2*U+1)) ++ heap (4194304+2*U)))
    (wide : ∀ n, 131072≤n → n<2097152 → heap n=projectReply (o.compression (heap (2*n+1) ++ heap (2*n))))
    (narrow : ∀ n, 0<n → n<131072 → heap n=pad238 (o.compression (heap (2*n+1) ++ heap (2*n))))
    (pairs : UnitPairs (memoryView s) heap) :
    let lv := (checkEvaluation o (l21Groups GroupedUpper.l21Base GroupedUpper.l21Span GroupedUpper.l21Passes
      (l21StartPrefix s GroupedUpper.l21SetupLen))).1
    let a := (checkEvaluation o (bandGroups recordKind GroupedUpper.bandABase GroupedUpper.bandASpan 131071
      GroupedUpper.bandAPasses (heapStartPrefix lv 7))).1
    let b := (checkEvaluation o (bandGroups t238Kind GroupedUpper.bandBBase GroupedUpper.bandBSpan 1
      GroupedUpper.bandBPasses (midState a))).1
    let root := t238Mask b 1 (o.compression (parentInput b 1))
    TailContent root heap (memoryView s) 0 ∧ root.getReg .x9=4294971424 ∧ root.getReg .x8=4294971392 := by
  intro lv a b root
  have regs := l21_start_regs s e
  have startPC := l21_start_pc s e
  have start : TailContent (l21StartPrefix s GroupedUpper.l21SetupLen) heap (memoryView s) (l21Node 2097152) :=
    tail_content_mem s _ heap (memoryView s) _ (l21_start_mem s)
      ⟨fun n lo hi => by unfold l21Node at lo; omega,fun _ _ _ => rfl⟩
  have l21 : TailContent lv heap (memoryView s) (l21Node 0) :=
    l21_groups_semantics o GroupedUpper.l21Base GroupedUpper.l21Span GroupedUpper.l21Passes
      (l21StartPrefix s GroupedUpper.l21SetupLen) heap (memoryView s) (by decide) level21 pairs start regs
  have lpath : lv ∈ support (l21Groups GroupedUpper.l21Base GroupedUpper.l21Span GroupedUpper.l21Passes
      (l21StartPrefix s GroupedUpper.l21SetupLen)) := check_evaluation_support o _
  obtain ⟨lregs,lpc⟩ := l21_loop_post _ regs startPC lpath
  have hregs := heap_start_regs lv lregs
  have hpc := heap_start_pc lv lpc
  have hstart : TailContent (heapStartPrefix lv 7) heap (memoryView s) 2097151 :=
    tail_content_mem lv _ heap (memoryView s) _ (heap_start_mem lv) l21
  have aContent : TailContent a heap (memoryView s) 131071 :=
    band_semantics recordKind o GroupedUpper.bandABase GroupedUpper.bandASpan 131071 GroupedUpper.bandAPasses
      (heapStartPrefix lv 7) heap (memoryView s) (by decide)
      (fun node lo hi => wide node (by omega) (by change node≤131071+16384*120 at hi; omega))
      hstart hregs.toParentRegs hregs.maskReg
  have apath : a ∈ support (bandGroups recordKind GroupedUpper.bandABase GroupedUpper.bandASpan 131071
      GroupedUpper.bandAPasses (heapStartPrefix lv 7)) := check_evaluation_support o _
  obtain ⟨aregs,apc⟩ := bandA_post _ hregs hpc apath
  have mregs := mid_regs _ aregs
  have mContent : TailContent (midState a) heap (memoryView s) 131071 :=
    tail_content_mem _ _ heap (memoryView s) _ (mid_mem _) aContent
  have bContent : TailContent b heap (memoryView s) 1 :=
    band_semantics t238Kind o GroupedUpper.bandBBase GroupedUpper.bandBSpan 1 GroupedUpper.bandBPasses
      (midState a) heap (memoryView s) (by decide)
      (fun node lo hi => narrow node (by omega) (by change node≤1+8738*15 at hi; omega))
      mContent mregs.toParentRegs mregs.maskReg
  have bpath : b ∈ support (bandGroups t238Kind GroupedUpper.bandBBase GroupedUpper.bandBSpan 1
      GroupedUpper.bandBPasses (midState a)) := check_evaluation_support o _
  obtain ⟨bregs,_⟩ := bandB_post _ mregs (mid_pc _ apc) bpath
  have rootContent : TailContent root heap (memoryView s) 0 :=
    tail_content_mem (t238Kind.after b 1 (o.compression (parentInput b 1))) root heap (memoryView s) 0
      (t238_after_mem b 1 (o.compression (parentInput b 1))).symm
      (kind_content_step t238Kind o b heap (memoryView s) 0 (by decide)
        (narrow 1 (by decide) (by decide)) bContent bregs.toParentRegs bregs.maskReg (by decide))
  refine ⟨rootContent,(mask_keeps_register _ _ _ _ (by decide)).trans bregs.heap,?_⟩
  exact (mask_keeps_register _ _ _ _ (by decide)).trans
    ((band_keep _ _ _ _ _ _ .x8 (by decide) (by decide) (by decide) bpath).trans
      ((mid_x8 _).trans ((band_keep _ _ _ _ _ _ .x8 (by decide) (by decide) (by decide) apath).trans
        ((heap_start_x8 lv).trans ((l21_groups_keeps_register _ _ _ _ .x8 (by decide) (by decide) lpath).trans
          ((l21_start_x8 s).trans e.out))))))

end TwoPermutationPrototype.Grouped
