import CommitGolfCandidate.P4OpenPass

/-! P4 opener header (words 0-3, the displaced setup words 3-12 re-executed at 1451-1460, the prefix configuration at
1461-1468 and the key copy at 1469-1474): from the opening input to the prefix loop's `Ready` state at word 1475.
Ported from dadon's 2a19be00 `GroupOpenHeader{Spec,Parts,Core}` and `GroupOpenHeader`; 04680e02's setup is 13 words
(theirs 15), so 10 words are copied (theirs 12) and the header is 28 rows. -/

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open Opening (RecordMarks)
open PackedOpening (setupInstructions setupPrefix nonempty_count opening_first_boundary)
set_option maxRecDepth 22000
set_option maxHeartbeats 2000000

def layoutRows : List Row :=
  [(0,.ADDI .x20 .x15 0),(1,.ADDI .x21 .x15 0),(2,.BEQ .x16 .x0 2708),(3,.JAL .x0 5792),
   (1451,.ADDI .x8 .x13 0),(1452,.ADDI .x9 .x12 0),(1453,.ADDI .x18 .x16 0),(1454,.LUI .x19 4096),
   (1455,.LUI .x22 327680),(1456,.ADD .x22 .x9 .x22),(1457,.ADDI .x23 .x0 1),(1458,.ADDI .x25 .x9 0),
   (1459,.LUI .x26 1),(1460,.ADDI .x27 .x0 256)]
def configRows : List Row :=
  [(1461,.ADDI .x10 .x0 1024),(1462,.ADDI .x12 .x0 1536),(1463,.ADDI .x11 .x0 200),(1464,.ADDI .x13 .x0 1),
   (1465,.ADDI .x24 .x26 (-1)),(1466,.ADDI .x14 .x8 0),(1467,.ADDI .x17 .x18 0),(1468,.ADDI .x29 .x0 11)]
def keyRows : List Row :=
  [(1469,.LD .x31 .x22 8),(1470,.SD .x10 .x31 8),(1471,.LD .x31 .x22 16),(1472,.SD .x10 .x31 16),
   (1473,.LD .x31 .x22 24),(1474,.SD .x10 .x31 24)]
def headerRows := layoutRows++configRows++keyRows
def header (s : MachineState) := walkRows s headerRows

def keyOf (td : BitVec (8*actual.sizes.trapdoor)) := td.extractLsb' (8*1342177288) 192

theorem nested_slice {n outer width start len : Nat} (word : BitVec n) (bound : start+len≤width) :
    (word.extractLsb' outer width).extractLsb' start len=word.extractLsb' (outer+start) len := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have mid : start+j<width := by omega
  simp [mid,hj,Nat.add_assoc]

structure HeaderFacts : Prop where
  ready : ∀ (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions), 0<p.card → Ready td p (keyOf td) (header (actual.initialState .opening (td,p))) 0
  run : ∀ (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions), 0<p.card → ∀ fuel, let s:=actual.initialState .opening (td,p)
    execute openingImage (28+fuel) s true=(do let z ←execute openingImage fuel (header s) true;return z.charge 28 0)

end TwoPermutationPrototype.GroupedOpening

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open Opening (RecordMarks)
open PackedOpening (setupInstructions setupPrefix nonempty_count opening_first_boundary)
set_option maxRecDepth 22000
set_option maxHeartbeats 2000000

theorem header_fetch : presentRows headerRows := by
  have raw : ∀ i : Fin headerRows.length, let r:=headerRows[i]; r.1<1498 ∧
    (openingImage.code[r.1]?).bind Opening.decodeBase=some r.2 := by decide +kernel
  intro p hp;obtain ⟨j,hj,eq⟩:=List.mem_iff_getElem.mp hp;subst p
  intro st pc;exact prefix_fetch_base _ _ _ (raw ⟨j,hj⟩).1 pc (raw ⟨j,hj⟩).2

attribute [local simp] Opening.getReg_setReg Opening.getReg_setMem MachineState.getReg_setPC pc_of_set mem_of_set open_zero
attribute [local simp] mem_of_reg MachineState.getMem_setPC MachineState.getMem_setReg

theorem layout_ok (s : MachineState) (pc : s.pc=address 0) (nz : s.getReg .x16≠0#64) :
    legal layoutRows s := by
  simp [layoutRows,legal,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,pc,address,beq_iff_eq,nz,
    show signExtend21 5792#21=5792#64 by decide]

private def tailOps := setupInstructions.drop 3

private def linear : Instr → Bool
  | .ADDI .. | .ADD .. | .SLLI .. | .LUI .. => true
  | _ => false

private theorem assign_at_pc (s : MachineState) (r : Reg) (v p q : Word) :
    (((s.setPC p).setReg r v).setPC q)=((s.setReg r v).setPC q) := by cases r <;> rfl

private theorem linear_one (s : MachineState) (p : Word) (op : Instr) (h : linear op=true) :
    execInstrBr (s.setPC p) op=(execInstrBr s op).setPC (p+4) := by
  cases op <;> simp only [linear] at h <;> first | contradiction | skip
  all_goals simp only [execInstrBr,MachineState.getReg_setPC,pc_of_set,assign_at_pc]
  all_goals rfl

private theorem moved (s : MachineState) (p : Word) (ops : List Instr) (plain : ops.all linear=true) :
    ops.foldl execInstrBr (s.setPC p)=(ops.foldl execInstrBr s).setPC (p+BitVec.ofNat 64 (4*ops.length)) := by
  induction ops generalizing s p with
  | nil => simp
  | cons op rest ih =>
    simp only [List.all_cons,Bool.and_eq_true] at plain
    simp only [List.foldl_cons,linear_one _ _ _ plain.1,ih _ _ plain.2,List.length_cons,Nat.mul_add,BitVec.ofNat_add]
    congr 1
    rw [BitVec.add_assoc,BitVec.add_comm (BitVec.ofNat 64 (4*rest.length))];rfl

private theorem moved_tail (s : MachineState) :
    tailOps.foldl execInstrBr (s.setPC (address 1451))=(tailOps.foldl execInstrBr s).setPC (address 1461) :=
  moved s (address 1451) tailOps (by decide)

private theorem instructions_of_rows (s : MachineState) (rows : List Row) :
    walkRows s rows=(rows.map Prod.snd).foldl execInstrBr s := by
  induction rows generalizing s with
  | nil => rfl
  | cons row tail ih => exact ih (execInstrBr s row.2)

theorem layout_sem (s : MachineState) (pc : s.pc=address 0) (nz : s.getReg .x16≠0#64) :
    walkRows s layoutRows=(setupPrefix s 13).setPC (address 1461) := by
  let before:=setupPrefix s 3
  have here : before.pc=address 3 := by
    simp [before,setupPrefix,setupInstructions,execInstrBr,pc,address,beq_iff_eq,nz]
  have jump : execInstrBr before (.JAL .x0 5792)=before.setPC (address 1451) := by
    change before.setPC (before.pc+signExtend21 5792)=_;rw [here];rfl
  have first : layoutRows.map Prod.snd=setupInstructions.take 3++[.JAL .x0 5792]++tailOps := rfl
  have original : setupInstructions.take 13=setupInstructions.take 3++tailOps := rfl
  rw [instructions_of_rows,first,setupPrefix,original]
  simp only [List.foldl_append,List.foldl_cons,List.foldl_nil]
  exact (congrArg (List.foldl execInstrBr · tailOps) jump).trans (moved_tail before)

theorem config_ok (s : MachineState) (pc : s.pc=address 1461) : legal configRows s := by
  simp [configRows,legal,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,pc,address]

theorem config_frame (s : MachineState) (pc : s.pc=address 1461) (p : Positions)
    (b : Base s p) (salt : s.getReg .x22=5637148704) (base : s.getReg .x26=4096) (selector : s.getReg .x5=0) :
    let t:=walkRows s configRows
    t.pc=address 1469 ∧ t.mem=s.mem ∧ Base t p ∧ Registers t 0 p.card := by
  let t:=walkRows s configRows
  have keep (k : Reg) (h : k ∉ ([.x10,.x12,.x11,.x13,.x24,.x14,.x17,.x29] : List Reg)) : t.getReg k=s.getReg k := by
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at h
    simp [t,configRows,walkRows,execInstrBr,Ne.symm h.1,Ne.symm h.2.1,Ne.symm h.2.2.1,Ne.symm h.2.2.2.1,
      Ne.symm h.2.2.2.2.1,Ne.symm h.2.2.2.2.2.1,Ne.symm h.2.2.2.2.2.2.1,Ne.symm h.2.2.2.2.2.2.2]
  refine ⟨?_,?_,?_,?_⟩
  · simp [walkRows,configRows,execInstrBr,pc,address]
  · simp [walkRows,configRows,execInstrBr]
  · exact ⟨(keep _ (by decide)).trans b.indices,(keep _ (by decide)).trans b.heap,(keep _ (by decide)).trans b.count,
      (keep _ (by decide)).trans b.leaves,(keep _ (by decide)).trans b.start,(keep _ (by decide)).trans b.dest,
      (keep _ (by decide)).trans b.mark,(keep _ (by decide)).trans b.cap,
      (keep _ (by decide)).trans b.capLeaves⟩
  · constructor <;> simp [walkRows,configRows,execInstrBr,b.indices,b.count,salt,base,selector,indexAt,countWord,Opening.indicesBase,
      Opening.trapdoorBase,Opening.trapdoorBytes,LENGTH,LOG_LENGTH,signExtend12] <;> rfl

def keyCopy (s : MachineState) := ((s.setMem 1032 (s.getMem 5637148712)).setMem 1040 (s.getMem 5637148720)).setMem 1048 (s.getMem 5637148728)

theorem key_ok (s : MachineState) (p : Positions) (pc : s.pc=address 1469) (r : Registers s 0 p.card) :
    legal keyRows s := by
  simp [keyRows,legal,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,r.salt,r.input,pc,address,signExtend12] <;> decide

theorem key_frame (s : MachineState) (p : Positions) (pc : s.pc=address 1469) (r : Registers s 0 p.card) :
    let t:=walkRows s keyRows
    t.pc=address 1475 ∧ t.mem=(keyCopy s).mem ∧ ∀ k, k≠.x31 → t.getReg k=s.getReg k := by
  refine ⟨?_,?_,?_⟩
  · simp [walkRows,keyRows,execInstrBr,pc,address]
  · simp [walkRows,keyRows,execInstrBr,mem_of_store,keyCopy,r.input,r.salt,signExtend12,
      MachineState.getMem_setMem_ne (by decide : (5637148720#64)≠1032#64),
      MachineState.getMem_setMem_ne (by decide : (5637148728#64)≠1032#64),
      MachineState.getMem_setMem_ne (by decide : (5637148728#64)≠1040#64)]
  · intro k ne;simp [walkRows,keyRows,execInstrBr,Ne.symm ne]

theorem low_zero (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (w : Nat) (low : w<1024) :
    memoryView (actual.initialState .opening (td,p)) w=0 := by
  change (actual.initialState .opening (td,p)).getMem (BitVec.ofNat 64 (8*w))=_
  rw [initial_input_word actual .opening (td,p) (8*w) (by omega)]
  have zero (j : Nat) (hj : j<8) : inputByte actual .opening (td,p) (8*w+j)=0 := by
    have lo : ¬actual.layout.trapdoor≤8*w+j := by change ¬4294971424≤_;omega
    have ix : ¬actual.layout.indices≤8*w+j := by change ¬5905584160≤_;omega
    have img : (actual.image .opening).data=[]:=rfl
    simp [inputByte,Submission.inputBuffers,fixedBuffer,positionsBuffer,lo,ix,img]
  rw [Finset.sum_eq_zero (fun j hj => by rw [zero _ (Finset.mem_range.mp hj)];simp)];rfl

theorem key_words (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (j : Fin 3) :
    (actual.initialState .opening (td,p)).getMem (BitVec.ofNat 64 (5637148712+8*j.val)) =
      (keyOf td).extractLsb' (64*j.val) 64 := by
  have hj:=j.isLt
  rw [←word_at _ _ (by omega),show 5637148712+8*j.val=Opening.trapdoorBase+(1342177288+8*j.val) by unfold Opening.trapdoorBase LENGTH LOG_LENGTH;omega,
    Opening.input_trapdoor_slice actual actual_layout td p _ _ (by change _≤1610612736;omega)]
  unfold keyOf
  rw [nested_slice _ (by omega : 64*j.val+64≤192)]
  congr 1 <;> omega


theorem original_base (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (nz : 0<p.card) :
    let t := setupPrefix (actual.initialState .opening (td,p)) 13
    Base t p ∧ t.getReg .x22=5637148704 ∧ t.getReg .x26=4096 ∧
      t.mem=(actual.initialState .opening (td,p)).mem := by
  have b:=opening_first_boundary actual actual_layout td p nz
  exact ⟨⟨b.index,b.heap,b.left,b.leaves,b.proofBegin,b.dest,b.one,b.capHeap,b.capLeaves⟩,
    b.nonce,b.marks,(PackedOpening.setup_registers _).2.2.2.2.2.2.2.2.2.2.2⟩

theorem base_at_pc (p : Positions) (s : MachineState) (pc : Word) (b : Base s p) : Base (s.setPC pc) p :=
  ⟨b.indices,b.heap,b.count,b.leaves,b.start,b.dest,b.mark,b.cap,b.capLeaves⟩

end TwoPermutationPrototype.GroupedOpening

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open Opening (RecordMarks)
open PackedOpening (setupInstructions setupPrefix nonempty_count opening_first_boundary)
set_option maxRecDepth 22000
set_option maxHeartbeats 2000000

attribute [local irreducible] setupPrefix walkRows keyCopy header

structure HeaderRegisters (s : MachineState) (p : Positions) where
  pc : s.pc=address 1475
  r : Registers s 0 p.card
  b : Base s p

theorem header_core (init : MachineState) (p : Positions) (pc : init.pc=address 0) (nr : init.getReg .x16≠0#64)
    (base0 : Base (setupPrefix init 13) p)
    (salt0 : (setupPrefix init 13).getReg .x22=5637148704) (marks0 : (setupPrefix init 13).getReg .x26=4096)
    (mem0 : (setupPrefix init 13).mem=init.mem) (selector : (setupPrefix init 13).getReg .x5=0) :
    legal headerRows init ∧ Nonempty (HeaderRegisters (header init) p) ∧ (header init).mem=(keyCopy init).mem := by
  let l:=walkRows init layoutRows
  let c:=walkRows l configRows
  let t:=walkRows c keyRows
  have eq : l=(setupPrefix init 13).setPC (address 1461) := layout_sem init pc nr
  have base : Base l p := by rw [eq];exact base_at_pc _ _ _ base0
  have lpc : l.pc=address 1461 := by rw [eq];rfl
  have salt : l.getReg .x22=5637148704 := by rw [eq,MachineState.getReg_setPC];exact salt0
  have marks : l.getReg .x26=4096 := by rw [eq,MachineState.getReg_setPC];exact marks0
  have lm : l.mem=init.mem := by rw [eq];exact mem0
  obtain ⟨cp,cm,cb,cr⟩:=config_frame l lpc p base salt marks (by rw [eq,MachineState.getReg_setPC]; exact selector)
  have cMem : c.mem=init.mem := cm.trans lm
  obtain ⟨tpc,tm,keep⟩:=key_frame c p cp cr
  have mem : t.mem=(keyCopy init).mem := tm.trans (by simp only [keyCopy,MachineState.setMem,MachineState.getMem,cMem])
  have join (s : MachineState) (xs ys : List Row) : walkRows s (xs++ys)=walkRows (walkRows s xs) ys := by
    simp only [walkRows,List.foldl_append]
  have header_eq : header init=t := by unfold header headerRows;rw [join,join]
  refine ⟨?_,?_,header_eq ▸ mem⟩
  · unfold headerRows
    apply legal_append
    · exact legal_append init _ _ (layout_ok init pc nr) (config_ok l lpc)
    · rw [join];exact key_ok c p cp cr
  · rw [header_eq]
    exact ⟨⟨tpc,⟨(keep _ (by decide)).trans cr.input,(keep _ (by decide)).trans cr.output,
      (keep _ (by decide)).trans cr.selector,(keep _ (by decide)).trans cr.width,(keep _ (by decide)).trans cr.primitive,
      (keep _ (by decide)).trans cr.index,(keep _ (by decide)).trans cr.leftReg,(keep _ (by decide)).trans cr.salt,
      (keep _ (by decide)).trans cr.base,(keep _ (by decide)).trans cr.divReg,(keep _ (by decide)).trans cr.tileMask⟩,
      ⟨(keep _ (by decide)).trans cb.indices,(keep _ (by decide)).trans cb.heap,(keep _ (by decide)).trans cb.count,
       (keep _ (by decide)).trans cb.leaves,(keep _ (by decide)).trans cb.start,(keep _ (by decide)).trans cb.dest,
       (keep _ (by decide)).trans cb.mark,(keep _ (by decide)).trans cb.cap,
       (keep _ (by decide)).trans cb.capLeaves⟩⟩⟩

end TwoPermutationPrototype.GroupedOpening

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open Opening (RecordMarks)
open PackedOpening (setupInstructions setupPrefix nonempty_count opening_first_boundary)
set_option maxRecDepth 22000
set_option maxHeartbeats 2000000

attribute [local irreducible] setupPrefix walkRows keyCopy header
private theorem key_outside (s : MachineState) (w : Word) (a : w≠1032) (b : w≠1040) (c : w≠1048) :
    (keyCopy s).getMem w=s.getMem w := by
  unfold keyCopy
  exact (MachineState.getMem_setMem_ne c).trans ((MachineState.getMem_setMem_ne b).trans (MachineState.getMem_setMem_ne a))

private theorem key_cell (s : MachineState) (j : Fin 3) : memoryView (keyCopy s) (129+j.val)=
    s.getMem (BitVec.ofNat 64 (5637148712+8*j.val)) := by
  fin_cases j <;> unfold memoryView keyCopy <;> rfl

/-- The displaced record setup preserves the selector initialized by the ABI. -/
private theorem selector_after_setup (s : MachineState) (nz : s.getReg .x16≠0#64) :
    (setupPrefix s 13).getReg .x5 = s.getReg .x5 := by
  simp [setupPrefix,setupInstructions,Opening.setupInstructions,execInstrBr,beq_iff_eq,
    show s.getReg .x0=0#64 from rfl,nz,MachineState.getReg_setPC,Opening.getReg_setReg]

theorem header_valid (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (nz : 0<p.card) :
    let init:=actual.initialState .opening (td,p)
    legal headerRows init ∧ Ready td p (keyOf td) (header init) 0 := by
  let init:=actual.initialState .opening (td,p)
  let t:=header init
  have nr : init.getReg .x16≠0#64 := nonempty_count p nz
  obtain ⟨b,salt,marks,mem0⟩:=original_base td p nz
  obtain ⟨valid,⟨regs⟩,mem⟩:=header_core init p rfl nr b salt marks mem0 ((selector_after_setup init nr).trans rfl)
  refine ⟨valid,⟨regs.r,regs.b,?_,?_,?_⟩⟩
  · simpa only [passPC,ite_eq_right (Nat.ne_of_lt nz)] using regs.pc
  · intro w fit guard _ _
    have neq (j : Nat) (hj : 129≤j ∧ j≤131) : wordAddress w≠wordAddress j :=
      fun h => (by have :=wordAddress_injective_of_bound (by omega) (by omega) h;omega : False)
    change t.mem _=_;rw [mem]
    change (keyCopy init).getMem (wordAddress w)=_
    exact key_outside init _ (neq 129 (by decide)) (neq 130 (by decide)) (neq 131 (by decide))
  · intro j lo hi;change t.mem _=_;rw [mem]
    by_cases stored : j≤3
    · let ix : Fin 3 := ⟨j-1,by omega⟩
      change memoryView (keyCopy init) (128+j)=_
      rw [show 128+j=129+ix.val by dsimp [ix];omega,key_cell init ix]
      exact key_words td p ix
    · have neq (n : Nat) (hn : 129≤n ∧ n≤131) : wordAddress (128+j)≠wordAddress n :=
        fun h => (by have :=wordAddress_injective_of_bound (by omega) (by omega) h;omega : False)
      change (keyCopy init).getMem (wordAddress (128+j))=_
      rw [key_outside init _ (neq 129 (by decide)) (neq 130 (by decide)) (neq 131 (by decide))]
      change memoryView init (128+j)=_
      rw [low_zero td p _ (by omega)]
      apply BitVec.eq_of_getLsbD_eq;intro b hb
      simp [Grouped.keyBlock,hb,show 192≤64*(j-1)+b by omega]

theorem header_run (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (nz : 0<p.card) (fuel : Nat) :
    let s:=actual.initialState .opening (td,p)
    execute openingImage (28+fuel) s true=(do let z ←execute openingImage fuel (header s) true;return z.charge 28 0) := by
  simpa only [header,show headerRows.length=28 by decide,show price headerRows=28 by decide] using
    walk_rows_run _ headerRows (header_valid td p nz).1 header_fetch fuel true

theorem certifiedHeader : HeaderFacts :=
  ⟨fun td p nz => (header_valid td p nz).2,header_run⟩

end TwoPermutationPrototype.GroupedOpening
