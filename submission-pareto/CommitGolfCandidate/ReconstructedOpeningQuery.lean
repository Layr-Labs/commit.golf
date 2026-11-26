import CommitGolfCandidate.ReconstructedOpeningIndex
import CommitGolfCandidate.ReconstructedLeafTape

namespace CommitGolfCandidate.Reconstruction.OpeningQuery
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel LeafSteps Generator CommitWindows
open TwoPermutationPrototype.RV64 OpeningOps OpeningIndex
set_option maxRecDepth 24000
set_option maxHeartbeats 2000000
attribute [local irreducible] ArtifactEncoding.decode execute

abbrev frame : Nat := 68719476336
abbrev indexWord (ord : Nat) := 738198020+ord
abbrev saveCount : Nat := 8589934271
abbrev savePtr : Nat := 8589934270

structure Entry (m : Model) (ord : Nat) (i : Index) : Prop where
  room : ord<2^24
  zero : m.reg .x0=0
  base : m.reg .x8=68719476336
  tag : m.reg .x31=2051
  pointer : m.reg .x11=wordAddress (indexWord ord)
  position : m.mem (indexWord ord)=BitVec.ofNat 64 i.val
  reciprocal : m.mem 8589934254=2863333376
  mask : m.mem 8589934253=65535
  generator : m.mem 8589934258=5637148520

def saveOps (ord : Nat) : List Op :=
  [.reg .x10 (.lui 1),
   .reg .x10 (.sub .x8 .x10),
   .sd .x10 .x12 1928 saveCount,
   .reg .x10 (.lui 1),
   .reg .x10 (.sub .x8 .x10),
   .sd .x10 .x11 1920 savePtr,
   .ld .x15 .x11 0 (indexWord ord)]

def prepareOps : List Op :=
  [.reg .x10 (.slli .x15 52),
   .reg .x14 (.srli .x10 52),
   .reg .x11 (.slli .x14 48),
   .reg .x12 (.lui 1),
   .reg .x12 (.sub .x8 .x12),
   .ld .x12 .x12 1792 8589934254,
   .reg .x16 (.mulhu .x11 .x12),
   .reg .x11 (.srli .x16 16),
   .reg .x12 (.lui 2731),
   .reg .x10 (.mulhu .x10 .x12),
   .reg .x10 (.srli .x10 19),
   .reg .x12 (.slli .x10 8),
   .reg .x10 (.slli .x10 6),
   .reg .x10 (.sub .x10 .x12),
   .reg .x10 (.add .x14 .x10)]

def counterOps : List Op :=
  [.reg .x12 (.lui 1),
   .reg .x12 (.sub .x8 .x12),
   .ld .x12 .x12 1784 8589934253,
   .reg .x10 (.and .x10 .x12),
   .reg .x10 (.sub .x15 .x10),
   .reg .x10 (.slli .x10 8),
   .reg .x10 (.add .x31 .x10),
   .reg .x10 (.addi .x10 1845),
   .reg .x12 (.lui 1),
   .reg .x12 (.sub .x8 .x12),
   .ld .x12 .x12 1824 8589934258,
   .sd .x12 .x10 16 (generatorBase+1)]

def argsOps : List Op :=
  [.reg .x10 (.andi .x11 120),
   .reg .x10 (.sub .x12 .x10),
   .reg .x11 (.addi .x0 200),
   .reg .x12 (.addi .x8 2048),
   .reg .x12 (.addi .x12 3984),
   .reg .x13 (.addi .x0 1),
   .reg .x5 (.addi .x0 0)]

def records (ord : Nat) := saveOps ord ++ prepareOps ++ counterOps ++ argsOps
def after (m : Model) (ops : List Op) := ops.foldl (fun a i => i.apply a) m
def saves (m : Model) := (m.store saveCount (m.reg .x12)).store savePtr (m.reg .x11)

private theorem index_separate (ord : Nat) (small : ord<2^24) :
    indexWord ord ≠ saveCount ∧ indexWord ord ≠ savePtr := by dsimp [indexWord,saveCount,savePtr];omega

theorem saved (m : Model) (ord : Nat) (i : Index) (h : Entry m ord i) :
    let s := after m (saveOps ord)
    Checked m (saveOps ord) ∧ s.reg .x15=BitVec.ofNat 64 i.val ∧ s.mem=(saves m).mem ∧
      (∀ r, r≠.x15 → r≠.x10 → s.reg r=m.reg r) := by
  let index := index_separate ord h.room
  have room : indexWord ord < 2^33 := by dsimp [indexWord];have := h.room;omega
  constructor
  · simp [saveOps,Checked,Op.Valid,Op.apply,Expr.eval,Model.set,Model.store,h.base,h.pointer,wordAddress,signExtend12,saveCount,savePtr]
    exact room
  constructor
  · change (if indexWord ord=savePtr then m.reg .x11 else
       if indexWord ord=saveCount then m.reg .x12 else m.mem (indexWord ord))=_
    rw [ite_eq_right index.2,ite_eq_right index.1,h.position]
  exact ⟨rfl,fun r a b => by simp [after,saveOps,Op.apply,Model.set,Model.store,a.symm,b.symm]⟩

def preMul (i : Index) := BitVec.ofNat 64 i.val <<< 52

theorem prepared (m : Model) (i : Index)
    (index : m.reg .x15=BitVec.ofNat 64 i.val) (base : m.reg .x8=68719476336)
    (magic : m.mem 8589934254 = 2863333376) :
    let s := after m prepareOps
    Checked m prepareOps ∧ s.mem=m.mem ∧ s.reg .x16=highProduct (slot i) ∧
    s.reg .x11=highProduct (slot i) >>> 16 ∧ s.reg .x14=word (slot i) ∧
    s.reg .x10 = word (slot i) + ((bucket (slot i) <<< 6)-(bucket (slot i) <<< 8)) ∧
    (∀ r, r≠.x16 → r≠.x14 → r≠.x12 → r≠.x11 → r≠.x10 → s.reg r=m.reg r) := by
  constructor
  · simp [prepareOps,Checked,Op.Valid,Op.apply,Expr.eval,Model.set,base,wordAddress]; decide
  refine ⟨rfl,?_,?_,?_,?_,?_⟩
  · change rv64_mulhu (((m.reg .x15 <<< 52) >>> 52) <<< 48) (m.mem 8589934254) = _
    rw [index,OpeningIndex.low,magic];rfl
  · change rv64_mulhu (((m.reg .x15 <<< 52) >>> 52) <<< 48) (m.mem 8589934254) >>> 16 = _
    rw [index,OpeningIndex.low,magic];rfl
  · change (m.reg .x15 <<< 52) >>> 52 = _
    rw [index,OpeningIndex.low]
  · change ((m.reg .x15 <<< 52) >>> 52) + (((rv64_mulhu (m.reg .x15 <<< 52) 11186176 >>> 19) <<< 6) -
       ((rv64_mulhu (m.reg .x15 <<< 52) 11186176 >>> 19) <<< 8)) = _
    rw [index,OpeningIndex.low,truncate_index];rfl
  · intro r a b c d e
    simp [after,prepareOps,Op.apply,Model.set,a.symm,b.symm,c.symm,d.symm,e.symm]

theorem countered (m : Model) (i : Index)
    (index : m.reg .x15=BitVec.ofNat 64 i.val) (base : m.reg .x8=68719476336)
    (tag : m.reg .x31=2051) (mask : m.mem 8589934253=65535) (gen : m.mem 8589934258=5637148520)
    (off : m.reg .x10=word (slot i) + ((bucket (slot i) <<< 6)-(bucket (slot i) <<< 8))) :
    let s := after m counterOps
    Checked m counterOps ∧ s.mem=TwoPermutationPrototype.writeWord m.mem (generatorBase+1)
      (BitVec.ofNat 64 (Generator.counter (tileOf i) (groupOf i))) ∧
    s.reg .x12=5637148520 ∧ (∀ r, r≠.x12 → r≠.x10 → s.reg r=m.reg r) := by
  constructor
  · simp [counterOps,Checked,Op.Valid,Op.apply,Expr.eval,Model.set,base,gen,wordAddress,generatorBase]; decide
  constructor
  · change TwoPermutationPrototype.writeWord m.mem _ (m.reg .x31 +
          ((m.reg .x15 - (m.reg .x10 &&& m.mem 8589934253)) <<< 8) + signExtend12 1845) = _
    rw [tag,index,off,mask]
    exact congrArg (TwoPermutationPrototype.writeWord m.mem (generatorBase+1)) (query_counter i)
  exact ⟨gen,fun r a b => by simp [after,counterOps,Op.apply,Model.set,Model.store,a.symm,b.symm]⟩

theorem arguments (m : Model) (i : Index) (zero : m.reg .x0=0) (base : m.reg .x8=68719476336)
    (src : m.reg .x12=5637148520) (win : m.reg .x11=highProduct (slot i) >>> 16) :
    let s := after m argsOps
    Checked m argsOps ∧ s.reg .x5=0 ∧ s.reg .x10=wordAddress (generatorBase-marker (groupOf i)) ∧
    s.reg .x11=200 ∧ s.reg .x12=wordAddress 8589934272 ∧ s.reg .x13=1 ∧ s.mem=m.mem ∧
    (∀ r, r≠.x5 → r≠.x10 → r≠.x11 → r≠.x12 → r≠.x13 → s.reg r=m.reg r) := by
  refine ⟨by simp [argsOps,Checked,Op.Valid],?_,?_,?_,?_,?_,rfl,?_⟩
  · change m.reg .x0+0=0;rw [zero];rfl
  · change m.reg .x12 - (m.reg .x11 &&& 120)=_
    rw [src,win];exact query_address i
  · change m.reg .x0+200=200;rw [zero];rfl
  · change m.reg .x8+signExtend12 2048+signExtend12 3984=_
    rw [base];rfl
  · change m.reg .x0+1=1;rw [zero];rfl
  · intro r a b c d e
    simp [after,argsOps,Op.apply,Model.set,a.symm,b.symm,c.symm,d.symm,e.symm]

def atQuery (m : Model) (ord : Nat) := after (after (after (after m (saveOps ord)) prepareOps) counterOps) argsOps
def start (i : Index) := generatorBase-marker (groupOf i)
def queryCode := (records 0).map Op.instr ++ [.ECALL]

private theorem ops_same (j : Nat) : (records j).map Op.instr = (records 0).map Op.instr := rfl

structure Ready (m : Model) (i : Index) : Prop where
  reg0 : m.reg .x5=0
  src : m.reg .x10=wordAddress (start i)
  len : m.reg .x11=200
  dst : m.reg .x12=wordAddress 8589934272
  tag : m.reg .x13=1
  index : m.reg .x15=BitVec.ofNat 64 i.val
  slot : m.reg .x14=word (OpeningIndex.slot i)
  prod : m.reg .x16=highProduct (OpeningIndex.slot i)

theorem setup (o : Oracle) (m : Model) (ord : Nat) (i : Index) (h : Entry m ord i) :
    let t := atQuery m ord
    Contract o ((records ord).map Op.instr) m t ∧ Ready t i ∧
    t.mem=TwoPermutationPrototype.writeWord (saves m).mem (generatorBase+1)
      (BitVec.ofNat 64 (Generator.counter (tileOf i) (groupOf i))) := by
  let a := after m (saveOps ord)
  let b := after a prepareOps
  let c := after b counterOps
  obtain ⟨ca,ai,am,ar⟩ := saved m ord i h
  have abase : a.reg .x8=68719476336 := (ar _ (by decide) (by decide)).trans h.base
  have amagic : a.mem 8589934254=2863333376 := by rw [show a.mem=_ from am];exact h.reciprocal
  have amask : a.mem 8589934253=65535 := by rw [show a.mem=_ from am];exact h.mask
  have agen : a.mem 8589934258=5637148520 := by rw [show a.mem=_ from am];exact h.generator
  obtain ⟨cb,bm,bp,bw,bs,bo,br⟩ := prepared a i ai abase amagic
  have pe (r : Reg) (p : r≠.x16 ∧ r≠.x14 ∧ r≠.x12 ∧ r≠.x11 ∧ r≠.x10) : b.reg r=a.reg r :=
    br r p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2
  have bi : b.reg .x15=BitVec.ofNat 64 i.val := (pe _ (by decide)).trans ai
  have bb : b.reg .x8=68719476336 := (pe _ (by decide)).trans abase
  have bt : b.reg .x31=2051 := (pe _ (by decide)).trans ((ar _ (by decide) (by decide)).trans h.tag)
  have bz : b.reg .x0=0 := (pe _ (by decide)).trans ((ar _ (by decide) (by decide)).trans h.zero)
  have bmask : b.mem 8589934253=65535 := by rw [show b.mem=_ from bm];exact amask
  have bgen : b.mem 8589934258=5637148520 := by rw [show b.mem=_ from bm];exact agen
  obtain ⟨cc,cm,cs,cr⟩ := countered b i bi bb bt bmask bgen bo
  obtain ⟨cd,dz,ds,dl,dd,dt,dm,dr⟩ := arguments c i ((cr _ (by decide) (by decide)).trans bz)
    ((cr _ (by decide) (by decide)).trans bb) cs ((cr _ (by decide) (by decide)).trans bw)
  constructor
  · unfold records
    simp only [List.map_append]
    apply LeafModel.combine
    · apply LeafModel.combine
      · exact LeafModel.combine (checked_run o m _ ca) (checked_run o a _ cb)
      · exact checked_run o b _ cc
    · exact checked_run o c _ cd
  constructor
  · refine ⟨dz,ds,dl,dd,dt,?_,?_,?_⟩
    all_goals apply Eq.trans (dr _ (by decide) (by decide) (by decide) (by decide) (by decide))
    all_goals apply Eq.trans (cr _ (by decide) (by decide))
    · exact bi
    · exact bs
    · exact bp
  · exact dm.trans (cm.trans (congrArg (fun mem => TwoPermutationPrototype.writeWord mem
      (generatorBase+1) (BitVec.ofNat 64 (Generator.counter (tileOf i) (groupOf i)))) (bm.trans am)))

private theorem fetched : HonestMachine.Fetched (Artifact.submission.image .opening) (consecutive 143 queryCode) := by
  exact HonestMachine.fetched_of_packed _ _ Artifact.openingCode rfl (by decide) (by change ∀ k : Fin 42, _;decide) (by
    change ∀ k : Fin 42, _;intro k;fin_cases k <;> rfl)

theorem query_run (o : Oracle) (m : Model) (ord : Nat) (i : Index) (h : Entry m ord i)
    (s : MachineState) (loc : s.pc=CommitBlocks.addr 143) (fits : Fits s m) :
    let t := atQuery m ord
    ∃ u, CommitExact.Segment o (Artifact.submission.image .opening) 42 s u ∧ u.pc=CommitBlocks.addr 185 ∧
      Fits u (t.permute o (start i) 8589934272) := by
  obtain ⟨run,ready,_⟩ := setup o m ord i h
  let t := atQuery m ord
  have mark : marker (groupOf i) ≤16 := by unfold marker;omega
  have r := LeafModel.permutation o t (start i) 8589934272 (by unfold start generatorBase;omega)
    (by decide) ready.src ready.dst ready.reg0 ready.len ready.tag
  obtain ⟨u,trace,afterFit⟩ := LeafModel.combine run r s fits
  rw [ops_same] at trace
  exact ⟨u,segment o _ queryCode s u 143 loc trace fetched,trace.next_pc 143 loc,afterFit⟩

end CommitGolfCandidate.Reconstruction.OpeningQuery
