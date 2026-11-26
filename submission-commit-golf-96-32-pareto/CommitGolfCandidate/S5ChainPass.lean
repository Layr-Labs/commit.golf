import CommitGolfCandidate.S5PairLoop
namespace CommitGolfCandidate.S5Machine
open CommitGolfCandidate.Chained
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

private theorem scratch_transfer {H base salt d s t} (old : TreeState H base salt d s) (frame : unchanged s t scratchBase 96) :
    TreeState H base salt d t := by
  constructor
  · intro k hk i hi
    have e:=parent_below_salts _ _ hi
    refine (frame _ _ ?_ (Or.inl ?_)).trans (old.nodes _ hk _ hi)
    · change _≤2^36;unfold rowBase at e;omega
    · unfold scratchBase rowBase at *;omega
  · intro ix;have e:=salt_limits ix
    exact (frame _ 24 (by change _≤2^36;unfold scratchBase at e;omega) (Or.inl e.2)).trans (old.salts ix)
  · intro h j k pad
    have bound:=padValid h j k pad
    have upper : unusedSlotAddr h j k+32≤scratchBase:=bound.trans (by decide)
    constructor
    · exact (frame _ 24 (by change _≤2^36;unfold scratchBase at upper;omega) (Or.inl (by omega))).trans (old.pads h j k pad).1
    · exact fun safe=>(frame _ 8 (by change _≤2^36;unfold scratchBase at upper;omega) (Or.inl (by omega))).trans ((old.pads h j k pad).2 safe)

theorem all_pairs (o : Oracle) {d : Height} (cut : chained d) (n b : Nat) (s : MachineState) (base : Nat→Output) (salt : Late.SaltTape)
    (total : b+n=tiles d) (frame : PairFrame d b s) (tree : TreeState o.compression base salt d.val s)
    (rows : doneRows o.compression base d.val (2*b) s) :
    ∃ t,PairFrame d (tiles d) t ∧ TreeState o.compression base salt d.val t ∧ doneRows o.compression base d.val (2*tiles d) t ∧
      Runs .commit true o s t (n*(2*segmentWords d+4)) (n*(2*segmentWords d+4+7*(2*calls d))) (n*(2*calls d)) := by
  induction n generalizing b s with
  | zero=>
    rw [Nat.add_zero] at total;subst b
    exact ⟨s,frame,tree,rows,by simpa using runs_id .commit true o s⟩
  | succ n ih=>
    obtain ⟨u,f,st,rd,head⟩:=pair_step o frame cut (by omega) tree rows
    obtain ⟨t,final,fin,all,tail⟩:=ih (b+1) u (by omega) f st rd
    refine ⟨t,final,fin,all,?_⟩
    have joined:=runs_comp head tail
    simpa only [Nat.succ_mul,Nat.add_comm] using joined

private theorem pair_tail (o : Oracle) {d : Height} (cut : chained d) (s : MachineState) (base : Nat→Output) (salt : Late.SaltTape)
    (frame : PairFrame d (tiles d) s) (tree : TreeState o.compression base salt d.val s)
    (rows : doneRows o.compression base d.val (2*tiles d) s) :
    ∃ t,t.pc=pcAt (passEnd d) ∧ Common t ∧ TreeState o.compression base salt (d.val+1) t ∧
      Runs .commit true o s t (remainder d*segmentWords d) (remainder d*(segmentWords d+7*calls d)) (remainder d*calls d) := by
  have facts := (by decide +kernel : ∀ h : Height,chained h →
    remainder h=count h%2 ∧ count h=2*tiles h+remainder h ∧ mainExit h+remainder h*segmentWords h=passEnd h) d cut
  have endPC : s.pc=pcAt (mainExit d) := frame.pc.trans (by rw [if_neg (Nat.lt_irrefl _)])
  by_cases odd : count d%2=1
  · have rem:=facts.1.trans odd
    have size : 2*tiles d+1=count d:=by omega
    have pc : s.pc=pcAt (segmentPC d Lane.tail) := by simpa [segmentPC,odd] using endPC
    have valid : 2*tiles d+Lane.tail.val<count d := by change 2*tiles d+0<count d;omega
    obtain ⟨t,run,next,ip,pads,effect⟩:=chained_lane o d (tiles d) Lane.tail s cut frame.toPairCtx pc frame.pad tree.pads valid
    have st:=node_frame tree effect valid
    have built:=grow_row tree (show doneRows _ _ _ (2*tiles d+Lane.tail.val) s from rows) effect valid
    change doneRows _ _ _ (2*tiles d+0+1) t at built
    rw [Nat.add_zero,size] at built
    refine ⟨t,?_,next.toCommon,close_level st built,by simpa only [rem,Nat.one_mul] using run⟩
    apply ip.trans;apply congrArg pcAt
    have haveEnd:=facts.2.2;simpa [segmentPC,odd,rem] using haveEnd
  · have rem : remainder d=0:=by omega
    have size : 2*tiles d=count d := by omega
    have endEq : mainExit d=passEnd d := by simpa only [rem,Nat.zero_mul,Nat.add_zero] using facts.2.2
    refine ⟨s,endPC.trans (congrArg pcAt endEq),frame.toCommon,close_level tree (size ▸ rows),?_⟩
    simpa only [rem,Nat.zero_mul] using runs_id .commit true o s
theorem chain_pass (d : Height) (cut : chained d) : StageLaw d := by
  intro o s base salt pc cm tree
  let z:=clearScratch s 8
  let a:=entered z d
  have atZ : z.pc=pcAt (pureEntry d) := by
    rw [show z.pc=s.pc+BitVec.ofNat 64 (4*8) from clear_pc s 8,pc,pc_delta,pureEntry,if_pos cut]
  have common : Common z := by
    obtain ⟨c1,c2,c3,c4,c5,c6,c7,c8,c9⟩:=cm
    constructor <;> apply (clear_register s 8 _).trans <;> assumption
  obtain ⟨ef,eq⟩:=entered_frame d z atZ common
  have st:=transfer_tree (scratch_transfer tree (clear_frame s 8 le_rfl)) eq
  have pad:=clear_pads s
  obtain ⟨twice,some_,tile,inner,cost,tag⟩:= (by decide +kernel : ∀ h : Height,chained h→
    2*tiles h+remainder h=count h ∧ 0<tiles h ∧ tileSize h=2 ∧ h.val<23 ∧
    8+(headerOps h).length+tiles h*(2*segmentWords h+4)+remainder h*segmentWords h=passSteps h ∧
    BitVec.ofNat 64 (2^63+256*(h.val+1))=tagWord h 0) d cut
  have bias : cursorBias d=0:=by simp [cursorBias,cut]
  have entry : PairFrame d 0 a := by
    refine ⟨⟨ef.toCommon,?_,?_,?_,(ef.tag cut).trans tag,ef.mask cut⟩,?_,?_⟩
    · rw [show srcAddr d (2*0)=nodeAddress d.val 0 by rw [srcAddr,←row_base];simp];simpa [bias] using ef.src
    · simpa [dstAddr,bias] using ef.dst
    · simpa [tile] using ef.counter inner
    · simpa [bodyEntry,tile,some_] using ef.pc
    · exact ⟨(read_congr_mem a z _ _ eq).trans pad.second,(read_congr_mem a z _ _ eq).trans pad.last⟩
  have zeros:=clear_run o d cut s cm pc
  have head : Runs .commit true o z a (headerOps d).length (headerOps d).length 0:=runs_pure (header_run d z atZ)
  obtain ⟨t,last,stable,done_,parents⟩:=all_pairs o cut (tiles d) 0 a base salt (by omega) entry st (fun _ h=>by omega)
  obtain ⟨u,endPC,cm',final,tail⟩:=pair_tail o cut t base salt last stable done_
  refine ⟨u,endPC,cm',final,?_⟩
  have joined:=runs_comp (runs_comp (runs_comp zeros head) parents) tail
  rw [phase_counts,←cost,←twice]
  convert joined using 1 <;> ring
end CommitGolfCandidate.S5Machine
