import CommitGolfCandidate.Stage3cChainPair
import CommitGolfCandidate.Stage3cPointerPass
namespace CommitGolfCandidate.Chained.BinaryMachine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 16000
set_option maxHeartbeats 8000000
set_option Elab.async false

private theorem scratch_transfer {H base salt d s t} (old : TreeState H base salt d s)
    (frame : unchanged s t scratchBase 96) : TreeState H base salt d t := by
  constructor
  · intro k hk i hi
    have e:=parent_below_salts _ _ hi
    refine (frame _ _ ?_ (Or.inl ?_)).trans (old.nodes _ hk _ hi)
    · change _≤2^36;unfold rowBase at e;omega
    · unfold scratchBase rowBase at *;omega
  · intro ix;have e:=salt_limits ix
    exact (frame _ 24 (by change _≤2^36;unfold scratchBase at e;omega) (Or.inl e.2)).trans (old.salts ix)
  · intro h j hj
    have e:=gap_limit h j hj
    have bound : tagAddr h j+32≤scratchBase:=e.trans (by decide : rowBase≤scratchBase)
    constructor
    · exact (frame _ 24 (by change _≤2^36;unfold scratchBase at bound;omega) (Or.inl (by omega))).trans (old.pads h j hj).1
    · exact fun c=>(frame _ 8 (by change _≤2^36;unfold scratchBase at bound;omega) (Or.inl (by omega))).trans ((old.pads h j hj).2 c)

theorem all_pairs (o : Oracle) {d : Height} (cut : chained d) (n b : Nat) (s : MachineState)
    (base : Nat→Output) (salt : Late.SaltTape) (total : b+n=tiles d) (frame : PairFrame d b s)
    (tree : TreeState o.compression base salt d.val s) (rows : doneRows o.compression base d.val (2*b) s) :
    ∃ t,PairFrame d (tiles d) t ∧ TreeState o.compression base salt d.val t ∧
      doneRows o.compression base d.val (2*tiles d) t ∧
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
  have st:=tree_mem eq.symm (scratch_transfer tree (clear_frame s 8 le_rfl))
  have pad:=clear_pads s
  obtain ⟨twice,some_,tile,inner,cost,tag⟩:= (by decide +kernel : ∀ h : Height,chained h→
    2*tiles h=count h ∧ 0<tiles h ∧ tileSize h=2 ∧ h.val<23 ∧
    8+(headerOps h).length+tiles h*(2*segmentWords h+4)=passSteps h ∧
    BitVec.ofNat 64 (2^63+256*(h.val+1))=tagWord h 0) d cut
  have bias : cursorBias d=0:=by simp [cursorBias,cut]
  have entry : PairFrame d 0 a := by
    refine ⟨⟨ef.toCommon,?_,?_,?_,(ef.tag cut).trans tag,ef.mask cut⟩,?_,?_⟩
    · simpa [srcAddr,bias] using ef.chainSrc cut
    · simpa [dstAddr,bias] using ef.chainDst cut
    · simpa [tile] using ef.counter (by rw [tile]; decide)
    · simpa [bodyEntry,tile,some_] using ef.pc
    · exact ⟨(read_congr_mem a z _ _ eq).trans pad.second,(read_congr_mem a z _ _ eq).trans pad.last⟩
  have zeros:=clear_run o d cut s cm pc
  have head : Runs .commit true o z a (headerOps d).length (headerOps d).length 0:=runs_pure (header_run d z atZ)
  obtain ⟨t,last,stable,done_,parents⟩:=all_pairs o cut (tiles d) 0 a base salt (by omega) entry st (fun _ h=>by omega)
  rw [twice] at done_
  refine ⟨t,last.pc.trans (by rw [if_neg (Nat.lt_irrefl _)]),last.toCommon,close_level stable done_,?_⟩
  have joined:=runs_comp (runs_comp zeros head) parents
  -- clear_run and header_run each contribute 0 calls, so the index is 0+0+body.
  simp only [Nat.zero_add] at joined
  have steps : passSteps d=8+(headerOps d).length+tiles d*(2*segmentWords d+4):=cost.symm
  have callsEq : count d*calls d=tiles d*(2*calls d) := by
    rw [←twice,Nat.mul_assoc,Nat.mul_left_comm 2]
  have cycEq : passCycles d=8+(headerOps d).length+tiles d*(2*segmentWords d+4+7*(2*calls d)) := by
    rw [phase_counts,steps,←twice]
    have split := Nat.mul_add (tiles d) (2*segmentWords d+4) (7*(2*calls d))
    have extra : 7*(2*tiles d)*calls d=tiles d*(7*(2*calls d)) := by
      have step1 : 7*(2*tiles d)*calls d=(2*tiles d)*(7*calls d) := by
        rw [Nat.mul_assoc,Nat.mul_left_comm 7 (2*tiles d) (calls d)]
      have step2 : (2*tiles d)*(7*calls d)=2*(tiles d*(7*calls d)) :=
        Nat.mul_assoc 2 (tiles d) (7*calls d)
      have step3 : 2*(tiles d*(7*calls d))=tiles d*(2*(7*calls d)) := by
        rw [Nat.mul_left_comm 2 (tiles d) (7*calls d)]
      have step4 : 2*(7*calls d)=7*(2*calls d) := by
        rw [←Nat.mul_assoc,Nat.mul_comm 2 7,Nat.mul_assoc]
      rw [step1,step2,step3,step4]
    rw [Nat.add_assoc,split,extra]
  rw [steps,cycEq,callsEq]
  exact joined

theorem all_stages (d : Height) : StageLaw d := by
  by_cases c : chained d
  · exact chain_pass d c
  · exact pointer_pass d c
end CommitGolfCandidate.Chained.BinaryMachine
