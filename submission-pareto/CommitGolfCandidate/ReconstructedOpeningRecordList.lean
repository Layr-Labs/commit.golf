import CommitGolfCandidate.ReconstructedOpeningRecordExecution
import CommitGolfCandidate.ReconstructedCapIterate
import CommitGolfCandidate.ReconstructedHonestDelivery

namespace CommitGolfCandidate.Reconstruction.OpeningRecordList
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel OpeningCursor OpeningPut OpeningRecordExecution
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling OpeningRecordFrame OpeningLoopRegs
open CommitBlocks (addr)
set_option maxRecDepth 20000
set_option maxHeartbeats 1800000
attribute [local irreducible] ArtifactEncoding.decode execute

noncomputable def fields (o : Oracle) (k : Generator.Key) (msg : Message) (ps : Positions) (ord : Nat) :=
  ((ps.sort (·≤·)).take ord).flatMap (record o k msg)

theorem next (o : Oracle) (k : Generator.Key) (msg : Message) (ps : Positions) (ord : Nat) (h : ord<ps.card) :
    fields o k msg ps (ord+1)=fields o k msg ps ord++record o k msg (sequence ps ord h) := by
  have within : ord<(ps.sort (·≤·)).length := by simpa using h
  simp only [fields,List.take_succ_eq_append_getElem within,List.flatMap_append,List.flatMap_cons,
    List.flatMap_nil,List.append_nil,OpeningLoopRegs.sequence]

theorem bits (o : Oracle) (k : Generator.Key) (msg : Message) (ps : Positions) (ord : Nat) (h : ord≤ps.card) :
    Wire.bits (fields o k msg ps ord)=3633*ord := by
  induction ord with
  | zero => rfl
  | succ n ih =>
    have lt : n<ps.card := by omega
    rw [next o k msg ps n lt,Wire.bits_append,ih (by omega),record,Encoding.record_bits];omega

theorem complete (o : Oracle) (k : Generator.Key) (msg : Message) (ps : Positions) :
    fields o k msg ps ps.card=CapIterate.records (LeafTree.tree o k msg) ps (HonestDelivery.salts o k ps) := by
  unfold fields CapIterate.records
  have len : (ps.sort (·≤·)).length=ps.card := by simp
  rw [←len,List.take_length]
  apply List.flatMap_congr
  intro i hi
  have mem : i∈ps := (Finset.mem_sort _).mp hi
  simp [record,publicOpenedSalts,mem,HonestDelivery.salts]

structure Progress (o : Oracle) (k : Generator.Key) (msg : Message) (trap : CommitStorage.Trapdoor) (ps : Positions)
    (ord : Nat) (s : MachineState) (m : Model) : Prop where
  pc : s.pc=(if ps.card-ord=0 then addr 1429 else addr 143)
  fits : Fits s m
  regs : Regs m ord (ps.card-ord) (Wire.bits (fields o k msg ps ord))
  live : Agrees m.mem (memoryView (HonestInputs.first trap ps))
  data : Serialized m.mem (Wire.pack (fields o k msg ps ord))

theorem run (o : Oracle) (k : Generator.Key) (msg : Message) (trap : CommitStorage.Trapdoor)
    (stored : CommitStorage.Stored o k msg trap) (ps : Positions) (positive : 0<ps.card) (ord : Nat) (h : ord≤ps.card) :
    ∃ s m n, n≤2000*ord ∧ CommitExact.Segment o OpeningStraight.image n (HonestInputs.first trap ps) s ∧
      Progress o k msg trap ps ord s m := by
  induction ord with
  | zero =>
    let a := HonestInputs.first trap ps
    obtain ⟨_,pc,_⟩ := HonestInputs.first_record trap ps positive 0
    refine ⟨a,OpeningReply.loaded a,0,by decide,CommitExact.empty o _ a,?_,OpeningReply.fits a,
      OpeningLoopRegs.start trap ps positive,fun _ _ => rfl,OpeningRead.initial trap ps positive⟩
    rw [Nat.sub_zero,if_neg (by omega)];exact pc
  | succ n ih =>
    have legal : n<ps.card := by omega
    obtain ⟨s,m,a,ab,sa,p⟩ := ih (by omega)
    have pc : s.pc=addr 143 := p.pc.trans (if_neg (by omega))
    let fs := fields o k msg ps n
    have limit : ps.card≤2^24 := by simpa only [Fintype.card_fin,LENGTH,LOG_LENGTH] using Finset.card_le_univ ps
    have room : (Wire.bits fs+3633)/64<capacity := by unfold fs;rw [bits o k msg ps n (by omega)];unfold capacity;omega
    obtain ⟨t,out,b,bb,sb,pt,ft,rt,lt,dt⟩ := OpeningRecordExecution.run o k msg trap stored ps n legal fs room m
      p.regs p.live p.data s pc p.fits
    refine ⟨t,out,a+b,by omega,CommitExact.compose sa sb,pt,ft,?_,lt,?_⟩
    · rw [bits o k msg ps (n+1) h]
      have e : Wire.bits fs+3633=3633*(n+1) := by unfold fs;rw [bits o k msg ps n (by omega)];omega
      exact e ▸ rt
    · rw [next o k msg ps n legal];exact dt

end CommitGolfCandidate.Reconstruction.OpeningRecordList
