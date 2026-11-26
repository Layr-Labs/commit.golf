import CommitGolfCandidate.ReconstructedOpeningWordFields
import CommitGolfCandidate.ReconstructedCapWriter

namespace CommitGolfCandidate.Reconstruction.OpeningNodeStream
open CommitGolf RiscvZkvm.Rv64 OpeningWordFields OpeningHeaderAddress Encoding OpeningPut
open TwoPermutationPrototype (Memory)
set_option maxRecDepth 12000

def words (m : Memory) (i : Index) (d k : Nat) := m (wordAt i d k)

theorem decoded (m : Memory) (t : CommitStorage.Trapdoor) (ps : Positions) (ne : 0<ps.card) (mem : Heap m t ps)
    (o : Oracle) (k : Generator.Key) (msg : Message) (st : CommitStorage.Stored o k msg t)
    (i : Index) (d : Fin 25) (pos : 0<d.val) :
    CapPayload.Values (words m i d) d (LeafTree.tree o k msg d (sibling i d)) := by
  let node := LeafTree.tree o k msg d (sibling i d)
  let src := OpeningNodes.raw t d (sibling i d)
  have eq (j : Fin 4) : words m i d j=(Binding.pack src).extractLsb' (64*j.val) 64 :=
    word m t ps ne mem i d pos j
  obtain ⟨low,top,hi⟩ := OpeningNodes.fields o k msg t st d (sibling i d) (OpeningNodes.sibling_cell i d pos) pos
  change src.1=node.1 at low
  change src.2.toNat%2^(lows d-192)=node.2.toNat%2^(lows d-192) at top
  change (src.2.toNat%2^(Binding.width d-192)) >>> (lows d-192)=_ at hi
  have vtop : words m i d 3=src.2 := (eq (3 : Fin 4)).trans BitVec.extractLsb'_append_eq_left
  have vl (j : Fin 3) : words m i d j = node.1.extractLsb' (64*j.val) 64 := by
    have bound := j.isLt
    calc
      _ = (src.2 ++ src.1).extractLsb' (64*j.val) 64 := eq (⟨j.val,by omega⟩ : Fin 4)
      _ = src.1.extractLsb' (64*j.val) 64 := BitVec.extractLsb'_append_eq_of_add_le (by omega)
      _ = _ := congrArg (fun v : BitVec 192 => v.extractLsb' (64*j.val) 64) low
  have sz : lows d-192≤64 ∧ Binding.width d-192≤64 :=
    (by decide : ∀ j : Fin 25, lows j-192≤64 ∧ Binding.width j-192≤64) d
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact (congrArg BitVec.toNat (vl (0:Fin 3))).trans (by rw [BitVec.extractLsb'_toNat];rfl)
  · exact (congrArg BitVec.toNat (vl (1:Fin 3))).trans (by rw [BitVec.extractLsb'_toNat];rfl)
  · exact (congrArg BitVec.toNat (vl (2:Fin 3))).trans (by rw [BitVec.extractLsb'_toNat];rfl)
  · rw [vtop];exact (CapPayload.masked _ _ sz.1).trans top
  · rw [vtop,BitVec.toNat_ushiftRight,CapPayload.masked _ _ sz.2];exact hi

theorem serialize (m : Memory) (t : CommitStorage.Trapdoor) (ps : Positions) (ne : 0<ps.card) (mem : Heap m t ps)
    (o : Oracle) (k : Generator.Key) (msg : Message) (st : CommitStorage.Stored o k msg t)
    (i : Index) (d : Fin 25) (pos : 0<d.val) (fs : List Wire.Field) (valid : Serialized m (Wire.pack fs))
    (room : (Wire.bits fs+192)/64<capacity) :
    Serialized (CapWriter.lowMemory m (Wire.bits fs) d (words m i d))
      (Wire.pack (fs++lowFields (LeafTree.tree o k msg d (sibling i d)) (lows d))) :=
  CapWriter.low_all _ _ d _ _ (decoded m t ps ne mem o k msg st i d pos) valid room

end CommitGolfCandidate.Reconstruction.OpeningNodeStream
