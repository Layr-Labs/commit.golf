import CommitGolfCandidate.ReconstructedCapLoad
import CommitGolfCandidate.ReconstructedCapDigits

namespace CommitGolfCandidate.Reconstruction.CapPayload
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 TwoPermutationPrototype.RV64
open LeafModel Binding Encoding OpeningCursor
open CapLoad (word)
set_option maxRecDepth 14000
set_option maxHeartbeats 1700000

def mask (bits : Nat) : Word := W (2^bits-1)

theorem masked (x : Word) (k : Nat) (bound : k≤64) : (x &&& mask k).toNat=x.toNat%2^k := by
  have hi := Nat.pow_le_pow_right (n:=2) (by decide) bound
  have pos := Nat.two_pow_pos k
  rw [BitVec.toNat_and,mask,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show 2^k-1<2^64 by omega),Nat.and_two_pow_sub_one_eq_mod]

theorem raw_words (trap : CommitStorage.Trapdoor) (ps : Positions) (nonempty : 0<ps.card)
    (s : MachineState) (m : Model) (fit : Fits s m) (source : CapEntry.Source s trap ps)
    (d id : Nat) (positive : 0<d) (small : d≤9) (heap : CommitParents.Cell d id) :
    let r := fun k => m.mem (word d id k)
    OpeningNodes.raw trap d id = ((r 2++r 1)++r 0,r 3) := by
  let a := CommitParents.addr d id
  let initial := HonestInputs.first trap ps
  have width : 2^(d+1)≤2^10 := Nat.pow_le_pow_right (by decide) (by omega)
  have num : id<1024 := heap.2.2.trans_le width
  have physical (k : Fin 4) : m.mem (word d id k.val)=CommitParents.atWord initial (a+8*k.val) := by
    have h := fit.memory (word d id k.val) (by have b := k.isLt;unfold word CapLoad.heap;omega)
    rw [←h]
    change s.getMem (wordAddress (word d id k.val))=_
    rw [CapLoad.address]
    exact source.tree d id k.val positive small heap k.isLt
  have eq := OpeningNodes.from_abi trap ps nonempty d id heap
  change CommitParents.cell initial a=OpeningNodes.raw trap d id at eq
  rw [←eq,CommitParents.cell_words initial a (CommitParents.aligned d id)]
  change _=((m.mem (word d id 2)++m.mem (word d id 1))++m.mem (word d id 0),m.mem (word d id 3))
  have h0 : m.mem (word d id 0)=CommitParents.atWord initial a := physical ⟨0,by decide⟩
  have h1 : m.mem (word d id 1)=CommitParents.atWord initial (a+8) := physical ⟨1,by decide⟩
  have h2 : m.mem (word d id 2)=CommitParents.atWord initial (a+16) := physical ⟨2,by decide⟩
  have h3 : m.mem (word d id 3)=CommitParents.atWord initial (a+24) := physical ⟨3,by decide⟩
  rw [h0,h1,h2,h3]

private theorem lanes (x y z : Word) :
    (((z++y)++x).extractLsb' 0 64=x) ∧ (((z++y)++x).extractLsb' 64 64=y) ∧ (((z++y)++x).extractLsb' 128 64=z) := by
  refine ⟨BitVec.extractLsb'_append_eq_right,?_,?_⟩
  · rw [BitVec.extractLsb'_append_eq_of_le (by decide : 64≤64)]
    exact BitVec.extractLsb'_append_eq_right
  · rw [BitVec.extractLsb'_append_eq_of_le (by decide : 64≤128)]
    exact BitVec.extractLsb'_append_eq_left

structure Values (r : Nat→Word) (d : Nat) (node : Binding.Digest) : Prop where
  first : (r 0).toNat = Wire.clipped ⟨node.1.toNat,64⟩
  second : (r 1).toNat = Wire.clipped ⟨node.1.toNat >>> 64,64⟩
  third : (r 2).toNat = Wire.clipped ⟨node.1.toNat >>> 128,64⟩
  top : (r 3 &&& mask (lows d-192)).toNat = Wire.clipped ⟨node.2.toNat,lows d-192⟩
  digit : ((r 3 &&& mask (Binding.width d-192)) >>> (lows d-192)).toNat=highDigit node (lows d)

/-- The four loaded heap words, including retained child tags, yield the four low
fields and the optional high digit of the canonical committed node. -/
theorem canonical (o : Oracle) (key : Generator.Key) (msg : Message) (trap : CommitStorage.Trapdoor)
    (stored : CommitStorage.Stored o key msg trap) (ps : Positions) (nonempty : 0<ps.card)
    (s : MachineState) (m : Model) (fit : Fits s m) (source : CapEntry.Source s trap ps)
    (d : Fin 10) (id : Nat) (pos : 0<d.val) (heap : CommitParents.Cell d.val id) :
    Values (fun k => m.mem (word d.val id k)) d.val (LeafTree.tree o key msg d.val id) := by
  let r := fun k => m.mem (word d.val id k)
  let node := LeafTree.tree o key msg d.val id
  have dep := d.isLt
  let depth : Fin 25 := ⟨d.val,by omega⟩
  obtain ⟨lo,top,digit⟩ := OpeningNodes.fields o key msg trap stored depth id heap pos
  have raw := raw_words trap ps nonempty s m fit source d.val id pos (by omega) heap
  change OpeningNodes.raw trap d.val id=((r 2++r 1)++r 0,r 3) at raw
  change (OpeningNodes.raw trap d.val id).1=node.1 at lo
  change (OpeningNodes.raw trap d.val id).2.toNat%2^(lows d.val-192) = _ at top
  change ((OpeningNodes.raw trap d.val id).2.toNat%2^(Binding.width d.val-192)) >>> (lows d.val-192)=_ at digit
  rw [raw] at lo top digit
  have three := lanes (r 0) (r 1) (r 2)
  change (r 2++r 1)++r 0=node.1 at lo
  rw [lo] at three
  have sizes : lows d.val-192≤64 ∧ Binding.width d.val-192≤64 :=
    (by decide : ∀ j : Fin 10, lows j.val-192≤64 ∧ Binding.width j.val-192≤64) d
  refine ⟨?_,?_,?_,(masked (r 3) _ sizes.1).trans top,?_⟩
  · exact (congrArg BitVec.toNat three.1).symm.trans (by rw [BitVec.extractLsb'_toNat];rfl)
  · exact (congrArg BitVec.toNat three.2.1).symm.trans (by rw [BitVec.extractLsb'_toNat];rfl)
  · exact (congrArg BitVec.toNat three.2.2).symm.trans (by rw [BitVec.extractLsb'_toNat];rfl)
  · rw [BitVec.toNat_ushiftRight,masked _ _ sizes.2];exact digit

end CommitGolfCandidate.Reconstruction.CapPayload
