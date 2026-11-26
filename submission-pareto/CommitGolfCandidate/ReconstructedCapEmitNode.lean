import CommitGolfCandidate.ReconstructedCapEmit

namespace CommitGolfCandidate.Reconstruction.CapEmitNode
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel OpeningPut OpeningCursor
open TwoPermutationPrototype.RV64
open CommitBlocks (addr)
open HonestCapTables (addrSlot)
set_option maxRecDepth 18000
set_option maxHeartbeats 1700000

def outside (i : Nat) := i < base ∨ base+capacity < i

theorem keep (m : TwoPermutationPrototype.Memory) (c d : Nat) (r : Nat→Word)
    (room : (c+192)/64<capacity) (i : Nat) (frozen : outside i) : CapWriter.lowMemory m c d r i=m i := by
  have loc (k : Nat) (bound : k≤192) : i≠cell (c+k) ∧ i≠cell (c+k)+1 := by
    unfold outside at frozen;unfold cell;omega
  obtain ⟨z,n⟩ := loc 0 (by decide)
  simp only [Nat.add_zero] at z n
  rw [CapWriter.lowMemory,OpeningPut.keep _ _ _ _ _ (loc 192 (by decide)).1 (loc 192 (by decide)).2,
    OpeningPut.keep _ _ _ _ _ (loc 128 (by decide)).1 (loc 128 (by decide)).2,
    OpeningPut.keep _ _ _ _ _ (loc 64 (by decide)).1 (loc 64 (by decide)).2,OpeningPut.keep _ _ _ _ _ z n]

structure Result (m t : Model) (c d id j : Nat) : Prop where
  data : t.mem=CapWriter.lowMemory m.mem c d (fun k => m.mem (CapLoad.word d id k))
  cursor : t.reg .x7=W (c+192+(Encoding.lows d-192))
  advance : t.reg .x24=addrSlot (j+1)
  preserved : ∀ r∈CapLowCore.fixed, r≠.x24 → t.reg r=m.reg r

theorem run (o : Oracle) (s : MachineState) (m : Model) (pc : s.pc=addr 1512) (fit : Fits s m)
    (idx : Fin 512) (ids : List Nat) (slot : idx.val < ids.length) (retained : CapSlots.Contains m.mem ids)
    (d : Fin 10) (id c : Nat) (which : ids[idx.val]=id) (small : id<1024)
    (room : (c+192)/64<capacity)
    (ptr : m.reg .x24=addrSlot idx.val) (dep : m.reg .x10=W d.val) (heap : m.reg .x5=W CapLoad.heap)
    (cursor : m.reg .x7=W c) (width : m.reg .x23=W (Encoding.lows d.val-192))
    (mask : m.reg .x22=CapPayload.mask (Encoding.lows d.val-192)) (output : m.reg .x17=wordAddress base) (thresh : m.reg .x28=65) :
    ∃ n t out, n≤59 ∧ CommitExact.Segment o OpeningStraight.image n s t ∧ t.pc=addr 1511 ∧ Fits t out ∧
      Result m out c d.val id idx.val := by
  let a := CapLoad.finish m d.val id
  have depLim := d.isLt
  obtain ⟨u,fetch,p,f⟩ := CapLoad.run o s m pc fit idx ids slot retained d.val id which small (by omega) ptr dep heap
  have size : Encoding.lows d.val-192≤64 := (by decide : ∀ b : Fin 10, Encoding.lows b.val-192≤64) d
  obtain ⟨n,t,out,length,emitted,loc,post,enc⟩ := CapEmit.one o a u p f c _ size room cursor width output thresh
  refine ⟨9+n,t,out,by omega,CommitExact.compose fetch emitted,loc,post,?_,enc.cursor,?_,?_⟩
  · have top : CapLowCore.top a=m.mem (CapLoad.word d.val id 3) &&& CapPayload.mask (Encoding.lows d.val-192) := by
      change m.mem (CapLoad.word d.val id 3) &&& m.reg .x22 = _;rw [mask]
    rw [enc.memory,CapEmit.encode,top];rfl
  · rw [enc.advance,show a.reg .x24=addrSlot idx.val from ptr]
    change W (HonestCapTables.scratch+4*idx.val)+W 4=W (HonestCapTables.scratch+4*(idx.val+1))
    rw [←BitVec.ofNat_add];apply congrArg W;omega
  · intro r member ne
    apply (enc.keep r member ne).trans
    obtain ⟨_,_,_,_,_,frame⟩ := CapLoad.words m d.val id
    simp only [CapLowCore.fixed,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> cases h <;>
      apply frame <;> decide

theorem serialized (o : Oracle) (key : Generator.Key) (msg : Message) (trap : CommitStorage.Trapdoor)
    (stored : CommitStorage.Stored o key msg trap) (ps : Positions) (nonempty : 0<ps.card)
    (s : MachineState) (m out : Model) (fit : Fits s m) (source : CapEntry.Source s trap ps)
    (d : Fin 10) (id j : Nat) (pos : 0<d.val) (bound : CommitParents.Cell d.val id)
    (fs : List Wire.Field) (room : (Wire.bits fs+192)/64<capacity)
    (before : Serialized m.mem (Wire.pack fs)) (emits : Result m out (Wire.bits fs) d.val id j) :
    Serialized out.mem (Wire.pack (fs++Encoding.lowFields (LeafTree.tree o key msg d.val id) (Encoding.lows d.val))) := by
  rw [emits.data]
  apply CapWriter.low _ _ d _ _ _ before room
  exact CapPayload.canonical o key msg trap stored ps nonempty s m fit source d id pos bound

end CommitGolfCandidate.Reconstruction.CapEmitNode
