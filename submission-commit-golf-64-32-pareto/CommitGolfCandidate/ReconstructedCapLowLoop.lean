import CommitGolfCandidate.ReconstructedCapLevelData

namespace CommitGolfCandidate.Reconstruction.CapLowLoop
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OpeningCursor OpeningPut LeafModel HonestCapPlan
open TwoPermutationPrototype.RV64
open HonestCapTables (addrSlot)
open CommitBlocks (addr)
set_option maxRecDepth 22000
set_option maxHeartbeats 2300000

structure Local (s : MachineState) (d n j : Nat) : Prop where
  pending : s.getReg .x20=W n
  index : s.getReg .x24=addrSlot j
  past : s.getReg .x25=addrSlot n
  width : s.getReg .x23=W (Encoding.lows d-192)
  mask : s.getReg .x22=CapPayload.mask (Encoding.lows d-192)
  table : s.getReg .x21=W (8*d)

theorem single (o : Oracle) (key : Generator.Key) (msg : Message) (trap : CommitStorage.Trapdoor) (ps : Positions)
    (stored : CommitStorage.Stored o key msg trap) (nonempty : 0<ps.card) (f : Nat→Bool)
    (d : Fin 10) (pos : 0<d.val) (ids : List Nat) (limit : ids.length≤256) (j : Nat) (sel : j < ids.length)
    (s : MachineState) (pc : s.pc=addr 1512) (fs : List Wire.Field) (data : CapLevelData.Packed s trap ps f d.val ids fs)
    (input : Local s d.val ids.length j) (bound : CommitParents.Cell d.val ids[j])
    (room : (Wire.bits fs+192)/64<capacity) :
    ∃ n t, n≤60 ∧ CommitExact.Segment o OpeningStraight.image n s t ∧
      t.pc=(if j+1=ids.length then addr 1581 else addr 1512) ∧ Local t d.val ids.length (j+1) ∧
      CapLevelData.Packed t trap ps f d.val ids (fs++CapSchedule.low (LeafTree.tree o key msg) d.val ids[j]) := by
  let m := CapFrame.state s
  have fit := CapFrame.fits s
  let idx : Fin 512 := ⟨j,by omega⟩
  let id := ids[j]
  have dep := d.isLt
  have sz : pairs d.val≤256 := HonestCapPlan.width_bound d.val (by omega)
  have hi : id<1024 := bound.2.2.trans_le (by exact Nat.pow_le_pow_right (by decide) (show d.val+1≤10 by omega))
  have gl := data.common.regs
  obtain ⟨n,t,out,length,emit,guard,ft,res⟩ := CapEmitNode.run o s m pc fit idx ids sel data.slots d id (Wire.bits fs) rfl hi room input.index
    data.depth (gl .x5 (W CapLoad.heap) (by decide)) data.buffer.cursor input.width input.mask (gl .x17 (W HonestRecordMemory.proofBase) (by decide))
    (gl .x28 65 (by decide))
  have fixed (r : Reg) (mem : r∈CapLowCore.fixed) (notPtr : r≠.x24) : t.getReg r=s.getReg r :=
    (ft.registers r).trans (res.preserved r mem notPtr)
  have registers : ∀ r∈CapLevelData.kept, t.getReg r=s.getReg r := by
    intro r mem
    simp only [CapLevelData.kept,List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with h|h|h|h|h|h|h|h|h|h|h|h <;> cases h <;> apply fixed <;> decide
  have newInput : Local t d.val ids.length (j+1) :=
    ⟨(fixed _ (by decide) (by decide)).trans input.pending,(ft.registers _).trans res.advance,
      (fixed _ (by decide) (by decide)).trans input.past,(fixed _ (by decide) (by decide)).trans input.width,
      (fixed _ (by decide) (by decide)).trans input.mask,(fixed _ (by decide) (by decide)).trans input.table⟩
  let gs := fs++CapSchedule.low (LeafTree.tree o key msg) d.val id
  have low := CapEmitNode.serialized o key msg trap stored ps nonempty s m out fit data.common.source d id j pos bound fs room data.buffer.output res
  have payload : CapEvidence.Buffer t gs := by
    refine ⟨?_,CapEvidence.serial _ _ ft gs low⟩
    have bits : Wire.bits gs=Wire.bits fs+192+(Encoding.lows d.val-192) := by
      rw [show gs=fs++Encoding.lowFields (LeafTree.tree o key msg d.val id) (Encoding.lows d.val) from rfl,
        Wire.bits_append,Encoding.low_bits];omega
    rw [bits];exact (ft.registers _).trans res.cursor
  have newData := CapLevelData.change s t trap ps f d.val ids fs gs data sz (by omega) payload registers
    (CapFrame.emitted s t m out fit ft (Wire.bits fs) d.val id j res room)
  have g := CapLevelData.emit_guard o t guard (j+1) ids.length (by omega) limit newInput.index newInput.past
  exact ⟨n+1,_,by omega,CommitExact.compose emit g,rfl,⟨newInput.pending,newInput.index,newInput.past,newInput.width,newInput.mask,newInput.table⟩,
    CapLevelData.jump t trap ps f d.val ids gs newData _ sz (by omega)⟩

theorem loop (o : Oracle) (key : Generator.Key) (msg : Message) (trap : CommitStorage.Trapdoor) (ps : Positions)
    (stored : CommitStorage.Stored o key msg trap) (nonempty : 0<ps.card) (f : Nat→Bool)
    (d : Fin 10) (pos : 0<d.val) (ids : List Nat) (size : ids.length≤256)
    (bounds : ∀ id∈ids, CommitParents.Cell d.val id)
    (todo done_ : List Nat) (split : ids=done_++todo) (s : MachineState)
    (pc : s.pc=(if todo=[] then addr 1581 else addr 1512)) (fs : List Wire.Field)
    (data : CapLevelData.Packed s trap ps f d.val ids fs) (input : Local s d.val ids.length done_.length)
    (room : Wire.bits (fs++todo.flatMap (CapSchedule.low (LeafTree.tree o key msg) d.val))+192<capacity*64) :
    ∃ n t, n≤60*todo.length ∧ CommitExact.Segment o OpeningStraight.image n s t ∧ t.pc=addr 1581 ∧
      Local t d.val ids.length ids.length ∧
      CapLevelData.Packed t trap ps f d.val ids (fs++todo.flatMap (CapSchedule.low (LeafTree.tree o key msg) d.val)) := by
  induction todo generalizing done_ s fs with
  | nil =>
    have len : ids.length=done_.length := by rw [split,List.append_nil]
    simp only [List.flatMap_nil,List.append_nil]
    exact ⟨0,s,by omega,CommitExact.empty _ _ _,pc,by rw [len] at input ⊢;exact input,data⟩
  | cons id tail ih =>
    let node := CapSchedule.low (LeafTree.tree o key msg) d.val
    have index : done_.length < ids.length := by rw [split,List.length_append,List.length_cons];omega
    have which : ids[done_.length]'index=id := by
      have access : (done_++id::tail)[done_.length]'(by simp)=id := by simp
      simpa only [split] using access
    have truePc : s.pc=addr 1512 := by simpa only [List.cons_ne_nil,ite_false] using pc
    obtain ⟨k,u,cost,advance,pcU,loopU,dataU⟩ := single o key msg trap ps stored nonempty f d pos ids size done_.length index s truePc fs data input
      (bounds _ (List.getElem_mem _)) (CapSchedule.prefix_room fs _ room)
    rw [which] at dataU
    have nextEq : ids=(done_++[id])++tail := by simp [split,List.append_assoc]
    have set : done_.length+1=ids.length ↔ tail=[] := by
      rw [split,List.length_append,List.length_cons,←List.length_eq_zero_iff];omega
    have pcu : u.pc=(if tail=[] then addr 1581 else addr 1512) := by simpa only [set] using pcU
    have nextInput : Local u d.val ids.length (done_++[id]).length := by simpa only [List.length_append,List.length_singleton] using loopU
    have limit : Wire.bits ((fs++node id)++tail.flatMap node)+192<capacity*64 := by
      simpa only [List.append_assoc,List.flatMap_cons] using room
    obtain ⟨n,t,more,walk,endPC,last,output⟩ := ih (done_++[id]) nextEq u pcu (fs++node id) dataU nextInput limit
    refine ⟨k+n,t,by simp only [List.length_cons];omega,CommitExact.compose advance walk,endPC,last,?_⟩
    simpa only [List.append_assoc,List.flatMap_cons] using output

end CommitGolfCandidate.Reconstruction.CapLowLoop
