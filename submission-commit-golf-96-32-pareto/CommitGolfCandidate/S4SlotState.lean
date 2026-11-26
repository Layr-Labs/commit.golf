import CommitGolfCandidate.S4SlotRun
import CommitGolfCandidate.S4BatchRows
namespace CommitGolfCandidate.S4.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (Trapdoor pcAt)
open Machine (W Runs proofBase)
def slotPart (td : Trapdoor) (ps : Positions) (j : Nat) := mainBytes (240,Late.slice td (slotAddress (indices ps) j) 32)
def batchPayload (td : Trapdoor) (ps : Positions) (n : Nat) :=
  returnedRecords td ps true 128 ++ (List.range n).flatMap (slotPart td ps)
theorem slotPartSize (td : Trapdoor) (ps : Positions) (j : Nat) : (slotPart td ps j).length=30:=by
  simp only [slotPart,mainBytes,List.length_map,List.length_range] <;> rfl
theorem batchMore (td : Trapdoor) (ps : Positions) (n : Nat) :
    batchPayload td ps (n+1)=batchPayload td ps n++slotPart td ps n := by
  simp only [batchPayload,List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc]
theorem batchPayloadSize (td : Trapdoor) (ps : Positions) (batch : ps.card=128) (n : Nat) :
    (batchPayload td ps n).length=65280+30*n:=by
  induction n with
  | zero=>simp only [batchPayload,List.range_zero,List.flatMap_nil,List.append_nil,returnedLen td ps true 128 batch.symm.le];rfl
  | succ n ih=>rw [batchMore,List.length_append,ih,slotPartSize];omega

structure SlotData (td : Trapdoor) (ps : Positions) (s : MachineState) (j : Nat) : Prop where
  dest : s.getReg .x19=W (slotOut j)
  sources : Sources td ps s
  bytes : Contains s proofBase (batchPayload td ps j)
  flags : Marked ps 128 s
structure SlotTile (td : Trapdoor) (ps : Positions) (s : MachineState) (t : Nat) extends SlotData td ps s (8*t) : Prop where
  pc : s.pc=pcAt (if t=21 then 5177 else 4903)
  left : s.getReg .x9=W (21-t)
  flagsPtr : s.getReg .x24=W (512+16*t)
  children : s.getReg .x22=W (Late.rowAddress 15 (8*t))
  parents : s.getReg .x23=W (Late.nodeAddress 16 (8*t))

private def setupSlotsOps := immediate3 .x22 (Late.rowAddress 15 0)++immediate3 .x23 (Late.nodeAddress 16 0)++[.addi .x9 .x0 21]
def setupSlots (s : MachineState) := Machine.Sym.evaluated setupSlotsOps s
private theorem setupCode : (Machine.Fragment.arithmetic setupSlotsOps).valid .opening 4892 4903 := by decide

theorem slotEntry (td : Trapdoor) (ps : Positions) (s : MachineState) (batch : ps.card=128) (rows : BatchCursor td ps s 128) :
    SlotTile td ps (setupSlots s) 0 ∧ Runs .opening s (setupSlots s) 11 11 := by
  have pc : s.pc=pcAt 4892:=rows.pc
  obtain ⟨run,regs,mem,endPC⟩:=Machine.evalMath .opening setupSlotsOps 4892 4903 s pc setupCode
    (fun c mem=>bne_iff_ne.mp (List.all_eq_true.mp (by decide : setupSlotsOps.all (fun c=>c.dst != .x0)=true) c mem))
    (fun _ member=>by cases member)
  let u:=setupSlots s
  have equal : u.mem=s.mem:=mem
  have flags : Marked ps 128 u:=by intro j bj;simpa only [Machine.byte,MachineState.getByte,MachineState.getMem,equal] using rows.marked j bj
  have payload : batchPayload td ps 0=returnedRecords td ps true 128:=by simp [batchPayload]
  refine ⟨⟨⟨(regs .x19).trans (by exact rows.dest),rows.sources.sameMem mem,payload.symm ▸ rows.bytes.mem mem,flags⟩,
    endPC,(regs .x9).trans rfl,(regs .x24).trans (by exact rows.flags),(regs .x22).trans rfl,(regs .x23).trans rfl⟩,run⟩

theorem afterSlot (td : Trapdoor) (ps : Positions) (batch : ps.card=128) (s z : MachineState)
    (t : Fin 22) (l : Fin 8) (tail : Bool) (inside : 8*t.val+l.val<171)
    (data : SlotData td ps s (8*t.val+l.val)) (h : SlotEnd tail l (8*t.val+l.val) (indices ps) s z) :
    SlotData td ps z (8*t.val+l.val+1) := by
  let j:=8*t.val+l.val
  have hi : j<171:=inside
  obtain ⟨lo,top,_⟩:=slotBounds (indices ps) j hi
  have fromBytes : Contains s (slotAddress (indices ps) j) (slotPart td ps j):=
    fieldRead (by decide : 30≤32) (data.sources.fixed _ 32 lo top)
  have len:=batchPayloadSize td ps batch j
  have source : Sources td ps z:=data.sources.moved h.moved (by unfold slotOut;omega)
  refine ⟨h.cursor,source,?_,untouchedFlags data.flags h.moved.frame (by unfold slotOut;omega)⟩
  rw [batchMore]
  apply data.bytes.copy fromBytes (slotPartSize ..)
  · rw [len];change Machine.Moved s z _ (proofBase+(65280+30*j)) 30
    exact Nat.add_assoc proofBase 65280 (30*j) ▸ h.moved
  · rw [len];unfold proofBase;omega
theorem SlotData.mem {td : Trapdoor} {ps : Positions} {s t : MachineState} {j : Nat}
    (d : SlotData td ps s j) (same : t.mem=s.mem) (ptr : t.getReg .x19=s.getReg .x19) : SlotData td ps t j:=by
  refine ⟨ptr.trans d.dest,d.sources.sameMem same,d.bytes.mem same,?_⟩
  intro q b;simpa only [Machine.byte,MachineState.getByte,MachineState.getMem,same] using d.flags q b
end CommitGolfCandidate.S4.Open
