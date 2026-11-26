import CommitGolfCandidate.ReconstructedCapGroupStart
import CommitGolfCandidate.ReconstructedCapHeaderFold
import CommitGolfCandidate.ReconstructedCapLevelData

namespace CommitGolfCandidate.Reconstruction.CapHeaderPiece
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OpeningCursor OpeningPut LeafModel
open TwoPermutationPrototype.RV64
open CommitBlocks (addr)
set_option maxRecDepth 22000
set_option maxHeartbeats 2000000

structure Local (s : MachineState) (d n j : Nat) : Prop where
  count : s.getReg .x20=W n
  index : s.getReg .x21=W j
  back : s.getReg .x22=W j-1
  rem : s.getReg .x24=W (n-j)
  mask : s.getReg .x23=CapPayload.mask (Binding.width d-192)
  headerMask : s.getReg .x29=CapPayload.mask 31
  two : s.getReg .x26=2

theorem add_four (j : Fin 257) : CapWordStep.imm (W j.val) 4=W (j.val+4) :=
  (by decide : ∀ k : Fin 257, CapWordStep.imm (W k.val) 4=W (k.val+4)) j

theorem sub_four (r : Fin 257) (hi : 4≤r.val) : CapWordStep.imm (W r.val) 4092=W (r.val-4) :=
  (by decide : ∀ k : Fin 257, 4≤k.val → CapWordStep.imm (W k.val) 4092=W (k.val-4)) r hi

theorem guard (o : Oracle) (s : MachineState) (pc : s.pc=addr 1602) (j n : Nat) (size : n≤256) (bound : j≤260)
    (index : s.getReg .x21=W j) (count : s.getReg .x20=W n) :
    CommitExact.Segment o OpeningStraight.image 1 s (s.setPC (if j<n then addr 1603 else addr 1449)) := by
  apply CommitExact.plain o _ _ _ (.base (.BGEU .x21 .x20 7580)) (OpeningStraight.fetched 1602 _ (by decide) rfl s pc)
  simp only [ordinaryStep,memoryArgumentsValid,memAccess,ite_true,execInstrBr,pc,index,count,
    HonestCapState.unsigned (by omega : j<2^64) (by omega : n<2^64)]
  by_cases h : j<n <;> simp only [h,decide_true,decide_false,Bool.false_eq_true,
    ite_true,ite_false] <;> rfl

theorem foldData (o : Oracle) (key : Generator.Key) (msg : Message) (trap : CommitStorage.Trapdoor) (ps : Positions)
    (storage : CommitStorage.Stored o key msg trap) (nonempty : 0<ps.card) (f : Nat→Bool) (d : Fin 10) (paid : 8≤d.val)
    (xs g : List Nat) (at_ : Nat) (s : MachineState) (fs : List Wire.Field) (full : CapLevelData.Packed s trap ps f d.val xs fs)
    (local_ : Local s d.val xs.length at_) (small : xs.length≤256) (span : at_+g.length≤xs.length)
    (select : ∀ i : Fin g.length, xs[at_+i.val]'(by have h:=i.isLt;omega)=g[i.val])
    (cells : ∀ i∈g, CommitParents.Cell d.val i) :
    CapHeaderFold.Data (CapFrame.state s) d xs g at_ (CapSchedule.digit (LeafTree.tree o key msg) d.val) := by
  have named := full.common.regs
  have depth := d.isLt
  refine ⟨named .x9 (W HonestCapTables.scratch) (by decide),full.depth,named .x18 (W (CapLoad.heap+24)) (by decide),
    named .x31 (W 211) (by decide),full.slots,span,by omega,select,?_,?_⟩
  · intro i h;exact (cells i h).2.2.trans_le (Nat.pow_le_pow_right (by decide) (show d.val+1≤10 by omega))
  · intro i member
    have value := (CapPayload.canonical o key msg trap storage ps nonempty s (CapFrame.state s) (CapFrame.fits s)
      full.common.source d i (by omega) (cells i member)).digit
    have width : Encoding.lows d.val-192=32 := (by decide : ∀ k : Fin 10, 8≤k.val → Encoding.lows k.val-192=32) d paid
    change ((s.getReg .x23 &&& memoryView s (CapLoad.word d.val i 3)) >>> (32:Nat)).toNat=_
    rw [local_.mask,BitVec.and_comm,←width];exact value

structure Written (s t : MachineState) (fs : List Wire.Field) (hdr : Nat) (d n j : Nat) : Prop where
  buf : CapEvidence.Buffer t (fs++[⟨hdr,31⟩])
  mem : ∀ a, a<2^33 → CapEmitNode.outside a → memoryView t a=memoryView s a
  kept : ∀ r∈CapLevelData.kept, t.getReg r=s.getReg r
  count : t.getReg .x20=W n
  next : t.getReg .x21=W (j+4)
  back : t.getReg .x22=W (j+4)-1
  pending : 4≤n-j → t.getReg .x24=W (n-(j+4))
  mask : t.getReg .x23=CapPayload.mask (Binding.width d-192)
  headerMask : t.getReg .x29=CapPayload.mask 31
  two : t.getReg .x26=2

theorem run (o : Oracle) (s : MachineState) (d : Fin 10) (xs g : List Nat) (j : Nat) (dig : Nat→Nat) (fs : List Wire.Field)
    (pc : s.pc=addr 1603) (local_ : Local s d.val xs.length j) (input : CapHeaderFold.Data (CapFrame.state s) d xs g j dig)
    (baseReg : s.getReg .x17=wordAddress base) (test : s.getReg .x19=34) (buf : CapEvidence.Buffer s fs)
    (room : Wire.bits fs/64<capacity) (cap : xs.length≤256) (inside : j < xs.length) (groupSize : g.length=min 4 (xs.length-j)) :
    ∃ n t, n≤26+16*g.length ∧ CommitExact.Segment o OpeningStraight.image n s t ∧ t.pc=addr 1602 ∧
      Written s t fs (Encoding.headerValue dig g) d.val xs.length j := by
  let m := CapFrame.state s
  let left := xs.length-j
  let a := CapGroupStart.result m left
  have small : g.length≤4 := by rw [groupSize];omega
  have pos : 0<g.length := by rw [groupSize];omega
  have step : g.length-1+1=g.length := by omega
  have group : g.length=min 4 left := groupSize
  obtain ⟨k,u,less,beginRun,loc,fit⟩ := CapGroupStart.run o m s pc (CapFrame.fits s) left (by dsimp [left];omega) local_.rem
  obtain ⟨memA,zero,remain,ptr,firstReg⟩ := CapGroupStart.values m left j (by dsimp [left];omega) rfl local_.rem local_.back
  have baseData : CapHeaderFold.Data a d xs g j dig := by
    refine ⟨?_,?_,?_,?_,?_,input.contains,input.size,input.group,input.small,?_⟩
    · exact (firstReg _ (by decide) (by decide) (by decide) (by decide)).trans input.base
    · exact (firstReg _ (by decide) (by decide) (by decide) (by decide)).trans input.depth
    · exact (firstReg _ (by decide) (by decide) (by decide) (by decide)).trans input.heap
    · exact (firstReg _ (by decide) (by decide) (by decide) (by decide)).trans input.radix
    · exact memA ▸ input.slots
    · intro i h
      change (((CapGroupStart.result m left).reg .x23 &&& (CapGroupStart.result m left).mem _) >>> (32:Nat)).toNat=_
      rw [firstReg _ (by decide) (by decide) (by decide) (by decide),memA];exact input.encoded i h
  have ptrA : a.reg .x25=W (j+(g.length-1)) := by rw [←group] at ptr;rw [show j+(g.length-1)=j+g.length-1 by omega];exact ptr
  have remA : a.reg .x30=CapHeaderDigit.neg (g.length-1+1) := by rw [step,group];exact remain
  have acc : a.reg .x16=W (Encoding.headerValue dig (g.drop (g.length-1+1))) := by rw [step,List.drop_length];exact zero
  obtain ⟨v,b,body,pcV,fb,summed⟩ := CapHeaderFold.fold o d xs g j dig (g.length-1) small (by omega) a u loc fit baseData ptrA remA acc
  rw [step] at body
  have original (r : Reg) (keep : r∈CapHeaderDigit.keep) : b.reg r=s.getReg r := by
    apply (summed.regs _ keep).trans
    simp only [CapHeaderDigit.keep,List.mem_cons,List.not_mem_nil,or_false] at keep
    rcases keep with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> cases h <;> apply firstReg <;> decide
  have memB : b.mem=memoryView s := summed.mem.trans memA
  obtain ⟨h,t,out,hbound,write,pcT,ft,fresh⟩ := CapHeaderFlush.run o b v pcV fb (Wire.bits fs) room
    ((original _ (by decide)).trans buf.cursor) ((original _ (by decide)).trans baseReg) ((original _ (by decide)).trans test)
  have finalReg (r : Reg) (keep : r∈CapHeaderFlush.retained) : t.getReg r=s.getReg r := by
    apply ((ft.registers _).trans (fresh.regs _ keep)).trans
    apply original
    simp only [CapHeaderFlush.retained,List.mem_cons,List.not_mem_nil,or_false] at keep
    rcases keep with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> cases h <;> decide
  let hdr := Encoding.headerValue dig g
  refine ⟨k+16*g.length+h,t,by omega,CommitExact.compose (CommitExact.compose beginRun body) write,pcT,?_,?_,?_,
    (finalReg _ (by decide)).trans local_.count,?_,?_,?_,(finalReg _ (by decide)).trans local_.mask,
    (finalReg _ (by decide)).trans local_.headerMask,(finalReg _ (by decide)).trans local_.two⟩
  · refine ⟨?_,CapEvidence.serial t out ft _ ?_⟩
    · have cursor := (ft.registers _).trans fresh.cursor
      rw [Wire.bits_append];exact cursor
    · exact CapHeaderFlush.serialized b out fs hdr summed.value ((original _ (by decide)).trans local_.headerMask) fresh
        (memB ▸ buf.output) room
  · intro q bound loc
    have fitOut := ft.memory q bound
    rw [fitOut,fresh.memory,OpeningPut.keep]
    · exact congrFun memB q
    · unfold CapEmitNode.outside at loc;unfold cell;omega
    · unfold CapEmitNode.outside at loc;unfold cell;omega
  · intro r keep
    apply finalReg
    simp only [CapLevelData.kept,List.mem_cons,List.not_mem_nil,or_false] at keep
    rcases keep with h|h|h|h|h|h|h|h|h|h|h|h <;> cases h <;> decide
  · rw [ft.registers,fresh.group,original _ (by decide),local_.index];exact add_four ⟨j,by omega⟩
  · rw [ft.registers,fresh.back,original _ (by decide),local_.back]
    exact (by decide : ∀ i : Fin 257, W i.val-1+4=W (i.val+4)-1) ⟨j,by omega⟩
  · intro hpos
    rw [ft.registers,fresh.pending,original _ (by decide),local_.rem]
    have z := sub_four ⟨xs.length-j,by omega⟩ hpos
    simpa only [Nat.sub_sub] using z

end CommitGolfCandidate.Reconstruction.CapHeaderPiece
