import CommitGolfCandidate.GroupOpenWholePack
import CommitGolfCandidate.GroupOpenPrefix

namespace TwoPermutationPrototype.GroupedOpening.Whole
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 PackedOpening
open Wide Shifted30 CapCopy
attribute [local simp] MachineState.getReg_setPC Opening.getReg_setReg
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

def headLen (l : Nat) := if l=0 then 1 else 3
def nodeHead (l : Nat) (s : MachineState) := if l=0 then execInstrBr s (.LD .x7 .x7 128) else headPrefix s 3
def point (c l : Nat) := if l=14 then row c 22 else row c (7+l)
def tailAt (c l : Nat) := packStart c l+packCost l
def fixedTail (l : Nat) (s : MachineState) := if l=13 then
  execCode s [.ADDI .x21 .x21 534,.SRLI .x6 .x6 1]
  else execInstrBr s (.SRLI .x6 .x6 1)
def step (c : Nat) (l : Fin 14) (s : MachineState) :=
  fixedTail l (pack l (copy c (4+l.val) (nodeHead l s)))

private theorem end_code (c : Fin 4) : Slice (row c 21) [.ADDI .x21 .x21 534,.SRLI .x6 .x6 1] ∧
    row c 21+2=row c 22 ∧ row c 22<7872 := by revert c;decide +kernel

theorem node_layout (c : Fin 4) (l : Fin 14) :
    rawStart c (4+l.val)=row c (7+l.val)+headLen l ∧ source (4+l.val)=.x7 ∧ offset (4+l.val)=siblingOffset l ∧
    width (4+l.val)=plainWidth l ∧ row c (7+l.val)<7872 ∧
    (l.val=13 → tailAt c l=row c 21) ∧
    (l.val≠13 → tailAt c l+1=row c (8+l.val)) ∧
    point c (l.val+1)-point c l =
      headLen l+(shape c (4+l.val)).cycles+packCost l+(if l.val=13 then 2 else 1) := by
  revert c l;decide

theorem node_codes (c : Fin 4) (l : Fin 14) :
    (l.val=0 → Decodes (row c (7+l.val)) (.LD .x7 .x7 128)) ∧
    (l.val≠0 → Slice (row c (7+l.val)) headCode) ∧
    (l.val≠13 → Decodes (tailAt c l) (.SRLI .x6 .x6 1)) := by
  revert l;fin_cases c <;> decide +kernel

def ZeroInput (s : MachineState) (i : Index) :=
  s.getReg .x7=BitVec.ofNat 64 (groupSlots+1024*(i.val/4)+584) ∧
  s.getMem (BitVec.ofNat 64 (pointerAddress i.val))=BitVec.ofNat 64 (quadAddress i.val)

private theorem head_result (c : Fin 4) (l : Fin 14) (s : MachineState) (i : Index)
    (pc : s.pc=pcAt (row c (7+l.val))) (heap : s.getReg .x9=BitVec.ofNat 64 trapdoorBase)
    (node : s.getReg .x6=BitVec.ofNat 64 (upperNode i l)) (ptr : l.val=0 → ZeroInput s i) :
    let h:=nodeHead l s
    RunsOpeningBlock s h (headLen l) ∧ h.pc=pcAt (rawStart c (4+l.val)) ∧ h.mem=s.mem ∧
      h.getReg .x7=BitVec.ofNat 64 (siblingAddress i l) ∧ ∀ r,r≠.x7 → h.getReg r=s.getReg r := by
  have lay:=node_layout c l
  have codes:=node_codes c l
  by_cases z : l.val=0
  · obtain ⟨slot,pointer⟩:=ptr z
    have facts:=pointer_address_inside i.val i.isLt
    have addr : s.getReg .x7+signExtend12 (128#12)=BitVec.ofNat 64 (pointerAddress i.val) := by
      rw [slot,show signExtend12 (128#12)=BitVec.ofNat 64 128 from rfl,←BitVec.ofNat_add];unfold pointerAddress;congr 1
    have valid : accessValid (BitVec.ofNat 64 (pointerAddress i.val)) 8=true :=
      Opening.aligned_access _ facts.1 (le_trans facts.2.2 (by decide : nonceBase≤MEMORY_BYTES))
    have ran:=run_step s _ _ lay.2.2.2.2.1 pc (codes.1 z) rfl
      (by change accessValid (s.getReg .x7+signExtend12 (128#12)) 8=true;rw [addr];exact valid)
    simp only [nodeHead,headLen,if_pos z]
    refine ⟨ran,?_,rfl,?_,?_⟩
    · change s.pc+4=_
      rw [pc,lay.1];simp only [headLen,if_pos z];exact ofNat_four _
    · simp [execInstrBr,addr,pointer,z,siblingAddress]
    · intro r ne;simp [execInstrBr,Ne.symm ne]
  · have h:=sibling_head_post s
    have run : RunsOpeningBlock s (headPrefix s 3) 3 := pure_run s _ headCode (codes.2.1 z)
      ((show ∀ c : Fin 4, ∀ l : Fin 14, row c (7+l.val)+3≤7872 from by decide) c l)
      pc (by decide)
    simp only [nodeHead,headLen,if_neg z]
    refine ⟨run,?_,h.2.1,physical_sibling_source s i l z heap node,h.2.2.2⟩
    rw [h.1,pc,lay.1];simp only [headLen,if_neg z];exact ofNat_step _ 3

private theorem finish_result (c : Fin 4) (l : Fin 14) (s : MachineState)
    (pc : s.pc=pcAt (tailAt c l)) :
    let u:=fixedTail l s
    RunsOpeningBlock s u (if l.val=13 then 2 else 1) ∧
    u.pc=(if l.val+1=14 then pcAt (row c 22) else pcAt (row c (7+(l.val+1)))) ∧
    u.mem=s.mem ∧ u.getReg .x21=s.getReg .x21+BitVec.ofNat 64 (if l.val=13 then 534 else 0) ∧
    u.getReg .x6=s.getReg .x6 >>> 1 ∧
    ∀ r, r≠.x21 → r≠.x6 → u.getReg r=s.getReg r := by
  have eqs:=(node_layout c l).2.2.2.2.2
  by_cases last : l.val=13
  · obtain ⟨rows,dest,fit⟩:=end_code c
    let mid := execCode s [.ADDI .x21 .x21 534,.SRLI .x6 .x6 1]
    have start : s.pc=pcAt (row c 21) := pc.trans (congrArg pcAt (eqs.1 last))
    have ran : RunsOpeningBlock s mid 2 := pure_run s _ _ rows (by change _+2≤_;omega) start (by decide)
    have pcJ : mid.pc=pcAt (row c 22) := by change s.pc+4+4=_;rw [start,BitVec.add_assoc,←dest];exact ofNat_step _ 2
    simp only [fixedTail,if_pos last,if_pos (show l.val+1=14 by omega)]
    refine ⟨ran,pcJ,rfl,rfl,rfl,?_⟩
    intro r a b; simp [execCode,execInstrBr,Ne.symm a,Ne.symm b]
  · have fit : tailAt c l<7872 := pack_fit c l
    have ran:=run_step s _ _ fit pc ((node_codes c l).2.2 last) rfl rfl
    simp only [fixedTail,if_neg last,if_neg (show l.val+1≠14 by omega)]
    refine ⟨ran,?_,rfl,?_,rfl,?_⟩
    · change s.pc+4=_;rw [pc]
      exact (ofNat_four _).trans (congrArg pcAt (by rw [eqs.2.1 last];congr 1;omega))
    · simp [execInstrBr]
    · intro r a b;simp [execInstrBr,Ne.symm b]

structure NodeResult (s u : MachineState) (i : Index) (o : Nat) (l : Fin 14) : Prop where
  run : RunsOpeningBlock s u (point (pageClass o) (l.val+1)-point (pageClass o) l)
  next : WholeCursor u i o (l.val+1)
  kept : ∀ r, r≠.x6 → r≠.x7 → r≠.x21 → r≠.x31 → r≠.x29 → r≠.x11 → u.getReg r=s.getReg r
  input : ∀ a<proofBase, u.getMem (BitVec.ofNat 64 a)=s.getMem (BitVec.ofNat 64 a)
  frame : ∀ a<2^64, a<siblingDestination o l ∨ siblingDestination o (l.val+1)≤a →
    u.getByte (BitVec.ofNat 64 a)=s.getByte (BitVec.ofNat 64 a)
  bytes : ∀ b<siblingWidth l, u.getByte (BitVec.ofNat 64 (siblingDestination o l+b))=payload s i l b

theorem node_result (s : MachineState) (i : Index) (o : Nat) (l : Fin 14) (bound : o<LENGTH)
    (cur : WholeCursor s i o l) (ptr : l.val=0 → ZeroInput s i) :
    NodeResult s (step (pageClass o) l s) i o l := by
  let c : Fin 4:=⟨pageClass o,class_lt o⟩
  let f : Fin 18:=⟨4+l.val,by have := l.isLt;omega⟩
  let h:=nodeHead l s
  let m:=copy c f h
  let p:=pack l m
  let u:=step c l s
  let S:=siblingAddress i l
  let T:=siblingDestination o l
  have lays:=node_layout c l
  obtain ⟨_,src,off,size,_,_,_,price⟩:=lays
  have fits:=all_sibling_copies_fit i o l bound l.isLt
  have nle:=plain_width_le l
  have goalEnd : siblingDestination o (l.val+1)=T+siblingWidth l := by
    unfold T siblingDestination;rw [sibling_offset_next l l.isLt,Nat.add_assoc]
  have ram : MEMORY_BYTES<2^64 := by decide
  have srcBounds:=sibling_address_inside i l
  have tailBound:=nonces_end_at_indices
  have order:=indices_before_records
  have srcLow : S+32<proofBase := by
    have gap : nonceBase<proofBase := by decide
    exact lt_of_le_of_lt srcBounds.2.2 gap
  have srcFit : S+32≤MEMORY_BYTES := le_trans srcBounds.2.2 (by decide : nonceBase≤MEMORY_BYTES)
  have base : proofBase≤T := by unfold T siblingDestination recordBase;omega
  have pc : s.pc=pcAt (row c (7+l.val)) := by simpa only [if_neg (show l.val≠14 by have:=l.isLt;omega)] using cur.pc
  obtain ⟨runH,pcH,memH,srcH,keepH⟩ := head_result c l s i pc cur.heap cur.node ptr
  have baseReg : s.getReg .x21=BitVec.ofNat 64 (recordBase o) := by
    simpa only [if_neg (show l.val≠14 by have:=l.isLt;omega),Nat.add_zero] using cur.dest
  have addr : s.getReg .x21+BitVec.ofNat 64 (siblingOffset l)=BitVec.ofNat 64 T := by
    rw [baseReg,←BitVec.ofNat_add];rfl
  have field:=field_copy c f h S T pcH (by rw [src];exact srcH)
    (by rw [off,show h.getReg .x21=_ from keepH .x21 (by decide)];exact addr)
    srcBounds.1 (sibling_residue o l l.isLt)
    (by omega)
    (by change T+width (4+l.val)≤MEMORY_BYTES;rw [size];have:=fits.2.2.2;omega)
  have inM (a : Nat) (lo : a<proofBase) : m.getMem (BitVec.ofNat 64 a)=s.getMem (BitVec.ofNat 64 a) :=
    (Whole.beforeProof field a lo base).trans (by simp only [MachineState.getMem,memH,h])
  have regM (r : Reg) (a : r≠.x31) (b : r≠.x7) (d : r≠.x29) (e : r≠.x11) : m.getReg r=s.getReg r :=
    (field.regs r ⟨a,d,e⟩).trans (keepH r b)
  have full (fold : folded l) : siblingWidth l=30 := by unfold folded at fold; simp [siblingWidth,show ¬l.val<2 by omega, show l.val<13 by omega]
  have pRes:=pack_result c l m S T field.pc ((field.regs _ (by decide)).trans srcH)
    (by rw [regM _ (by decide) (by decide) (by decide) (by decide)];exact addr) srcBounds.1 fits.2.1 srcFit
    (by intro fld;have := fits.2.2.2;rw [full fld] at this;exact this)
  obtain ⟨runU,pcU,memU,destU,nodeU,keepU⟩:=finish_result c l p pRes.pc
  have kept (r : Reg) (a : r≠.x6) (b : r≠.x7) (cc : r≠.x21) (d : r≠.x31) (e : r≠.x29) (f : r≠.x11) : u.getReg r=s.getReg r :=
    (keepU r cc a).trans ((pRes.regs r d e).trans (regM r d b e f))
  have tagEq : tag m S l=tag s S l := by unfold tag;rw [half_from_words inM _ (by omega),regM _ (by decide) (by decide) (by decide) (by decide)]
  have mem : u.mem=if folded l then (m.setHalfword (BitVec.ofNat 64 (T+28)) (tag s S l)).mem else m.mem := by
    rw [←tagEq];exact memU.trans pRes.mem
  have tf : T+siblingWidth l≤MEMORY_BYTES:=fits.2.2.2
  refine ⟨?_,⟨pcU,(kept _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans cur.heap,?_,?_⟩,
    kept,?_,?_,?_⟩
  · have total:=((runH.next field.run).next pRes.run).next runU
    change RunsOpeningBlock s u ((headLen l+(shape c (4+l.val)).cycles+packCost l)+(if l.val=13 then 2 else 1)) at total
    change RunsOpeningBlock s u _
    rw [price];simpa only [Nat.add_assoc] using total
  · change u.getReg .x6=_
    have before : p.getReg .x6=BitVec.ofNat 64 (upperNode i l) :=
      (pRes.regs .x6 (by decide) (by decide)).trans ((regM .x6 (by decide) (by decide) (by decide) (by decide)).trans cur.node)
    exact nodeU.trans ((congrArg (fun x : Word => x >>> (1:Nat)) before).trans (node_shift i l))
  · change u.getReg .x21=_
    have before : p.getReg .x21=BitVec.ofNat 64 (recordBase o) :=
      (pRes.regs .x21 (by decide) (by decide)).trans ((regM .x21 (by decide) (by decide) (by decide) (by decide)).trans baseReg)
    rw [show u.getReg .x21=_ from destU,before,←BitVec.ofNat_add]
    by_cases last : l.val=13 <;> simp [last,show l.val+1=14 ↔ l.val=13 by omega]
  · intro a lo
    by_cases fld : folded l
    · rw [if_pos fld] at mem
      change u.mem _=_
      rw [mem]
      exact (half_below m (T+28) a _ (by have:=full fld;omega) lo (by omega)).trans (inM a lo)
    · rw [if_neg fld] at mem
      change u.mem _=_
      rw [mem];exact inM a lo
  · intro a afit away
    rw [goalEnd] at away
    have old : m.getByte (BitVec.ofNat 64 a)=s.getByte (BitVec.ofNat 64 a) :=
      (field_outside field.bytes a afit (by rw [size];omega) (by rw [size];omega)).trans (emit_byte_of_mem memH _)
    by_cases fld : folded l
    · rw [if_pos fld] at mem
      rw [emit_byte_of_mem mem];have wid:=full fld
      exact (half_outside m (T+28) a _ (by have:=fits.2.1;omega) (by omega) afit (by omega)).trans old
    · rw [if_neg fld] at mem; exact (emit_byte_of_mem mem _).trans old
  · intro b hb
    by_cases late : folded l ∧ 28≤b
    · have wid:=full late.1
      have byte : b-28<2 := by omega
      have eq : T+b=(T+28)+(b-28) := by omega
      rw [if_pos late.1] at mem
      unfold payload
      rw [if_pos late]
      change u.getByte (BitVec.ofNat 64 (T+b))=_
      rw [emit_byte_of_mem mem,eq,emit_stored_byte m _ (b-28) _ (by have:=fits.2.1;omega) (by omega) byte]
    · have below (fld : folded l) : b<28 := by by_contra bad; exact late ⟨fld,by omega⟩
      have inside : b<width f := by
        change b<width (4+l.val);rw [size]
        by_cases fld : folded l
        · simpa only [plainWidth,if_pos fld] using below fld
        · simpa only [plainWidth,if_neg fld] using hb
      have old := (field.bytes.copied b inside).trans (emit_byte_of_mem memH _)
      unfold payload;rw [if_neg late]
      by_cases fld : folded l
      · rw [if_pos fld] at mem;have wid:=full fld;have bb:=below fld
        exact (emit_byte_of_mem mem _).trans ((half_outside m (T+28) (T+b) _ (by have:=fits.2.1;omega)
          (by omega) (by omega) (by omega)).trans old)
      · rw [if_neg fld] at mem; exact (emit_byte_of_mem mem _).trans old

end TwoPermutationPrototype.GroupedOpening.Whole
