import CommitGolfCandidate.GroupOpenLeafFields
import CommitGolfCandidate.GroupOpenWideCopy16

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open PackedOpening (ByteCopy)
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000

def firstSource (i : Index) (b : Nat) : Nat :=
  if b<16 then nonceAddress i+b else
    leafAddress (i.val ^^^ ((b-16)/32+1)) + (b-16)%32

theorem first_source_before (i : Index) (b : Nat) (bound : b<112) : firstSource i b < proofBase := by
  unfold firstSource
  split
  · have ix := i.isLt
    have tail := nonces_end_at_indices
    have endIx := indices_before_records
    unfold nonceAddress
    omega
  · let j : Fin 3 := ⟨(b-16)/32,by omega⟩
    have before := (leaf_address_inside _ (sibling_in_message i j)).2.2
    have tail := nonces_end_at_indices
    have endIx := indices_before_records
    change leafAddress (i.val ^^^ ((b-16)/32+1))+32 ≤ nonceBase at before
    omega

theorem source_quartet (i : Index) (j : Fin 3) (b : Nat) (inside : b<32) :
    firstSource i (16+32*j.val+b) = leafAddress (i.val ^^^ (j.val+1))+b := by
  unfold firstSource
  rw [if_neg (by omega)]
  have q : (16+32*j.val+b-16)/32=j.val := by omega
  have r : (16+32*j.val+b-16)%32=b := by omega
  rw [q,r]

structure PrefixWrites (before after : MachineState) (i : Index) (ordinal first last : Nat) : Prop where
  bytes : ∀ b, first ≤ b → b<last → after.getByte (BitVec.ofNat 64 (recordBase ordinal+b)) =
    before.getByte (BitVec.ofNat 64 (firstSource i b))
  frame : ∀ a, a<2^64 → a<recordBase ordinal+first ∨ recordBase ordinal+last≤a →
    after.getByte (BitVec.ofNat 64 a) = before.getByte (BitVec.ofNat 64 a)
  input : ∀ a<proofBase, after.getMem (BitVec.ofNat 64 a) = before.getMem (BitVec.ofNat 64 a)

theorem PrefixWrites.of_copy {s u : MachineState} {i : Index} {ordinal first count src : Nat}
    (copy : ByteCopy s u src (recordBase ordinal+first) count)
    (fits : recordBase ordinal+first+count ≤ MEMORY_BYTES)
    (source : ∀ b, b<count → firstSource i (first+b) = src+b)
    (input : ∀ a<proofBase, u.getMem (BitVec.ofNat 64 a)=s.getMem (BitVec.ofNat 64 a)) :
    PrefixWrites s u i ordinal first (first+count) := by
  constructor
  · intro b lo hi
    have add : first+(b-first)=b := by omega
    have matchSource := source (b-first) (by omega)
    rw [add] at matchSource
    rw [matchSource]
    simpa only [Nat.add_assoc,add] using copy.copied (b-first) (by omega)
  · intro a valid outside
    have ram : MEMORY_BYTES<2^64 := by decide
    exact field_outside copy a valid (by omega) (by simpa only [Nat.add_assoc] using outside)
  · exact input

theorem PrefixWrites.join {s u v : MachineState} {i : Index} {o a b c : Nat}
    (left : PrefixWrites s u i o a b) (right : PrefixWrites u v i o b c)
    (ends : c ≤ 112) (fit : o<LENGTH) (order : a ≤ b ∧ b ≤ c := by omega) :
    PrefixWrites s v i o a c := by
  have ram : MEMORY_BYTES < 2^64 := by decide
  have last := all_record_ends_fit o fit
  have endBytes : recordBase (o+1) = recordBase o+534 := by
    unfold recordBase recordBytes; omega
  have base : proofBase ≤ recordBase o := by unfold recordBase; omega
  constructor
  · intro j lo hi
    by_cases old : j<b
    · exact (right.frame _ (by omega) (Or.inl (by omega))).trans (left.bytes j lo old)
    · exact (right.bytes j (by omega) hi).trans (left.frame _ (by
        have z := first_source_before i j (by omega); omega) (Or.inl (by
        have z := first_source_before i j (by omega); omega)))
  · intro address valid outside
    exact (right.frame _ valid (outside.imp (by omega) id)).trans
        (left.frame _ valid (outside.imp id (by omega)))
  · intro address below
    exact (right.input _ below).trans (left.input _ below)

theorem PrefixWrites.move {s u s' u' : MachineState} {i : Index} {o a b : Nat}
    (writes : PrefixWrites s u i o a b) (initial : s'.mem=s.mem) (final : u'.mem=u.mem) :
    PrefixWrites s' u' i o a b := by
  constructor
  · intro j lo hi
    simpa only [MachineState.getByte,MachineState.getMem,initial,final] using writes.bytes j lo hi
  · intro j fit outside
    simpa only [MachineState.getByte,MachineState.getMem,initial,final] using writes.frame j fit outside
  · intro j below
    simpa only [MachineState.getMem,initial,final] using writes.input j below

def prefixScratch : List Reg := [.x6,.x7,.x10,.x21,.x28,.x29,.x31]

def Keeps (s u : MachineState) : Prop := ∀ r, r ∉ prefixScratch → u.getReg r=s.getReg r

theorem Keeps.next {s u v : MachineState} (head : Keeps s u) (tail : Keeps u v) : Keeps s v :=
  fun r hr => (tail r hr).trans (head r hr)

structure PrefixStart (s : MachineState) (i : Index) (o : Nat) : Prop where
  pc : s.pc=0x103c
  heap : s.getReg .x9=BitVec.ofNat 64 trapdoorBase
  slots : s.getReg .x24=BitVec.ofNat 64 groupSlots
  nonce : s.getReg .x22=BitVec.ofNat 64 nonceBase
  groups : s.getReg .x19=BitVec.ofNat 64 4194304
  output : s.getReg .x21=BitVec.ofNat 64 (recordBase o)
  index : s.getMem (s.getReg .x8)=BitVec.ofNat 64 i.val
  readable : accessValid (s.getReg .x8) 8 = true

structure GroupCursor (s : MachineState) (i : Index) (o j : Nat) : Prop where
  pc : s.pc=BitVec.ofNat 64 (4096+4*(39+36*j))
  heap : s.getReg .x9=BitVec.ofNat 64 trapdoorBase
  groups : s.getReg .x19=BitVec.ofNat 64 4194304
  group : s.getReg .x7=BitVec.ofNat 64 (groupSlots+1024*(i.val/4))
  low : s.getReg .x10=BitVec.ofNat 64 (i.val%4)
  index : s.getReg .x6=BitVec.ofNat 64 i.val
  output : s.getReg .x21=BitVec.ofNat 64 (recordBase o+16)

def saltStart (s : MachineState) : MachineState := slotStart (Writer16.state (nonceSetup s))

/-- Cycles of a record's salt: the three setup rows, the alignment-dispatched copy and the slot rows. -/
def saltCycles (o : Nat) : Nat := 8+Writer16.cycles (recordBase o)

theorem run_salt_start (s : MachineState) (i : Index) (o : Nat) (fit : o<LENGTH) (start : PrefixStart s i o) :
    let u := saltStart s
    RunsOpeningBlock s u (saltCycles o) ∧ GroupCursor u i o 0 ∧ PrefixWrites s u i o 0 16 ∧ Keeps s u := by
  let t := nonceSetup s
  let v := Writer16.state t
  have h := nonce_setup_post s
  have z := slot_post v
  obtain ⟨srcEven,dstEven,sep,room⟩ := all_nonce_copies_fit i o fit
  have endRecord := all_record_ends_fit o fit
  have ix := i.isLt
  have tail := nonces_end_at_indices
  have endIx := indices_before_records
  have srcA : nonceAddress i % 8 = 0 := by
    have : nonceBase % 8 = 0 := by decide
    unfold nonceAddress; omega
  have base : proofBase ≤ recordBase o := by unfold recordBase; omega
  have h1 : nonceAddress i+16 ≤ indicesBase := by
    have lt : i.val < LENGTH := i.isLt
    unfold nonceAddress; omega
  have h2 : 12 ≤ 8*LENGTH := by decide
  have apart : nonceAddress i+28 ≤ recordBase o := by omega
  have room28 : recordBase o+28 ≤ MEMORY_BYTES := by unfold recordBase recordBytes at *; omega
  have done := Writer16.copy t (nonceAddress i) (recordBase o) (by rw [h.1,start.pc]; rfl)
    (physical_nonce_source s i start.nonce start.index)
    ((h.2.2.2.2 .x21 (by decide) (by decide)).trans start.output) srcA dstEven apart room28
  have fieldPC : v.pc = 4232 := done.pc
  have rd : v.getReg .x6 = BitVec.ofNat 64 i.val :=
    (done.regs _ (by decide)).trans (h.2.2.2.1.trans start.index)
  have fixed (r : Reg) (a : r≠.x31) (b : r≠.x6) (c : r≠.x7) :
      v.getReg r = s.getReg r := (done.regs r a).trans (h.2.2.2.2 r b c)
  have stable : Keeps s (slotStart v) := by
    intro r free
    simp only [prefixScratch,List.mem_cons,List.not_mem_nil,or_false,not_or] at free
    exact (z.2.2.2.2.2 r free.2.2.2.1 free.2.1 free.2.2.1).trans
      (fixed r free.2.2.2.2.2.2 free.1 free.2.1)
  have gate : RunsOpeningBlock s t 3 := fun fuel coins => execute_nonce_setup s start.pc start.readable fuel coins
  have sourceBytes : PrefixWrites t v i o 0 16 := by
    apply PrefixWrites.of_copy (src:=nonceAddress i) (count:=16)
    · simpa using done.bytes
    · simpa using room
    · intro b hb; simp [firstSource,hb]
    · intro a ha
      have pb : proofBase % 8 = 0 := by decide
      have small : a < 2^64 := by
        have : proofBase < 2^64 := by decide
        omega
      exact done.below (BitVec.ofNat 64 a) (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]; omega)
  have nonceRun : RunsOpeningBlock t v (Writer16.cycles (recordBase o)) := done.run
  have total := (gate.next nonceRun).next (run_slot v fieldPC)
  rw [show 3+Writer16.cycles (recordBase o)+5 = saltCycles o by unfold saltCycles; omega] at total
  refine ⟨total, ⟨?_,?_,?_,?_,?_,?_,?_⟩,
    sourceBytes.move h.2.1.symm z.2.1, stable⟩
  · change (slotStart v).pc = _
    rw [z.1,fieldPC]; rfl
  · exact (stable .x9 (by decide)).trans start.heap
  · exact (stable .x19 (by decide)).trans start.groups
  · change (slotStart v).getReg .x7 = _
    rw [z.2.2.2.1,rd,masked_group,(fixed .x24 (by decide) (by decide) (by decide)),start.slots,
      ← BitVec.ofNat_add,Nat.add_comm]
  · change (slotStart v).getReg .x10 = _
    rw [z.2.2.2.2.1,rd,low_selector]
  · exact (z.2.2.2.2.2 .x6 (by decide) (by decide) (by decide)).trans rd
  · change (slotStart v).getReg .x21 = _
    rw [z.2.2.1,(fixed .x21 (by decide) (by decide) (by decide)),start.output]
    exact (BitVec.ofNat_add (n:=64) _ 16).symm

def groupStep (j : Fin 3) (s : MachineState) : MachineState := copyState (.quartet j) (quartetHead j s)

theorem run_group_step (s : MachineState) (i : Index) (o : Nat) (j : Fin 3) (fit : o<LENGTH)
    (start : GroupCursor s i o j.val) :
    let u := groupStep j s
    RunsOpeningBlock s u (4+recordCopyCost o) ∧ GroupCursor u i o (j.val+1) ∧
    PrefixWrites s u i o (16+32*j.val) (16+32*j.val+32) ∧ Keeps s u := by
  let t := quartetHead j s
  let src := leafAddress (i.val ^^^ (j.val+1))
  let dest := recordBase o+(16+32*j.val)
  have head := quartet_head_post j s
  have bounds := leaf_address_inside _ (sibling_in_message i j)
  have srcA : src%8=0 := bounds.1
  have before : src+32 ≤ nonceBase := bounds.2.2
  have room := all_record_ends_fit o fit
  have count := j.isLt
  have actualRoom : dest+32 ≤ MEMORY_BYTES := by unfold dest recordBase recordBytes at *; omega
  have baseAligned : proofBase%2=0 := by decide
  have endIx := indices_before_records
  have endSalt := nonces_end_at_indices
  have field : FieldInputs (.quartet j) t src dest := by
    refine ⟨?_,quartet_physical_source s i j start.group start.low,?_,?_,actualRoom,by change src%2=0; omega,?_,
      fun _ => srcA⟩
    · rw [head.1,start.pc]
      change BitVec.ofNat 64 _ + BitVec.ofNat 64 16 = _
      rw [← BitVec.ofNat_add]
      congr 1
      simp [CopySite.start]; omega
    · rw [show t.getReg .x21=s.getReg .x21 from head.2.2.2 .x21 (by decide),start.output]
      rw [← BitVec.ofNat_add]
      change BitVec.ofNat 64 (recordBase o+16+32*j.val)=BitVec.ofNat 64 (recordBase o+(16+32*j.val))
      rw [Nat.add_assoc]
    · change src+32 ≤ dest
      unfold dest recordBase; omega
    · unfold dest recordBase recordBytes; omega
  have step (r : Reg) (a : r≠.x31) (b : r≠.x28) (c : r≠.x29) :
      (groupStep j s).getReg r = s.getReg r :=
    (copy_register (.quartet j) t r a (.inr c)).trans (head.2.2.2 r b)
  have cost : copyCost (.quartet j) dest = recordCopyCost o := by
    simp only [copyCost, CopySite.wide, ite_true, recordCopyCost, dest]
    rw [show recordBase o+(16+32*j.val) = recordBase o+8*(2+4*j.val) by omega, wide_cost_shift]
  have copyRun : RunsOpeningBlock t (groupStep j s) (recordCopyCost o) := by
    rw [← cost]; exact field.run
  have writes : PrefixWrites t (groupStep j s) i o (16+32*j.val) (16+32*j.val+32) := by
    apply PrefixWrites.of_copy (src:=src) (count:=32) field.bytes actualRoom (source_quartet i j)
    intro a ha
    exact field.words_before proofBase a ha (by unfold dest recordBase; omega) (by decide)
  refine ⟨(run_quartet_head j s start.pc).next copyRun, ⟨?_,
    (step _ (by decide) (by decide) (by decide)).trans start.heap,
    (step _ (by decide) (by decide) (by decide)).trans start.groups,
    (step _ (by decide) (by decide) (by decide)).trans start.group,
    (step _ (by decide) (by decide) (by decide)).trans start.low,
    (step _ (by decide) (by decide) (by decide)).trans start.index,
    (step _ (by decide) (by decide) (by decide)).trans start.output⟩,
    writes.move head.2.1.symm rfl, ?_⟩
  · change (copyState (.quartet j) t).pc = _
    rw [field.final_pc]
    congr 1
    simp only [CopySite.start,CopySite.halfwords]
    omega
  · intro r free
    simp only [prefixScratch,List.mem_cons,List.not_mem_nil,or_false,not_or] at free
    exact step r free.2.2.2.2.2.2 free.2.2.2.2.1 free.2.2.2.2.2.1

def recordPrefix (s : MachineState) := quartetExit (groupStep 2 (groupStep 1 (groupStep 0 (saltStart s))))

theorem execute_record_prefix (s : MachineState) (i : Index) (o : Nat) (fit : o<LENGTH) (start : PrefixStart s i o) :
    let u := recordPrefix s
    RunsOpeningBlock s u (saltCycles o+15+3*recordCopyCost o) ∧ LowerCursor u i o 0 ∧ PrefixWrites s u i o 0 112 ∧
      Keeps s u := by
  have ⟨salt,g0,w0,k0⟩ := run_salt_start s i o fit start
  have ⟨s0,g1,w1,k1⟩ := run_group_step _ i o 0 fit g0
  have ⟨s1,g2,w2,k2⟩ := run_group_step _ i o 1 fit g1
  have ⟨s2,g3,w3,k3⟩ := run_group_step _ i o 2 fit g2
  let last := groupStep 2 (groupStep 1 (groupStep 0 (saltStart s)))
  have e := quartet_exit_post last
  have past : Keeps s last := ((k0.next k1).next k2).next k3
  have kept : Keeps last (quartetExit last) := by
    intro r free
    simp only [prefixScratch,List.mem_cons,List.not_mem_nil,or_false,not_or] at free
    exact e.2.2.2.2 r free.2.2.2.1 free.1
  have writes : PrefixWrites s last i o 0 112 := (((w0.join w1 (by decide) fit).join w2 (by decide) fit).join w3 (by decide) fit)
  have total := (((salt.next s0).next s1).next s2).next (run_quartet_exit _ g3.pc)
  rw [show saltCycles o+(4+recordCopyCost o)+(4+recordCopyCost o)+(4+recordCopyCost o)+3 = saltCycles o+15+3*recordCopyCost o by omega]
    at total
  refine ⟨total, ⟨?_,?_,?_,?_⟩,
    writes.move rfl e.2.1,past.next kept⟩
  · change (quartetExit last).pc = _
    rw [e.1,show last.pc = _ from g3.pc]; rfl
  · exact (kept .x9 (by decide)).trans g3.heap
  · change (quartetExit last).getReg .x6 = _
    rw [e.2.2.2.1,show last.getReg .x6 = _ from g3.index,quarter_shift,show last.getReg .x19 = _ from g3.groups,← BitVec.ofNat_add, upper_node_zero,Nat.add_comm]
  · change (quartetExit last).getReg .x21 = _
    rw [e.2.2.1,show last.getReg .x21 = _ from g3.output]
    change BitVec.ofNat 64 (recordBase o+16) + BitVec.ofNat 64 96 = BitVec.ofNat 64 (recordBase o+112)
    rw [← BitVec.ofNat_add,Nat.add_assoc]

end TwoPermutationPrototype.GroupedOpening
