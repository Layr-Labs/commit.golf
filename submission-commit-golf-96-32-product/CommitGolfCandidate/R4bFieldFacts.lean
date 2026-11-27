import CommitGolfCandidate.R4bSchedule
set_option Elab.async false
namespace CommitGolfCandidate.R4b
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxHeartbeats 3000000
set_option maxRecDepth 5000
theorem facts0 (t l i : Nat) (bt : t<32) (bl : l<4) (bi : i<16777216) :
    fieldFacts t l i 0 := by
  refine ⟨?_,?_,?_⟩
  · simp [fieldFacts, addressOps, okList, Op.ok, Op.inputs, Op.dest, Op.put, Op.val, finalRegs, number, env, fixed, locals, reads, virtualSlot, tableRow, blockIndex, group, part, high, pointer, logicalSource, tableBase, S4.Open.tdBase, S4.Machine.indexBase, Late.rowBase] <;> omega
  · simp [fieldFacts, addressOps, okList, Op.ok, Op.inputs, Op.dest, Op.put, Op.val, finalRegs, number, env, fixed, locals, reads, virtualSlot, tableRow, blockIndex, group, part, high, pointer, logicalSource, tableBase, S4.Open.tdBase, S4.Machine.indexBase, Late.rowBase] <;> omega
  · intro r n h;cases r <;> simp_all [fieldFacts, addressOps, okList, Op.ok, Op.inputs, Op.dest, Op.put, Op.val, finalRegs, number, env, fixed, locals, reads, virtualSlot, tableRow, blockIndex, group, part, high, pointer, logicalSource, tableBase, S4.Open.tdBase, S4.Machine.indexBase, Late.rowBase] <;> omega

theorem facts1 (t l i : Nat) (bt : t<32) (bl : l<4) (bi : i<16777216) :
    fieldFacts t l i 1 := by
  refine ⟨?_,?_,?_⟩
  · simp [fieldFacts, addressOps, okList, Op.ok, Op.inputs, Op.dest, Op.put, Op.val, finalRegs, number, env, fixed, locals, reads, virtualSlot, tableRow, blockIndex, group, part, high, pointer, logicalSource, tableBase, S4.Open.tdBase, S4.Machine.indexBase, Late.rowBase] <;> omega
  · simp [fieldFacts, addressOps, okList, Op.ok, Op.inputs, Op.dest, Op.put, Op.val, finalRegs, number, env, fixed, locals, reads, virtualSlot, tableRow, blockIndex, group, part, high, pointer, logicalSource, tableBase, S4.Open.tdBase, S4.Machine.indexBase, Late.rowBase] <;> omega
  · intro r n h;cases r <;> simp_all [fieldFacts, addressOps, okList, Op.ok, Op.inputs, Op.dest, Op.put, Op.val, finalRegs, number, env, fixed, locals, reads, virtualSlot, tableRow, blockIndex, group, part, high, pointer, logicalSource, tableBase, S4.Open.tdBase, S4.Machine.indexBase, Late.rowBase] <;> omega

theorem facts2 (t l i : Nat) (bt : t<32) (bl : l<4) (bi : i<16777216) :
    fieldFacts t l i 2 := by
  refine ⟨?_,?_,?_⟩
  · simp [fieldFacts, addressOps, okList, Op.ok, Op.inputs, Op.dest, Op.put, Op.val, finalRegs, number, env, fixed, locals, reads, virtualSlot, tableRow, blockIndex, group, part, high, pointer, logicalSource, tableBase, S4.Open.tdBase, S4.Machine.indexBase, Late.rowBase] <;> omega
  · simp [fieldFacts, addressOps, okList, Op.ok, Op.inputs, Op.dest, Op.put, Op.val, finalRegs, number, env, fixed, locals, reads, virtualSlot, tableRow, blockIndex, group, part, high, pointer, logicalSource, tableBase, S4.Open.tdBase, S4.Machine.indexBase, Late.rowBase] <;> omega
  · intro r n h;cases r <;> simp_all [fieldFacts, addressOps, okList, Op.ok, Op.inputs, Op.dest, Op.put, Op.val, finalRegs, number, env, fixed, locals, reads, virtualSlot, tableRow, blockIndex, group, part, high, pointer, logicalSource, tableBase, S4.Open.tdBase, S4.Machine.indexBase, Late.rowBase] <;> omega

theorem facts3 (t l i : Nat) (bt : t<32) (bl : l<4) (bi : i<16777216) :
    fieldFacts t l i 3 := by
  refine ⟨?_,?_,?_⟩
  · simp [fieldFacts, addressOps, okList, Op.ok, Op.inputs, Op.dest, Op.put, Op.val, finalRegs, number, env, fixed, locals, reads, virtualSlot, tableRow, blockIndex, group, part, high, pointer, logicalSource, tableBase, S4.Open.tdBase, S4.Machine.indexBase, Late.rowBase] <;> omega
  · simp [fieldFacts, addressOps, okList, Op.ok, Op.inputs, Op.dest, Op.put, Op.val, finalRegs, number, env, fixed, locals, reads, virtualSlot, tableRow, blockIndex, group, part, high, pointer, logicalSource, tableBase, S4.Open.tdBase, S4.Machine.indexBase, Late.rowBase] <;> omega
  · intro r n h;cases r <;> simp_all [fieldFacts, addressOps, okList, Op.ok, Op.inputs, Op.dest, Op.put, Op.val, finalRegs, number, env, fixed, locals, reads, virtualSlot, tableRow, blockIndex, group, part, high, pointer, logicalSource, tableBase, S4.Open.tdBase, S4.Machine.indexBase, Late.rowBase] <;> omega

theorem facts4 (t l i : Nat) (bt : t<32) (bl : l<4) (bi : i<16777216) :
    fieldFacts t l i 4 := by
  refine ⟨?_,?_,?_⟩
  · simp [fieldFacts, addressOps, okList, Op.ok, Op.inputs, Op.dest, Op.put, Op.val, finalRegs, number, env, fixed, locals, reads, virtualSlot, tableRow, blockIndex, group, part, high, pointer, logicalSource, tableBase, S4.Open.tdBase, S4.Machine.indexBase, Late.rowBase] <;> omega
  · simp [fieldFacts, addressOps, okList, Op.ok, Op.inputs, Op.dest, Op.put, Op.val, finalRegs, number, env, fixed, locals, reads, virtualSlot, tableRow, blockIndex, group, part, high, pointer, logicalSource, tableBase, S4.Open.tdBase, S4.Machine.indexBase, Late.rowBase] <;> omega
  · intro r n h;cases r <;> simp_all [fieldFacts, addressOps, okList, Op.ok, Op.inputs, Op.dest, Op.put, Op.val, finalRegs, number, env, fixed, locals, reads, virtualSlot, tableRow, blockIndex, group, part, high, pointer, logicalSource, tableBase, S4.Open.tdBase, S4.Machine.indexBase, Late.rowBase] <;> omega

theorem facts5 (t l i : Nat) (bt : t<32) (bl : l<4) (bi : i<16777216) :
    fieldFacts t l i 5 := by
  refine ⟨?_,?_,?_⟩
  · simp [fieldFacts, addressOps, okList, Op.ok, Op.inputs, Op.dest, Op.put, Op.val, finalRegs, number, env, fixed, locals, reads, virtualSlot, tableRow, blockIndex, group, part, high, pointer, logicalSource, tableBase, S4.Open.tdBase, S4.Machine.indexBase, Late.rowBase] <;> omega
  · simp [fieldFacts, addressOps, okList, Op.ok, Op.inputs, Op.dest, Op.put, Op.val, finalRegs, number, env, fixed, locals, reads, virtualSlot, tableRow, blockIndex, group, part, high, pointer, logicalSource, tableBase, S4.Open.tdBase, S4.Machine.indexBase, Late.rowBase] <;> omega
  · intro r n h;cases r <;> simp_all [fieldFacts, addressOps, okList, Op.ok, Op.inputs, Op.dest, Op.put, Op.val, finalRegs, number, env, fixed, locals, reads, virtualSlot, tableRow, blockIndex, group, part, high, pointer, logicalSource, tableBase, S4.Open.tdBase, S4.Machine.indexBase, Late.rowBase] <;> omega

theorem facts6 (t l i : Nat) (bt : t<32) (bl : l<4) (bi : i<16777216) :
    fieldFacts t l i 6 := by
  refine ⟨?_,?_,?_⟩
  · simp [fieldFacts, addressOps, okList, Op.ok, Op.inputs, Op.dest, Op.put, Op.val, finalRegs, number, env, fixed, locals, reads, virtualSlot, tableRow, blockIndex, group, part, high, pointer, logicalSource, tableBase, S4.Open.tdBase, S4.Machine.indexBase, Late.rowBase] <;> omega
  · simp [fieldFacts, addressOps, okList, Op.ok, Op.inputs, Op.dest, Op.put, Op.val, finalRegs, number, env, fixed, locals, reads, virtualSlot, tableRow, blockIndex, group, part, high, pointer, logicalSource, tableBase, S4.Open.tdBase, S4.Machine.indexBase, Late.rowBase] <;> omega
  · intro r n h;cases r <;> simp_all [fieldFacts, addressOps, okList, Op.ok, Op.inputs, Op.dest, Op.put, Op.val, finalRegs, number, env, fixed, locals, reads, virtualSlot, tableRow, blockIndex, group, part, high, pointer, logicalSource, tableBase, S4.Open.tdBase, S4.Machine.indexBase, Late.rowBase] <;> omega

theorem facts7 (t l i : Nat) (bt : t<32) (bl : l<4) (bi : i<16777216) :
    fieldFacts t l i 7 := by
  refine ⟨?_,?_,?_⟩
  · simp [fieldFacts, addressOps, okList, Op.ok, Op.inputs, Op.dest, Op.put, Op.val, finalRegs, number, env, fixed, locals, reads, virtualSlot, tableRow, blockIndex, group, part, high, pointer, logicalSource, tableBase, S4.Open.tdBase, S4.Machine.indexBase, Late.rowBase] <;> omega
  · simp [fieldFacts, addressOps, okList, Op.ok, Op.inputs, Op.dest, Op.put, Op.val, finalRegs, number, env, fixed, locals, reads, virtualSlot, tableRow, blockIndex, group, part, high, pointer, logicalSource, tableBase, S4.Open.tdBase, S4.Machine.indexBase, Late.rowBase] <;> omega
  · intro r n h;cases r <;> simp_all [fieldFacts, addressOps, okList, Op.ok, Op.inputs, Op.dest, Op.put, Op.val, finalRegs, number, env, fixed, locals, reads, virtualSlot, tableRow, blockIndex, group, part, high, pointer, logicalSource, tableBase, S4.Open.tdBase, S4.Machine.indexBase, Late.rowBase] <;> omega

theorem facts8 (t l i : Nat) (bt : t<32) (bl : l<4) (bi : i<16777216) :
    fieldFacts t l i 8 := by
  refine ⟨?_,?_,?_⟩
  · simp [fieldFacts, addressOps, okList, Op.ok, Op.inputs, Op.dest, Op.put, Op.val, finalRegs, number, env, fixed, locals, reads, virtualSlot, tableRow, blockIndex, group, part, high, pointer, logicalSource, tableBase, S4.Open.tdBase, S4.Machine.indexBase, Late.rowBase] <;> omega
  · simp [fieldFacts, addressOps, okList, Op.ok, Op.inputs, Op.dest, Op.put, Op.val, finalRegs, number, env, fixed, locals, reads, virtualSlot, tableRow, blockIndex, group, part, high, pointer, logicalSource, tableBase, S4.Open.tdBase, S4.Machine.indexBase, Late.rowBase] <;> omega
  · intro r n h;cases r <;> simp_all [fieldFacts, addressOps, okList, Op.ok, Op.inputs, Op.dest, Op.put, Op.val, finalRegs, number, env, fixed, locals, reads, virtualSlot, tableRow, blockIndex, group, part, high, pointer, logicalSource, tableBase, S4.Open.tdBase, S4.Machine.indexBase, Late.rowBase] <;> omega

theorem facts9 (t l i : Nat) (bt : t<32) (bl : l<4) (bi : i<16777216) :
    fieldFacts t l i 9 := by
  refine ⟨?_,?_,?_⟩
  · simp [fieldFacts, addressOps, okList, Op.ok, Op.inputs, Op.dest, Op.put, Op.val, finalRegs, number, env, fixed, locals, reads, virtualSlot, tableRow, blockIndex, group, part, high, pointer, logicalSource, tableBase, S4.Open.tdBase, S4.Machine.indexBase, Late.rowBase] <;> omega
  · simp [fieldFacts, addressOps, okList, Op.ok, Op.inputs, Op.dest, Op.put, Op.val, finalRegs, number, env, fixed, locals, reads, virtualSlot, tableRow, blockIndex, group, part, high, pointer, logicalSource, tableBase, S4.Open.tdBase, S4.Machine.indexBase, Late.rowBase] <;> omega
  · intro r n h;cases r <;> simp_all [fieldFacts, addressOps, okList, Op.ok, Op.inputs, Op.dest, Op.put, Op.val, finalRegs, number, env, fixed, locals, reads, virtualSlot, tableRow, blockIndex, group, part, high, pointer, logicalSource, tableBase, S4.Open.tdBase, S4.Machine.indexBase, Late.rowBase] <;> omega

theorem facts10 (t l i : Nat) (bt : t<32) (bl : l<4) (bi : i<16777216) :
    fieldFacts t l i 10 := by
  refine ⟨?_,?_,?_⟩
  · simp [fieldFacts, addressOps, okList, Op.ok, Op.inputs, Op.dest, Op.put, Op.val, finalRegs, number, env, fixed, locals, reads, virtualSlot, tableRow, blockIndex, group, part, high, pointer, logicalSource, tableBase, S4.Open.tdBase, S4.Machine.indexBase, Late.rowBase] <;> omega
  · simp [fieldFacts, addressOps, okList, Op.ok, Op.inputs, Op.dest, Op.put, Op.val, finalRegs, number, env, fixed, locals, reads, virtualSlot, tableRow, blockIndex, group, part, high, pointer, logicalSource, tableBase, S4.Open.tdBase, S4.Machine.indexBase, Late.rowBase] <;> omega
  · intro r n h;cases r <;> simp_all [fieldFacts, addressOps, okList, Op.ok, Op.inputs, Op.dest, Op.put, Op.val, finalRegs, number, env, fixed, locals, reads, virtualSlot, tableRow, blockIndex, group, part, high, pointer, logicalSource, tableBase, S4.Open.tdBase, S4.Machine.indexBase, Late.rowBase] <;> omega

theorem facts11 (t l i : Nat) (bt : t<32) (bl : l<4) (bi : i<16777216) :
    fieldFacts t l i 11 := by
  refine ⟨?_,?_,?_⟩
  · simp [fieldFacts, addressOps, okList, Op.ok, Op.inputs, Op.dest, Op.put, Op.val, finalRegs, number, env, fixed, locals, reads, virtualSlot, tableRow, blockIndex, group, part, high, pointer, logicalSource, tableBase, S4.Open.tdBase, S4.Machine.indexBase, Late.rowBase] <;> omega
  · simp [fieldFacts, addressOps, okList, Op.ok, Op.inputs, Op.dest, Op.put, Op.val, finalRegs, number, env, fixed, locals, reads, virtualSlot, tableRow, blockIndex, group, part, high, pointer, logicalSource, tableBase, S4.Open.tdBase, S4.Machine.indexBase, Late.rowBase] <;> omega
  · intro r n h;cases r <;> simp_all [fieldFacts, addressOps, okList, Op.ok, Op.inputs, Op.dest, Op.put, Op.val, finalRegs, number, env, fixed, locals, reads, virtualSlot, tableRow, blockIndex, group, part, high, pointer, logicalSource, tableBase, S4.Open.tdBase, S4.Machine.indexBase, Late.rowBase] <;> omega

theorem facts12 (t l i : Nat) (bt : t<32) (bl : l<4) (bi : i<16777216) :
    fieldFacts t l i 12 := by
  refine ⟨?_,?_,?_⟩
  · simp [fieldFacts, addressOps, okList, Op.ok, Op.inputs, Op.dest, Op.put, Op.val, finalRegs, number, env, fixed, locals, reads, virtualSlot, tableRow, blockIndex, group, part, high, pointer, logicalSource, tableBase, S4.Open.tdBase, S4.Machine.indexBase, Late.rowBase] <;> omega
  · simp [fieldFacts, addressOps, okList, Op.ok, Op.inputs, Op.dest, Op.put, Op.val, finalRegs, number, env, fixed, locals, reads, virtualSlot, tableRow, blockIndex, group, part, high, pointer, logicalSource, tableBase, S4.Open.tdBase, S4.Machine.indexBase, Late.rowBase] <;> omega
  · intro r n h;cases r <;> simp_all [fieldFacts, addressOps, okList, Op.ok, Op.inputs, Op.dest, Op.put, Op.val, finalRegs, number, env, fixed, locals, reads, virtualSlot, tableRow, blockIndex, group, part, high, pointer, logicalSource, tableBase, S4.Open.tdBase, S4.Machine.indexBase, Late.rowBase] <;> omega

theorem facts13 (t l i : Nat) (bt : t<32) (bl : l<4) (bi : i<16777216) :
    fieldFacts t l i 13 := by
  refine ⟨?_,?_,?_⟩
  · simp [fieldFacts, addressOps, okList, Op.ok, Op.inputs, Op.dest, Op.put, Op.val, finalRegs, number, env, fixed, locals, reads, virtualSlot, tableRow, blockIndex, group, part, high, pointer, logicalSource, tableBase, S4.Open.tdBase, S4.Machine.indexBase, Late.rowBase] <;> omega
  · simp [fieldFacts, addressOps, okList, Op.ok, Op.inputs, Op.dest, Op.put, Op.val, finalRegs, number, env, fixed, locals, reads, virtualSlot, tableRow, blockIndex, group, part, high, pointer, logicalSource, tableBase, S4.Open.tdBase, S4.Machine.indexBase, Late.rowBase] <;> omega
  · intro r n h;cases r <;> simp_all [fieldFacts, addressOps, okList, Op.ok, Op.inputs, Op.dest, Op.put, Op.val, finalRegs, number, env, fixed, locals, reads, virtualSlot, tableRow, blockIndex, group, part, high, pointer, logicalSource, tableBase, S4.Open.tdBase, S4.Machine.indexBase, Late.rowBase] <;> omega

theorem facts14 (t l i : Nat) (bt : t<32) (bl : l<4) (bi : i<16777216) :
    fieldFacts t l i 14 := by
  refine ⟨?_,?_,?_⟩
  · simp [fieldFacts, addressOps, okList, Op.ok, Op.inputs, Op.dest, Op.put, Op.val, finalRegs, number, env, fixed, locals, reads, virtualSlot, tableRow, blockIndex, group, part, high, pointer, logicalSource, tableBase, S4.Open.tdBase, S4.Machine.indexBase, Late.rowBase] <;> omega
  · simp [fieldFacts, addressOps, okList, Op.ok, Op.inputs, Op.dest, Op.put, Op.val, finalRegs, number, env, fixed, locals, reads, virtualSlot, tableRow, blockIndex, group, part, high, pointer, logicalSource, tableBase, S4.Open.tdBase, S4.Machine.indexBase, Late.rowBase] <;> omega
  · intro r n h;cases r <;> simp_all [fieldFacts, addressOps, okList, Op.ok, Op.inputs, Op.dest, Op.put, Op.val, finalRegs, number, env, fixed, locals, reads, virtualSlot, tableRow, blockIndex, group, part, high, pointer, logicalSource, tableBase, S4.Open.tdBase, S4.Machine.indexBase, Late.rowBase] <;> omega

theorem facts15 (t l i : Nat) (bt : t<32) (bl : l<4) (bi : i<16777216) :
    fieldFacts t l i 15 := by
  refine ⟨?_,?_,?_⟩
  · simp [fieldFacts, addressOps, okList, Op.ok, Op.inputs, Op.dest, Op.put, Op.val, finalRegs, number, env, fixed, locals, reads, virtualSlot, tableRow, blockIndex, group, part, high, pointer, logicalSource, tableBase, S4.Open.tdBase, S4.Machine.indexBase, Late.rowBase] <;> omega
  · simp [fieldFacts, addressOps, okList, Op.ok, Op.inputs, Op.dest, Op.put, Op.val, finalRegs, number, env, fixed, locals, reads, virtualSlot, tableRow, blockIndex, group, part, high, pointer, logicalSource, tableBase, S4.Open.tdBase, S4.Machine.indexBase, Late.rowBase] <;> omega
  · intro r n h;cases r <;> simp_all [fieldFacts, addressOps, okList, Op.ok, Op.inputs, Op.dest, Op.put, Op.val, finalRegs, number, env, fixed, locals, reads, virtualSlot, tableRow, blockIndex, group, part, high, pointer, logicalSource, tableBase, S4.Open.tdBase, S4.Machine.indexBase, Late.rowBase] <;> omega

theorem facts16 (t l i : Nat) (bt : t<32) (bl : l<4) (bi : i<16777216) :
    fieldFacts t l i 16 := by
  refine ⟨?_,?_,?_⟩
  · simp [fieldFacts, addressOps, okList, Op.ok, Op.inputs, Op.dest, Op.put, Op.val, finalRegs, number, env, fixed, locals, reads, virtualSlot, tableRow, blockIndex, group, part, high, pointer, logicalSource, tableBase, S4.Open.tdBase, S4.Machine.indexBase, Late.rowBase] <;> omega
  · simp [fieldFacts, addressOps, okList, Op.ok, Op.inputs, Op.dest, Op.put, Op.val, finalRegs, number, env, fixed, locals, reads, virtualSlot, tableRow, blockIndex, group, part, high, pointer, logicalSource, tableBase, S4.Open.tdBase, S4.Machine.indexBase, Late.rowBase] <;> omega
  · intro r n h;cases r <;> simp_all [fieldFacts, addressOps, okList, Op.ok, Op.inputs, Op.dest, Op.put, Op.val, finalRegs, number, env, fixed, locals, reads, virtualSlot, tableRow, blockIndex, group, part, high, pointer, logicalSource, tableBase, S4.Open.tdBase, S4.Machine.indexBase, Late.rowBase] <;> omega

theorem allFacts {q t l i : Nat} (bq : q<17) (bt : t<32) (bl : l<4) (bi : i<16777216) :
    fieldFacts t l i q := by
  let j : Fin 17:=⟨q,bq⟩
  change fieldFacts t l i j.val
  clear_value j
  fin_cases j
  · exact facts0 _ _ _ bt bl bi
  · exact facts1 _ _ _ bt bl bi
  · exact facts2 _ _ _ bt bl bi
  · exact facts3 _ _ _ bt bl bi
  · exact facts4 _ _ _ bt bl bi
  · exact facts5 _ _ _ bt bl bi
  · exact facts6 _ _ _ bt bl bi
  · exact facts7 _ _ _ bt bl bi
  · exact facts8 _ _ _ bt bl bi
  · exact facts9 _ _ _ bt bl bi
  · exact facts10 _ _ _ bt bl bi
  · exact facts11 _ _ _ bt bl bi
  · exact facts12 _ _ _ bt bl bi
  · exact facts13 _ _ _ bt bl bi
  · exact facts14 _ _ _ bt bl bi
  · exact facts15 _ _ _ bt bl bi
  · exact facts16 _ _ _ bt bl bi
end CommitGolfCandidate.R4b
