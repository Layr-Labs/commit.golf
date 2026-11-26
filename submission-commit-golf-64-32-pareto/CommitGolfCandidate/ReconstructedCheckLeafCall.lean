import CommitGolfCandidate.ReconstructedCheckLeafPlan
import CommitGolfCandidate.ReconstructedCheckParentCall
import CommitGolfCandidate.TaggedPinnedModel

namespace CommitGolfCandidate.Reconstruction.CheckLeafCall
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding Binding.Machine CheckValues CheckOracleMemory CheckRecorded CheckLeafPlan
open TwoPermutationPrototype TwoPermutationPrototype.Sampling TwoPermutationPrototype.RV64
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000
set_option exponentiation.threshold 2048
attribute [local irreducible] readBuffer

def request (o : Oracle) (idx : Index) (nonce : Words 2) (msg : Words 32) (q : Nat) : Block :=
  let first:=pinnedFirstRow o.permutation msg
  if q=0 then first.1 else (pinnedSecondRow o.permutation idx nonce first.2 msg).1

def row (o : Oracle) (data : Block) := PublicRow.permutation data (o.permutation data)

structure Params (o : Oracle) (env : Env) (idx : Index) (nonce : Words 2) (msg : Words 32) : Prop where
  inputs : ∀ q<2, ∀ i : Fin 25, (operand q i).val env=(request o idx nonce msg q).extractLsb' (64*i.val) 64
  answers : ∀ q<2, ∀ i<25, env.answer q i=(o.permutation (request o idx nonce msg q)).extractLsb' (64*i) 64
  room : ∀ q<2, let s:=(physical env (arg q)).toNat; let t:=(physical env (dst q)).toNat
    s+200≤MEMORY_BYTES ∧ t+200≤MEMORY_BYTES ∧ s%8=0 ∧ t%8=0

private theorem allowed : ∀ q : Fin 2, (∀ i : Fin 25, table.allowed (atIndex (arg q) i)=true) ∧
    (∀ i : Fin 25, table.allowed (atIndex (dst q) i)=true) := by decide

private theorem read25 (s : MachineState) (src : Nat) (b : BitVec 1600) (aligned : src%8=0)
    (words : ∀ i < 25, s.getMem (BitVec.ofNat 64 (src+8*i))=b.extractLsb' (64*i) 64) :
    readBuffer s src 200=b := by
  have all := CheckParentCall.read_words_eq s src 25 b aligned words
  change (readBuffer s src 200).cast _ = b at all
  rw [BitVec.cast_eq] at all
  exact all

private theorem read_input (o : Oracle) (env : Env) (layout : Layout env table) (idx : Index) (nonce : Words 2) (msg : Words 32)
    (p : Params o env idx nonce msg) (q : Nat) (bound : q<2) (m : State) (s : MachineState) (h : Matches env m s)
    (safe : Safe table m.writes) (src : Nat) (physicalSrc : physical env (arg q)=BitVec.ofNat 64 src)
    (aligned : src%8=0) (words : ∀ i : Fin 25, look table (atIndex (arg q) i) m.writes=operand q i) :
    readBuffer s src 200=request o idx nonce msg q := by
  apply read25 s src _ aligned
  intro i hi
  have w:=look_sound env table layout m.writes (atIndex (arg q) i) ((allowed ⟨q,bound⟩).1 ⟨i,hi⟩) safe
  rw [words ⟨i,hi⟩,p.inputs q bound ⟨i,hi⟩,←h.mem,physical_index,physicalSrc,←BitVec.ofNat_add] at w
  exact w.symm

private theorem syscall (o : Oracle) (site : Fin 6) (s : MachineState) (src dst : Nat) (data : Block)
    (pc : s.pc=CommitBlocks.addr (oracleSite site)) (srcRoom : src+200≤MEMORY_BYTES) (dstRoom : dst+200≤MEMORY_BYTES)
    (srcA : src%8=0) (dstA : dst%8=0) (read : readBuffer s src 200=data)
    (regs : s.getReg .x5=0 ∧ s.getReg .x10=BitVec.ofNat 64 src ∧ s.getReg .x11=200 ∧
      s.getReg .x12=BitVec.ofNat 64 dst ∧ s.getReg .x13=1) :
    Segment o 1 s (writeBits s (BitVec.ofNat 64 dst) (o.permutation data)) [row o data] := by
  have sv : (BitVec.ofNat 64 src).toNat=src := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by unfold MEMORY_BYTES at srcRoom;omega)]
  have dv : (BitVec.ofNat 64 dst).toNat=dst := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by unfold MEMORY_BYTES at dstRoom;omega)]
  have args : oracleInput s=some (.inr (.inl data)) := by
    have k : (s.getReg .x13).toNat=1 := by rw [regs.2.2.2.2];rfl
    unfold oracleInput;dsimp only;rw [k]
    simp [regs.2.1,regs.2.2.1,regs.2.2.2.1,rangeValid,sv,dv,srcA,dstA,srcRoom,dstRoom,read,PERMUTATION_WIDTH]
    congr 1
    exact (by simp : ∀ x : BitVec 1600, BitVec.ofNat 1600 x.toNat=x) data
  have sg:=call o site s (.inr (.inl data)) pc regs.1 args
  rw [regs.2.2.2.1] at sg
  exact sg

theorem call_step (o : Oracle) (env : Env) (layout : Layout env table) (idx : Index) (nonce : Words 2) (msg : Words 32)
    (p : Params o env idx nonce msg) (q : Nat) (bound : q<2) (site : Fin 6) (m : State) (s : MachineState)
    (h : Matches env m s) (safe : Safe table m.writes) (pc : s.pc=CommitBlocks.addr (oracleSite site)) (fields : callTest q m) :
    ∃ t, Segment o 1 s t [row o (request o idx nonce msg q)] ∧ Matches env (modelCall q m) t ∧ Safe table (modelCall q m).writes := by
  obtain ⟨h5,h10,h11,h12,h13,words⟩:=fields
  let src:=(physical env (arg q)).toNat
  let dest:=(physical env (dst q)).toNat
  have source : physical env (arg q)=BitVec.ofNat 64 src := by simp [src]
  have target : physical env (dst q)=BitVec.ofNat 64 dest := by simp [dest]
  have regs : s.getReg .x5=0 ∧ s.getReg .x10=BitVec.ofNat 64 src ∧ s.getReg .x11=200 ∧
      s.getReg .x12=BitVec.ofNat 64 dest ∧ s.getReg .x13=1 := by
    rw [h.regs .x5,h.regs .x10,h.regs .x11,h.regs .x12,h.regs .x13,h5,h10,h11,h12,h13]
    exact ⟨rfl,source,rfl,target,rfl⟩
  obtain ⟨srcRoom,dstRoom,srcA,dstA⟩ := p.room q bound
  have read := read_input o env layout idx nonce msg p q bound m s h safe src source srcA words
  have sg := syscall o site s src dest _ pc srcRoom dstRoom srcA dstA read regs
  have outRoom : dest+8*25≤2^64 := by change dest+200≤MEMORY_BYTES at dstRoom;unfold MEMORY_BYTES at dstRoom;omega
  exact ⟨_,sg,reply env m s h (dst q) q 25 _ (p.answers q bound) dest target dstA outRoom,
    safe_install table (dst q) q m.writes safe 25 (fun i hi=>(allowed ⟨q,bound⟩).2 ⟨i,hi⟩)⟩

end CommitGolfCandidate.Reconstruction.CheckLeafCall
