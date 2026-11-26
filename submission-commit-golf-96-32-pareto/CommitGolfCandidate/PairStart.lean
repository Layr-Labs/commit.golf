import CommitGolfCandidate.PairHeader
import CommitGolfCandidate.PairProgress
import CommitGolfCandidate.BufferRefinement
namespace CommitGolfCandidate.PairCap.Batch
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 10000
set_option maxHeartbeats 200000

private theorem initialZero (input : CheckInput) (a : Nat) (low : a<32768) :
    (submission.initialState .check input).getByte (BitVec.ofNat 64 a) = 0 := by
  rw [initial_input_byte submission .check input a (by omega)]
  have b0 : ¬ submission.layout.commitment ≤ a := by change ¬ 4294971392 ≤ a; omega
  have b1 : ¬ submission.layout.indices ≤ a := by change ¬ 6442455072 ≤ a; omega
  have b2 : ¬ submission.layout.values ≤ a := by change ¬ 6576672800 ≤ a; omega
  have b3 : ¬ submission.layout.proof ≤ a := by change ¬ 10871640096 ≤ a; omega
  have b4 : ¬ dataBase (submission.image .check) ≤ a := by change ¬ 68719476736 ≤ a; omega
  simp [inputByte,Submission.inputBuffers,fixedBuffer,positionsBuffer,valuesBuffer,b0,b1,b2,b3,b4]

attribute [local irreducible] initialRows readBuffer
theorem startInvariant (o : Oracle) (input : CheckInput) (b : input.positions.card=BATCH)
    (length : input.proof.length=71680) :
    RecordInvariant o.compression input 0 (initialRows (submission.initialState .check input)) := by
  let s := submission.initialState .check input
  have s16 : s.getReg .x16 = 128 := by change BitVec.ofNat 64 input.positions.card=128; rw [b];rfl
  have s17 : s.getReg .x17 = 71680 := by change BitVec.ofNat 64 input.proof.length=71680; rw [length];rfl
  obtain ⟨pc,rem,idx,v,pf,rt,slots,scratch,depth,mem⟩ := rowsRegisters s s16 s17
  refine ⟨by decide,idx,v,pf,rem,scratch,depth,slots,rt,pc,?_,?_,?_,?_⟩
  · intro u
    have mm (a : Word) : (initialRows s).getByte a = s.getByte a := by
      simp only [MachineState.getByte,MachineState.getMem,mem]
    unfold storedAt
    rw [mm, initialZero input _ (by dsimp [flag]; have := u.isLt; omega)]
    rfl
  · intro r hr; omega
  · intro a _
    change (initialRows s).mem a = s.mem a
    exact congrArg (fun z : Word → Word => z a) mem
  · intro p
    rw [read_buffer_memory_congr _ _ mem]
    have eqn := read_serialized_slice s (0 : BitVec 256) (16384+96*p.val+64) 0 32 (by
      intro j hj
      rw [initialZero input _ (by have := p.isLt;omega)]
      simp)
    simpa using eqn

end CommitGolfCandidate.PairCap.Batch
