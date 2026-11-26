import CommitGolfCandidate.PairBefore
import CommitGolfCandidate.PairWrites

namespace CommitGolfCandidate.PairCap
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8000
set_option maxHeartbeats 400000

attribute [local irreducible] beforeState overrideState Nat.iterate readBuffer
  openingResult suffixState setupState finishState

private abbrev retained (s : MachineState) :=
  readBuffer s submission.layout.trapdoor submission.sizes.trapdoor

private def prepared (committed : MachineState) (ps : Positions) :=
  setupState (jumpState (beforeState (retained committed) ps))

private theorem loaded (committed : MachineState) (ps : Positions) (hb : ps.card=BATCH) (k : Nat) (hk : k<128) :
    (prepared committed ps).getMem (BitVec.ofNat 64 (indexBase+8*k)) =
      BitVec.ofNat 64 (openingIndex ps k) := by
  have h : k < ps.card := by rw [hb]; exact hk
  change (prepared committed ps).mem _ = _
  unfold prepared
  rw [setupMem]
  have before := beforeWord committed ps hb (BitVec.ofNat 64 (indexBase+8*k))
    (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by dsimp [indexBase]; omega)]; dsimp [indexBase]; omega)
  change (beforeState (retained committed) ps).getMem _ = _
  rw [before]
  change (CommitGolfCandidate.submission.initialState .opening (retained committed, ps)).getMem
     (BitVec.ofNat 64 (CommitGolfCandidate.submission.layout.indices + 8*k)) = _
  exact (opening_input_index (retained committed) ps k h).trans (by simp [openingIndex,h])

private theorem srcData (committed : MachineState) (ps : Positions) (hb : ps.card=BATCH) (k : Nat) :
    let address := childAddress (openingIndex ps k/65536)
    readBuffer (prepared committed ps) address 32 = readBuffer committed address 32 := by
  dsimp only
  let u := openingIndex ps k/65536
  have b : openingIndex ps k < 16777216 := opening_index_bound ps k
  have bu : u < 256 := by dsimp [u]; omega
  have props : ∀ x : Fin 256, childAddress x.val % 8 = 0 ∧
       4294971424 ≤ childAddress x.val ∧ childAddress x.val + 32 ≤ 5905584160 := by decide
  have pp : childAddress u % 8 = 0 ∧ 4294971424 ≤ childAddress u ∧ childAddress u + 32 ≤ 5905584160 := props ⟨u,bu⟩
  obtain ⟨aligned,above,within⟩ := pp
  change readBuffer (prepared committed ps) (childAddress u) 32 = _
  unfold prepared; rw [read_buffer_memory_congr _ _ (setupMem _)]
  trans readBuffer (submission.initialState .opening (retained committed,ps)) (childAddress u) 32
  · apply read_digest_congr _ _ _ aligned
    intro j hj
    apply beforeWord committed ps hb
    change childAddress u + 32 ≤ 5905584160 at within
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]; omega
  · let off := childAddress u - 4294971424
    have eqn : 4294971424+off = childAddress u := by dsimp [off]; omega
    have bound : off+32 ≤ 2147483648 := by dsimp [off]; change childAddress u + 32 ≤ 5905584160 at within; omega
    have hh := opening_input_roundtrip committed ps off bound
    change readBuffer (submission.initialState .opening (retained committed, ps)) (4294971424+off) 32 = readBuffer committed (4294971424+off) 32 at hh
    simpa only [eqn] using hh

private theorem batchPreserves (committed : MachineState) (ps : Positions) (hb : ps.card=BATCH)
    (a : Nat) (ha : a%8=0) (endA : a+32≤outBase) :
    readBuffer (openingResult (retained committed) ps).state a 32 =
      readBuffer (beforeState (retained committed) ps) a 32 := by
  rw [batchState _ ps hb]
  unfold suffixState
  rw [read_buffer_memory_congr _ _ (finishMem _)]
  trans readBuffer (prepared committed ps) a 32
  · apply read_digest_congr _ _ _ ha
    intro j hj
    apply sweepBelow (openingIndex ps) (opening_index_bound ps) 128 (by decide)
      (prepared committed ps) (setupFrame _) (loaded committed ps hb)
    dsimp [outBase] at endA
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    dsimp [outBase]; omega
  · exact read_buffer_memory_congr _ _ (setupMem _) _ _

private theorem batchPreservesSalt (committed : MachineState) (ps : Positions) (hb : ps.card=BATCH)
    (a : Nat) (ha : a%8=0) (endA : a+16≤outBase) :
    readBuffer (openingResult (retained committed) ps).state a 16 =
      readBuffer (beforeState (retained committed) ps) a 16 := by
  rw [batchState _ ps hb]
  unfold suffixState
  rw [read_buffer_memory_congr _ _ (finishMem _)]
  trans readBuffer (prepared committed ps) a 16
  · apply read_salt_congr _ _ _ ha
    intro j hj
    apply sweepBelow (openingIndex ps) (opening_index_bound ps) 128 (by decide)
      (prepared committed ps) (setupFrame _) (loaded committed ps hb)
    dsimp [outBase] at endA
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    dsimp [outBase]; omega
  · exact read_buffer_memory_congr _ _ (setupMem _) _ _

theorem batchRecords (committed : MachineState) (ps : Positions) (hb : ps.card=BATCH)
    (r : Nat) (hr : r<128) :
    let st := (openingResult (retained committed) ps).state
    readBuffer st (10871640096+528*r) 16 = readBuffer committed (5905584160+16*openingIndex ps r) 16 ∧
    ∀ j < 16, readBuffer st (10871640096+528*r+16+32*j) 32 =
      readBuffer committed (4294971424+heapOffset (((LENGTH+openingIndex ps r)/2^j) ^^^ 1)) 32 := by
  dsimp only
  have old := (beforePayload committed ps hb).1 r hr
  constructor
  · rw [batchPreservesSalt committed ps hb _ (by omega) (by dsimp [outBase]; omega)]
    exact old.1
  · intro j hj
    rw [batchPreserves committed ps hb _ (by omega) (by dsimp [outBase]; omega)]
    exact old.2 j hj

theorem batchSlot (committed : MachineState) (ps : Positions) (hb : ps.card=BATCH)
    (p : Nat) (hp : p<128) :
    readBuffer (openingResult (retained committed) ps).state (outBase+32*p) 32 =
    overrideSlot (fun k => openingIndex ps k/131072)
      (fun k => readBuffer committed (childAddress (openingIndex ps k/65536)) 32) p BATCH
      (readBuffer committed (4294971424+heapOffset (128+p)) 32) := by
  rw [batchState _ ps hb]
  unfold suffixState
  rw [read_buffer_memory_congr _ _ (finishMem _)]
  have swept := sweepSlot (openingIndex ps) (opening_index_bound ps) 128 (by decide) (prepared committed ps)
     (setupFrame _) (loaded committed ps hb) p hp
  change readBuffer (overrideState^[128] (prepared committed ps)) _ 32 = _
  rw [swept]
  have orig : readBuffer (prepared committed ps) (outBase+32*p) 32 =
      readBuffer committed (4294971424+heapOffset (128+p)) 32 := by
    unfold prepared; rw [read_buffer_memory_congr _ _ (setupMem _)]
    exact (beforePayload committed ps hb).2 p hp
  simp only [srcData committed ps hb,orig,BATCH]

end CommitGolfCandidate.PairCap
