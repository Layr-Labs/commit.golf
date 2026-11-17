import CommitGolfCandidate.CapCheckRecordsReady
import CommitGolfCandidate.CapCheckLowerLogical
import CommitGolfCandidate.CapCheckValueBytes
import CommitGolfCandidate.CapRecordBytes

/-! A later physical record authenticates exactly its seventeen serialized
digest slots and ABI value. The index and value identities are explicit
parser handoff premises; neither can be supplied by proof bytes. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false

theorem cap_check_record_logical (oracle : Oracle) (input : CheckInput)
    (records : List CapLowerRecord) (suffix : Proof)
    (encoded : input.proof=capDigestEncoding (capLowerTranscript records)++suffix)
    (admitted : input.proof.length ≤ capProgram.sizes.proof)
    (ordinal remaining : Nat) (state : MachineState)
    (ready : CapCheckRecordsReady input ordinal remaining state)
    (present : ordinal < input.positions.card) (recordPresent : ordinal < records.length)
    (index : records[ordinal].index=
      (input.positions.sort (· ≤ ·))[ordinal]'(by simpa using present))
    (value : records[ordinal].value=
      input.values ((input.positions.attach.sort (fun i j => i.val ≤ j.val))[ordinal]'(by
        simpa using present))) :
    readBuffer (checkEvaluation oracle (capCheckLowerRecord state)).1 256 32 =
      records[ordinal].root oracle.compression := by
  have cardinal : input.positions.card ≤ LENGTH := by
    simpa [Index] using Finset.card_le_univ input.positions
  have sourceBounds :
      320 ≤ capProgram.layout.proof+544*ordinal ∧
      capProgram.layout.proof+544*ordinal+544<2^64 ∧
      320 ≤ capProgram.layout.values+256*ordinal ∧
      capProgram.layout.values+256*ordinal+256<2^64 := by
    norm_num [capProgram,capExperimental,candidate,layout,trapdoorBytes,
      LENGTH,LOG_LENGTH,LEAF_SIZE,DIGEST_BYTES] at cardinal ⊢
    omega
  have saltAligned : (capProgram.layout.proof+544*ordinal)%8=0 := by
    norm_num [capProgram,capExperimental,candidate,layout,trapdoorBytes,
      LENGTH,LOG_LENGTH,LEAF_SIZE,DIGEST_BYTES]
    omega
  have valueAligned : (capProgram.layout.values+256*ordinal)%8=0 := by
    norm_num [capProgram,capExperimental,candidate,layout,trapdoorBytes,
      LENGTH,LOG_LENGTH,LEAF_SIZE,DIGEST_BYTES]
    omega
  apply cap_check_lower_logical_digest oracle state records[ordinal]
    (capProgram.layout.proof+544*ordinal) (capProgram.layout.values+256*ordinal)
    ready.scratch ready.proof ready.values
    (by
      rw [ready.indices,index]
      exact cap_check_retained_index input state ordinal present ready.inputs)
    saltAligned sourceBounds.1 sourceBounds.2.1 valueAligned
    sourceBounds.2.2.1 sourceBounds.2.2.2
  · have slot := cap_framed_record_slot input state records suffix encoded admitted
      ready.inputs ordinal 0 recordPresent (by decide)
    simpa only [Nat.mul_zero,Nat.add_zero,capLowerEncoding,
      List.getElem?_cons_zero,Option.getD_some] using slot
  · intro block inside
    rw [cap_check_retained_value_block input state ordinal block present inside ready.inputs,
      value]
  · intro level
    have slot := cap_framed_record_slot input state records suffix encoded admitted
      ready.inputs ordinal (level.val+1) recordPresent (by omega)
    have address : capProgram.layout.proof+544*ordinal+32*(level.val+1)=
      capProgram.layout.proof+544*ordinal+32+32*level.val := by omega
    rw [address] at slot
    simpa only [capLowerEncoding,List.getElem?_cons_succ,List.getElem?_ofFn,
      level.isLt,↓reduceDIte,Option.getD_some] using slot

end CommitGolfCandidate
