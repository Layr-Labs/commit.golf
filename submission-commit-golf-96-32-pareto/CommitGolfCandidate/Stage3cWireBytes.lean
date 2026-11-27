import CommitGolfCandidate.Stage3cCheckInput
import CommitGolfCandidate.Stage3cReadCursor
import CommitGolfCandidate.Stage3cScheme
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open BinaryMachine.Reader (window)
open Pw (packedInput wireBits)
theorem window_mod (v bits pos len : Nat) (inside : pos+len≤bits) : window (v%2^bits) pos len=window v pos len := by
  have h:=Reader.window_high v 0 bits pos (by omega)
  change window v 0 bits/2^pos=_ at h
  simp only [window,Nat.zero_add,pow_zero,Nat.div_one] at h
  unfold window;rw [h,Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (by omega : len≤bits-pos))]

theorem wire_source (x : CheckInput) (len : x.proof.length=67840) :
    Reader.Source (initial x) proofBase 67840 (packedInput x) := by
  intro j hj
  have e:=congrArg BitVec.toNat (read_buffer_byte (initial x) proofBase 67840 j hj)
  change _=(Open.byteAt (initial x) (proofBase+j)).toNat at e
  rw [←e,BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow];rfl

theorem opening_length (tree : Late.Levels) (salt : Late.SaltTape) (ps : Positions) (batch : ps.card=BATCH) :
    (Chained.Binary.opening tree salt ps).length=67840 := by
  simp only [Chained.Binary.opening,if_pos batch,Chained.Binary.packed,List.length_map,List.length_range];exact Chained.Binary.field_geometry.2

attribute [local irreducible] readBuffer Chained.Binary.encode List.range
theorem packed_roundtrip (x : CheckInput) (tree : Late.Levels) (salt : Late.SaltTape) (b : x.positions.card=BATCH)
    (proof : x.proof=Chained.Binary.opening tree salt x.positions) :
    packedInput x=Chained.Binary.encode (Pw.batchFields tree salt (Open.indices x.positions))%2^wireBits := by
  let num:=Chained.Binary.encode (Pw.batchFields tree salt (Open.indices x.positions))
  let raw:=BitVec.ofNat wireBits num
  have len : x.proof.length=67840:=proof ▸ opening_length _ _ _ b
  have cells (j : Nat) (inside : j<67840) : (initial x).getByte (Open.W (proofBase+j))=raw.extractLsb' (8*(0+j)) 8 := by
    have elem:=proof_byte x j (by omega) (by unfold proofBase;omega)
    have equal : x.proof=(List.range 67840).map (fun j=>BitVec.ofNat 8 (num/2^(8*j))) := by
      rw [proof,Chained.Binary.opening,if_pos b,Chained.Binary.packed,Chained.Binary.field_geometry.2];rfl
    apply elem.trans
    rw [List.getElem_of_eq equal];simp only [List.getElem_map,List.getElem_range,Nat.zero_add]
    apply BitVec.eq_of_toNat_eq
    simp only [raw,BitVec.extractLsb'_toNat,BitVec.toNat_ofNat,Nat.shiftRight_eq_div_pow]
    exact (window_mod num wireBits (8*j) 8 (by unfold wireBits;omega)).symm
  have e:=read_serialized_slice (initial x) raw proofBase 0 67840 cells
  change readBuffer (initial x) proofBase 67840=raw.extractLsb' 0 wireBits at e
  rw [BitVec.extractLsb'_eq_self] at e
  exact congrArg BitVec.toNat e
end CommitGolfCandidate.Chained.BinaryMachine.Check
