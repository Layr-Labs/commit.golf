import CommitGolfCandidate.ChainedWidthTableRun

/-! The fixed seventeen-row record table is independent of all supplied proof bytes. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

def recordWidths : List (Fin 7) := [1,6]++List.replicate 8 2++[1]++List.replicate 6 0

theorem record_widths_count : recordWidths.length=17 := by decide +kernel
theorem record_widths_spec : recordWidths.map Fin.val=InteriorCodec.recordSpec.map Prod.snd := by decide +kernel
theorem record_widths_words : (widthTableWords recordWidths).length=51 := by decide +kernel

theorem native_record_widths (s : MachineState) :
    ParseWidthsAt (widthTableState recordWidths s) (s.getReg .x7) (InteriorCodec.recordSpec.map Prod.snd) := by
  rw [←record_widths_spec]
  exact width_table_memory recordWidths s (by rw [record_widths_count]; decide)

theorem native_record_widths_execution (image : Image) (base : Word)
    (code : OpsAt image base (widthTableOps recordWidths)) (s : MachineState) (metadata : Nat)
    (pointer : s.getReg .x7=BitVec.ofNat 64 metadata) (room : metadata+34≤MEMORY_BYTES)
    (pc : s.pc=base) (fuel : Nat) (coins : Bool) :
    execute image (51+fuel) s coins=
      (do let result ← execute image fuel (widthTableState recordWidths s) coins
          return result.charge 51 0) := by
  have capacity : metadata+2*recordWidths.length≤MEMORY_BYTES := by
    simpa only [record_widths_count] using room
  simpa only [record_widths_count] using
    width_table_execution image base recordWidths code s metadata pointer capacity pc fuel coins

end CommitGolfCandidate.Chained.Native
