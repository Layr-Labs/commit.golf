import CommitGolfCandidate.Stage3cCapLoop
import CommitGolfCandidate.Stage3cBatchLoop
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Open
open CommitGolf
open Late (Levels SaltTape)
open Writer (widths)

private def widthEnergy (n : Nat) : List Nat→Nat
  | []=>0
  | w::ws=>(Writer.measureField ⟨n%64,0⟩ w).cycles+widthEnergy (n+w) ws
private theorem charge_widths (n : Nat) (fs : List Binary.Field) : energy n fs=widthEnergy n (fs.map Binary.Field.bits) := by
  induction fs generalizing n with
  | nil=>rfl
  | cons f fs ih=>simp only [energy,List.map_cons,widthEnergy,ih]
private theorem selected_widths (tree : Levels) (salt : SaltTape) (xs : List Index) :
    (recordFields tree salt xs).map Binary.Field.bits=(List.replicate xs.length Writer.recordWidths).flatten := by
  induction xs with
  | nil=>rfl
  | cons i xs ih=>simp only [recordFields,List.flatMap_cons,List.map_append,Writer.record_widths,List.length_cons,
      List.replicate_succ,List.flatten_cons] at ih ⊢;rw [ih]
private theorem slot_widths (tree : Levels) (xs : List Index) (js : List Nat) :
    ((js.map (Binary.slot tree xs)).map Binary.Field.bits)=List.replicate js.length 230 := by
  induction js with
  | nil=>rfl
  | cons j js ih=>simp only [List.map_cons,List.length_cons,List.replicate_succ,ih];rfl
set_option maxRecDepth 80000 in
set_option maxHeartbeats 4500000 in
private theorem fixed_charge : widthEnergy 0 ((List.replicate 128 Writer.recordWidths).flatten++List.replicate 256 230)=156360 := by decide +kernel

theorem packed_charge (tree : Levels) (salt : SaltTape) (xs : List Index) (batch : xs.length=128) :
    energy 0 (recordFields tree salt xs)+energy (widths (recordFields tree salt xs)) (capFields tree xs 0 256)=156360 := by
  have both:=energy_append 0 (recordFields tree salt xs) (capFields tree xs 0 256)
  rw [Nat.zero_add] at both
  rw [←both,
    charge_widths,List.map_append,selected_widths,batch,capFields,slot_widths,List.length_range'];exact fixed_charge

theorem record_width_sum (tree : Levels) (salt : SaltTape) (xs : List Index) :
    widths (recordFields tree salt xs)=3780*xs.length := by
  induction xs with
  | nil=>rfl
  | cons i xs ih=>
    change widths (Binary.recordFields tree salt i++recordFields tree salt xs)=3780*(xs.length+1)
    rw [sum_append,batch_record_width,ih];omega

theorem cap_cost_eq (xs : List Index) :
    capPrice xs 0 256=(((List.range 256).map (Writer.capMarks xs)).map fun m=>Writer.capCost m.1 m.2).sum := by
  simp only [capPrice,List.range_eq_range',List.map_map]
  rfl

theorem cost_exact (tree : Levels) (salt : SaltTape) (xs : List Index) (batch : xs.length=128) :
    101+(recordSteps tree salt 0 xs+3*128)+4+
      (capPrice xs 0 256+energy (widths (recordFields tree salt xs)) (capFields tree xs 0 256))+7=Writer.batchCost xs := by
  have charge:=packed_charge tree salt xs batch
  rw [Writer.batchCost,Writer.writer_charge,recordSteps,batch,cap_cost_eq] at *
  dsimp only at *
  omega
end CommitGolfCandidate.Chained.BinaryMachine.Open
