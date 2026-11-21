import CommitGolfCandidate.ChainedWidthTable

/-! Exact fetches and execution for trusted straight-line width plans. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
attribute [local irreducible] execute

def widthTableImage (widths : List (Fin 7)) : Image := ⟨widthTableWords widths,[]⟩

theorem width_table_decode (widths : List (Fin 7)) :
    (widthTableWords widths).map inverseDecodeBase=(widthTableOps widths).map some := by
  have single (width : Fin 7) :
      (widthInitWords width).map inverseDecodeBase=(widthInitOps width).map some := by
    fin_cases width <;> rfl
  induction widths with
  | nil => rfl
  | cons width widths ih =>
    change (widthInitWords width++widthTableWords widths).map inverseDecodeBase=
      (widthInitOps width++widthTableOps widths).map some
    rw [List.map_append,List.map_append,single,ih]

theorem width_table_decode_at (widths : List (Fin 7)) (index : Nat) (inside : index<3*widths.length) :
    ((widthTableWords widths)[index]?).bind decodeInstruction=
      some (.base ((widthTableOps widths).getD index .EBREAK)) := by
  have projected := congrArg (fun xs => xs[index]?) (width_table_decode widths)
  simp only [List.getElem?_map] at projected
  have op : (widthTableOps widths)[index]?=some ((widthTableOps widths).getD index .EBREAK) := by
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by rwa [width_table_ops_length])]
    rfl
  rw [op] at projected
  cases word : (widthTableWords widths)[index]? with
  | none => simp [word] at projected
  | some value =>
    simp only [word,Option.map_some,Option.some.injEq] at projected
    simp only [Option.bind_some]
    cases decoded : decodeInstruction value with
    | none => simp [inverseDecodeBase,decoded] at projected
    | some instruction =>
      cases instruction <;> simp [inverseDecodeBase,decoded] at projected <;> simp [projected]

theorem width_table_at (widths : List (Fin 7)) (room : 4096+12*widths.length<2^64) :
    OpsAt (widthTableImage widths) 4096 (widthTableOps widths) := by
  intro index inside s pc
  have bound : index<3*widths.length := by rwa [width_table_ops_length] at inside
  apply inverse_image_fetch (widthTableImage widths) s index _ (by omega)
  · change s.pc=BitVec.ofNat 64 4096+BitVec.ofNat 64 (4*index) at pc
    rwa [←BitVec.ofNat_add] at pc
  · exact width_table_decode_at widths index bound

theorem width_table_execution (image : Image) (base : Word) (widths : List (Fin 7))
    (code : OpsAt image base (widthTableOps widths)) (s : MachineState) (source : Nat)
    (pointer : s.getReg .x7=BitVec.ofNat 64 source) (room : source+2*widths.length≤MEMORY_BYTES)
    (pc : s.pc=base) (fuel : Nat) (coins : Bool) :
    execute image (3*widths.length+fuel) s coins=
      (do let result ← execute image fuel (widthTableState widths s) coins
          return result.charge (3*widths.length) 0) := by
  induction widths generalizing s source base with
  | nil => simp [width_table_zero,Execution.charge]
  | cons width widths ih =>
    have front := ops_at_left image base (widthInitOps width) (widthTableOps widths) code
    have tail := ops_at_right image base (widthInitOps width) (widthTableOps widths) code
    change OpsAt image (base+12) (widthTableOps widths) at tail
    have memoryBound : MEMORY_BYTES≤2^64 := by decide
    have numeric : (s.getReg .x7).toNat=source := by
      rw [pointer,BitVec.toNat_ofNat,Nat.mod_eq_of_lt]
      simp only [List.length_cons] at room
      omega
    have access : accessValid (s.getReg .x7+1) 1=true := by
      exact byte_access_offset _ 1 (by rw [numeric]; simp only [List.length_cons] at room; omega)
    have nextPointer : (widthInitPrefix width s 3).getReg .x7=BitVec.ofNat 64 (source+2) := by
      rw [width_init_pointer,pointer,BitVec.ofNat_add]
      rfl
    have nextPC : (widthInitPrefix width s 3).pc=base+12 := by
      rw [width_init_pc width s 3 (by decide),pc]
      rfl
    have rest := ih (base+12) tail (widthInitPrefix width s 3) (source+2) nextPointer
      (by simp only [List.length_cons] at room; omega) nextPC
    rw [show 3*(width::widths).length+fuel=3+(3*widths.length+fuel) by simp only [List.length_cons]; omega,
      width_init_execution image base width front s pc access,rest,width_table_cons]
    simp [Execution.charge,List.length_cons,Nat.mul_add,Nat.add_comm,Nat.add_left_comm]

end CommitGolfCandidate.Chained.Native
