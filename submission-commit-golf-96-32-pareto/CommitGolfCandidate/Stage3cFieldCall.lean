import CommitGolfCandidate.Stage3cFieldRun
namespace CommitGolfCandidate.Chained.BinaryMachine.Writer
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W)
def fieldCode (n k : Nat) := stream (parts n) k ++ finish

private theorem return_kept (s : MachineState) (ws : List Nat) (k : Nat) :
    (pathEnd s (stream ws k)).getReg .x1=s.getReg .x1 := by
  apply path_keeps_reg
  induction ws generalizing k with
  | nil=>rfl
  | cons w ws ih=>
    simp only [stream,chunkCode,List.all_append,ih,Bool.and_true]
    have f : ∀ b : Bool,(fetchWord b).all (fun z=>keepsReg .x1 z.2) := by decide
    have m : mix.all (fun z=>keepsReg .x1 z.2) := by decide
    have g : ∀ b : Bool,(spill b).all (fun z=>keepsReg .x1 z.2) := by decide
    rw [f,m];split <;> first | rfl | simp [g]

theorem field_price (n k : Nat) :
    (fieldCode n k).length=(measureField ⟨k,0⟩ n).cycles := by
  have q:=stream_meter (parts n) k 0
  have calcEq : measureField ⟨k,0⟩ n =
      let m:=(parts n).foldl push ⟨k,0⟩; {m with cycles:=m.cycles+finish.length} := by
    simp only [measureField,parts,List.foldl_append];split <;> rfl
  rw [calcEq]
  simp only [Nat.zero_add] at q
  simp only [fieldCode,List.length_append,q]

theorem field_call (s : MachineState) (n k src dst : Nat) (small : n≤256) (partialBits : k<64)
    (pc : s.pc=pcAt 21) (size : s.getReg .x11=W n) (pending : s.getReg .x24=W k) (threshold : s.getReg .x27=64)
    (from_ : s.getReg .x10=W src) (to_ : s.getReg .x19=W dst)
    (sa : src%8=0) (da : dst%8=0) (sb : src+32≤MEMORY_BYTES) (db : dst+32≤MEMORY_BYTES) :
    let t:=pathEnd s (fieldCode n k)
    let cycles:=(measureField ⟨k,0⟩ n).cycles
    Open.Runs s t cycles cycles ∧ t.pc=(s.getReg .x1 &&& ~~~1#64) ∧ t.getReg .x24=W ((k+n)%64) ∧
      t.getReg .x19=W (dst+8*((k+n)/64)) := by
  let ws:=parts n
  obtain ⟨proper,total⟩:=parts_valid n
  have count : ws.length≤4 := by
    simp only [ws,parts,List.length_append,List.length_replicate];split <;> simp <;> omega
  let u:=pathEnd s (stream ws k)
  obtain ⟨run,ip,zero,bits,dest⟩:=stream_run s ws k src dst proper (total ▸ small) partialBits pc (total ▸ size) pending threshold
    from_ to_ sa da (by omega) (by omega)
  obtain ⟨ok,ret,mem,regs⟩:=finished u ip zero
  have tail : Open.Runs u (pathEnd u finish) finish.length finish.length := path_run _ true _ _ finish_sites ok
  have cost : (stream ws k).length+finish.length=(measureField ⟨k,0⟩ n).cycles :=
    (List.length_append (as:=stream ws k) (bs:=finish)).symm.trans (field_price n k)
  have joined:=run.trans tail
  rw [cost] at joined
  simp only [fieldCode,end_append]
  refine ⟨joined,ret.trans (congrArg (· &&& ~~~1#64) (return_kept s ws k)),?_,?_⟩
  · change (pathEnd u finish).regs .x24=_
    rw [regs];exact bits.trans (congrArg (fun m=>W ((k+m)%64)) total)
  · change (pathEnd u finish).regs .x19=_
    rw [regs];exact dest.trans (congrArg (fun m=>W (dst+8*((k+m)/64))) total)
end CommitGolfCandidate.Chained.BinaryMachine.Writer
