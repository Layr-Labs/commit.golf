import CommitGolfCandidate.R4LaneCode
namespace CommitGolfCandidate.R4
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (pcAt pc_succ rowAddress nodeAddress)
attribute [local irreducible] DetRun writeBits readBuffer submission
set_option exponentiation.threshold 1024
private theorem direct (o : Oracle) (img : Image) (s : MachineState) (a b : Nat)
    (fetchOp : fetch img s=some (.base .ECALL)) (mode : s.getReg .x5=0) (kind : s.getReg .x13=0) (width : s.getReg .x11=96)
    (src : s.getReg .x10=Z b) (dst : s.getReg .x12=Z a)
    (sa : b%8=0) (da : a%8=0) (sb : b+96≤MEMORY_BYTES) (db : a+32≤MEMORY_BYTES) :
    DetRun o img s 1 (writeBits s (Z a) (o.compression (readBuffer s b 96))) 8 1 :=
  DetRun.compress_eq (by rfl) (oracle:=o) (img:=img) (s:=s) fetchOp mode width kind b a src dst sa da sb db
    (o.compression (readBuffer s b 96)) (congrArg o.compression (BitVec.cast_eq _ _))

theorem simpleCall (o : Oracle) (s : MachineState) (n p : Nat) (d : Width)
    (hi : p<nodes d) (f : Pointers d p s) (pc : s.pc=pcAt n) (op : Site n .ECALL) :
    let a:=nodeAddress (d.val+1) p
    let b:=rowAddress d p
    let w:=o.compression (readBuffer s b 96)
    MRun o s 1 (writeBits s (Z a) w) 8 1 := by
  dsimp only
  exact direct o (submission.image .commit) s (nodeAddress (d.val+1) p) (rowAddress d p) (op s pc) f.mode f.kind f.width f.src f.dst (Late.rowAligned _ _) (Late.nodeAligned _ _)
    (le_trans (Late.row_disjoint d p p d.isLt hi) (le_trans (Nat.le_add_right _ 32) ((Late.parent_below_salts _ _ hi).trans (by decide : Late.rowBase≤MEMORY_BYTES))))
    ((Late.parent_below_salts _ _ hi).trans (by decide : Late.rowBase≤MEMORY_BYTES))
end CommitGolfCandidate.R4
