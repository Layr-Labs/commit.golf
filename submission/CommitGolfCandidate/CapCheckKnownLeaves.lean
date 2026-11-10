import CommitGolfCandidate.CapCheckSegmentSuccess
import CommitGolfCandidate.CapDfsSerialization

/-! Payload agreement only at known cap leaves. No initial internal root is
constrained. The finalized mark view and known-leaf frame transport this
agreement through any successful actual checker segment. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false

def CapCheckKnownLeaves (state : MachineState) :
    {height : Nat} → Nat → CapView height → Prop
  | _,node,.leaf known => ∀ digest,known=some digest → capReadRoot state node=digest
  | _,node,.node left right =>
    CapCheckKnownLeaves state (2*node) left ∧
      CapCheckKnownLeaves state (2*node+1) right

theorem cap_check_known_leaves_frame (marked : Nat → Bool)
    (state next : MachineState) {height : Nat} (view : CapView height) (node : Nat)
    (lower : 128≤node*2^height) (upper : (node+1)*2^height≤256)
    (marks : CapViewMarks marked node view)
    (known : CapCheckKnownLeaves state node view)
    (frame : ∀ leaf,128≤leaf → leaf<256 → marked leaf=true →
      capReadRoot next leaf=capReadRoot state leaf) :
    CapCheckKnownLeaves next node view := by
  induction view generalizing node with
  | leaf payload =>
    intro digest equal
    have nodeLower : 128≤node := by simpa using lower
    have nodeUpper : node<256 := by
      have bound : node+1≤256 := by simpa using upper
      omega
    have present : marked node=true := by
      change marked node=payload.isSome at marks
      rw [equal] at marks
      exact marks
    exact (frame node nodeLower nodeUpper present).trans (known digest equal)
  | @node depth left right ihLeft ihRight =>
    have power := Nat.two_pow_pos depth
    have lower' := lower
    have upper' := upper
    rw [pow_succ] at lower' upper'
    obtain ⟨_,leftMarks,rightMarks⟩ := marks
    obtain ⟨leftKnown,rightKnown⟩ := known
    exact ⟨ihLeft (2*node) (by nlinarith) (by nlinarith) leftMarks leftKnown,
      ihRight (2*node+1) (by nlinarith) (by nlinarith) rightMarks rightKnown⟩

theorem cap_check_value_known_leaves (oracle : Oracle) (limit : Nat)
    (marked : Nat → Bool) (count : Nat) (control : CapDfsControl)
    (state : MachineState) (ready : CapCheckDfsReady limit marked control state)
    (above : 22528≤(state.getReg .x25).toNat)
    {height : Nat} (view : CapView height) (node : Nat)
    (lower : 128≤node*2^height) (upper : (node+1)*2^height≤256)
    (marks : CapViewMarks marked node view)
    (known : CapCheckKnownLeaves state node view)
    (passed : (capCheckDfsValue oracle marked count control state).2=true) :
    CapCheckKnownLeaves (capCheckDfsValue oracle marked count control state).1 node view := by
  apply cap_check_known_leaves_frame marked state _ view node lower upper marks known
  intro leaf leafLower leafUpper present
  exact (cap_check_value_known_root oracle limit marked count control state
    ready above leaf leafLower leafUpper present passed).1

end CommitGolfCandidate
