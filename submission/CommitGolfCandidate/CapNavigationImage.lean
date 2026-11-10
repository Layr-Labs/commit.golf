import CommitGolfCandidate.CapDfsNavigation

/-! Exact navigation fetches in both experimental depth-24 images. The four
operations occur at different opening/check PCs, but retain the same decoded
instruction semantics and one-cycle bridges. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

def capNavigationIndex : Bool → CapNavigation → Nat
  | false, .descend => 87
  | false, .ascend => 103
  | false, .sibling => 105
  | false, .parity => 101
  | true, .descend => 133
  | true, .ascend => 151
  | true, .sibling => 158
  | true, .parity => 149

def capNavigationPC (checking : Bool) (operation : CapNavigation) : Word :=
  BitVec.ofNat 64 (4096 + 4 * capNavigationIndex checking operation)

def capWalkImage (checking : Bool) : Image :=
  (capExperimental 24).image (if checking then .check else .opening)

theorem cap_navigation_fetched (checking : Bool) (operation : CapNavigation)
    (state : MachineState) (pc : state.pc = capNavigationPC checking operation) :
    fetch (capWalkImage checking) state =
      some (.base (capNavigationInstruction operation)) := by
  apply cap_image_fetch _ state (capNavigationIndex checking operation) _
  · cases checking <;> cases operation <;> decide
  · exact pc
  · cases checking <;> cases operation <;> rfl

theorem cap_navigation_image_execute (checking : Bool) (operation : CapNavigation)
    (state : MachineState) (pc : state.pc = capNavigationPC checking operation)
    (fuel : Nat) (allowCoins : Bool) :
    execute (capWalkImage checking) (1 + fuel) state allowCoins =
      (do let result ← execute (capWalkImage checking) fuel
            (capNavigationState operation state) allowCoins
          return result.charge 1 0) :=
  cap_navigation_execute _ operation state
    (cap_navigation_fetched checking operation state pc) fuel allowCoins

end CommitGolfCandidate
