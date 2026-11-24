import CommitGolfCandidate.Layout2CapBank1
import CommitGolfCandidate.Layout2CapBank2
import CommitGolfCandidate.Layout2CapBank3
import CommitGolfCandidate.Layout2CapBank4
import CommitGolfCandidate.Layout2CapBank5
import CommitGolfCandidate.Layout2CapBank6
import CommitGolfCandidate.Layout2CapBank7
import CommitGolfCandidate.Layout2CapBank8
import CommitGolfCandidate.Layout2CapBank9
import CommitGolfCandidate.Layout2CapBank10
import CommitGolfCandidate.Layout2CapBank11
import CommitGolfCandidate.Layout2CapBank12
import CommitGolfCandidate.Layout2CapBank13
import CommitGolfCandidate.Layout2CapBank14
import CommitGolfCandidate.Layout2CapBank15
import CommitGolfCandidate.Layout2CapBank16
import CommitGolfCandidate.Layout2CapBank17
import CommitGolfCandidate.Layout2CapBank18
import CommitGolfCandidate.Layout2CapBank19
import CommitGolfCandidate.Layout2CapBank20
import CommitGolfCandidate.Layout2CapBank21
import CommitGolfCandidate.Layout2CapBank22
import CommitGolfCandidate.Layout2CapBank23
import CommitGolfCandidate.Layout2CapBank24
import CommitGolfCandidate.Layout2CapBank25
import CommitGolfCandidate.Layout2CapBank26
import CommitGolfCandidate.Layout2CapBank27
import CommitGolfCandidate.Layout2CapBank28
import CommitGolfCandidate.Layout2CapBank29
import CommitGolfCandidate.Layout2CapBank30
import CommitGolfCandidate.Layout2CapBank31
import CommitGolfCandidate.Layout2CapBank32
namespace CommitGolfCandidate.Layout2.Cap
open CommitGolf Layout2Helpers
set_option maxRecDepth 20000
set_option maxHeartbeats 1800000

theorem checked_entry (m i : Nat) (lo : 1≤m) (hi : m≤32) (bound : i<8*size m) :
    dec m i<8*size m ∧ enc m i<8*size m ∧ enc m (dec m i)=i ∧ dec m (enc m i)=i ∧
    u16 (offset m+2*i)=dec m i := by
  have ok : checkEntry m i=true := by
    interval_cases m
    · exact bank1 i bound
    · exact bank2 i bound
    · exact bank3 i bound
    · exact bank4 i bound
    · exact bank5 i bound
    · exact bank6 i bound
    · exact bank7 i bound
    · exact bank8 i bound
    · exact bank9 i bound
    · exact bank10 i bound
    · exact bank11 i bound
    · exact bank12 i bound
    · exact bank13 i bound
    · exact bank14 i bound
    · exact bank15 i bound
    · exact bank16 i bound
    · exact bank17 i bound
    · exact bank18 i bound
    · exact bank19 i bound
    · exact bank20 i bound
    · exact bank21 i bound
    · exact bank22 i bound
    · exact bank23 i bound
    · exact bank24 i bound
    · exact bank25 i bound
    · exact bank26 i bound
    · exact bank27 i bound
    · exact bank28 i bound
    · exact bank29 i bound
    · exact bank30 i bound
    · exact bank31 i bound
    · exact bank32 i bound
  simpa only [checkEntry,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq,and_assoc] using ok

theorem directory : ∀ j : Fin 32, u16 (85440+8*j.val)=size j.val ∧
    u32 (85440+8*j.val+4)=offset j.val := by decide +kernel

theorem limits : ∀ j : Fin 33, size j.val≤952 ∧ offset j.val%2=0 ∧ offset j.val+16*size j.val≤337472 := by decide +kernel

end CommitGolfCandidate.Layout2.Cap
