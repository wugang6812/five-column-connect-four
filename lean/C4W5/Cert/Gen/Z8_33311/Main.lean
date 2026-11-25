import C4W5.CompactZone.Z8_33311.Check0
import C4W5.CompactZone.Z8_33311.Check1
import C4W5.CompactZone.Z8_33311.Check2
import C4W5.CompactZone.Z8_33311.Check3
import C4W5.CompactZone.Z8_33311.Check4
import C4W5.CompactZone.Z8_33311.Check5
import C4W5.CompactZone.Z8_33311.Check6
import C4W5.CompactZone.Z8_33311.Check7
import C4W5.CompactZone.Z8_33311.Check8

namespace C4W5.Z8_33311
open Connect4 (Player opponent)
open Connect4.NarrowBoards C4W5.PackedBank
open C4W5.CompactZone.Z8_33311
open C4W5.CompactZone.ClaimBank
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

private theorem ok : all fmt.radix (zcheckRowL 8 fmt t) t = true :=
  (all_branch (all_branch (all_branch bank0_ok bank1_ok) (all_branch bank2_ok bank3_ok)) (all_branch (all_branch bank4_ok bank5_ok) (all_branch bank6_ok (all_branch bank7_ok bank8_ok))))

theorem safe (H : Nat) (hH : H % 2 = 0) (hKH : 8 + 2 ≤ H) : Safe H (playList (emptyBoard 5) .black [2, 2, 2, 0, 0]) :=
  zone_safe_of_claim_bank (by decide) hH hKH fmt t [2, 2, 2, 0, 0] ⟨2,0,5,0,0,2,0,3,0,0⟩
    (by decide +kernel) ok (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C4W5.Z8_33311.safe

end C4W5.Z8_33311
