import C4W5.Compact.FiniteBridge
import C4W5.Compact.Cert.H10_Top_dedup
import EvenClaimWide.H10_311_known_dag.Main
import EvenClaimWide.H10_G2_known_dag.Main
import EvenClaimWide.H10_G3_known_dag.Main
import EvenClaimWide.H10_G4_known_dag.Main
import EvenClaimWide.H10_U_known_dag.Main
import EvenClaimWide.H12_G3_known_dag.Main
import EvenClaimWide.H12_G4_known_dag.Main
import EvenClaimWide.H12_G5_known_dag.Main
import EvenClaimWide.H12_Top_known_dag.Main

/-! Instantiate finite direct roots. This target is not the unconditional height-12
    empty-board draw: those openings also require the separately specified Zones. -/
namespace C4W5.Compact
open C4W5Gen.FiniteWide

theorem finite_gaps : FiniteGaps := finite_gaps_of_plays {
  c311_10 := H10_311_known_dag.safe
  g2_10 := H10_G2_known_dag.safe
  g3_10 := H10_G3_known_dag.safe
  g4_10 := H10_G4_known_dag.safe
  top_10 := C4W5Gen.WideRealPilot.H10_Top.safe
  u_10 := H10_U_known_dag.safe
  g3_12 := H12_G3_known_dag.safe
  g4_12 := H12_G4_known_dag.safe
  g5_12 := H12_G5_known_dag.safe
  top_12 := H12_Top_known_dag.safe
}

#print axioms finite_gaps
end C4W5.Compact
