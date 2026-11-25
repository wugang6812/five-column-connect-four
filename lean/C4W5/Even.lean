import C4W5.Compact.SmallComplete
import C4W5.Compact.FiniteCandidate
import C4W5.Compact.ZoneComplete
import C4W5.Compact.StretchComplete
import C4W5.Compact.Openings

/-! Final compact public source. These declarations require all checked Main
    imports; no former large strategy table is a fallback. -/
namespace C4W5
open Connect4 (Player)
open Connect4.NarrowBoards

theorem compact_certificates : Certificates :=
  Compact.to_certificates Compact.small_roots Compact.finite_gaps
    Compact.zones Compact.stretch_families

theorem compact_center_two : Safe 2 Compact.centerOpening :=
  C4W5Gen.EvenCompact.H2_3.safe

/-- On five columns the empty board is a draw at every positive even height. -/
theorem five_columns_even_draw {h : Nat} (h₂ : 2 ≤ h) (he : h % 2 = 0) :
    IsDraw h (emptyBoard 5) :=
  Compact.even_draw_of_contracts Compact.small_roots Compact.finite_gaps
    Compact.zones Compact.stretch_families h₂ he

#print axioms compact_certificates
#print axioms five_columns_even_draw
end C4W5
