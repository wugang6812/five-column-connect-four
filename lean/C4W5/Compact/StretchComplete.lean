import C4W5.Compact.StretchRoutes
import STopLongPacked.Main
import SG3LongPacked.Main
import SG5LongPacked.Main
import SGZLongPacked.Main

/-! Final unbounded source route. This deliberately imports the actual Main modules;
    it must not be accepted before every one has been verified. -/
namespace C4W5.Compact

theorem stretch_families : StretchFamilies :=
  stretch_families_of
    STopLongPacked.top_all
    SG3LongPacked.g3_all
    SG5LongPacked.g5_tight
    SG5LongPacked.g5_mid
    SGZLongPacked.g5_wide

#print axioms stretch_families
end C4W5.Compact
