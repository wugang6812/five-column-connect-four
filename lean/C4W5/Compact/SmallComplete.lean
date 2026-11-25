import C4W5.Compact.Contracts
import C4W5.Compact.Small

namespace C4W5.Compact

theorem small_roots : SmallRoots where
  h2 := safe2
  c311 := fun m hm h4 => by
    have h : m = 2 ∨ m = 3 ∨ m = 4 := by omega
    rcases h with rfl | rfl | rfl
    exacts [safe311_4, safe311_6, safe311_8]
  c322 := fun m hm h4 => by
    have h : m = 2 ∨ m = 3 ∨ m = 4 := by omega
    rcases h with rfl | rfl | rfl
    exacts [safe322_4, safe322_6, safe322_8]
  c333 := fun m hm h4 => by
    have h : m = 2 ∨ m = 3 ∨ m = 4 := by omega
    rcases h with rfl | rfl | rfl
    exacts [safe333_4, safe333_6, safe333_8]

#print axioms small_roots
end C4W5.Compact
