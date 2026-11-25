import C4W5.Tree.Main
import C4W5.Tree.Sides
import C4W5.Allis.Strategy

/-! A certificate-free router for the accepted complete even-height decomposition.
    The fields are obligations, not axioms. This file alone does not close them. -/
namespace C4W5.Compact
open Connect4 (Player)
open Connect4.NarrowBoards

structure SmallRoots : Prop where
  h2 : Safe 2 (emptyBoard 5)
  c311 : ∀ m : Nat, 2 ≤ m → m ≤ 4 → Safe (2 * m) P311
  c322 : ∀ m : Nat, 2 ≤ m → m ≤ 4 → Safe (2 * m) P322
  c333 : ∀ m : Nat, 2 ≤ m → m ≤ 4 → Safe (2 * m) (T 0)

structure FiniteGaps : Prop where
  c311_10 : Safe 10 P311
  g2_10 : Safe 10 (G 2)
  g3_10 : Safe 10 (G 3)
  g4_10 : Safe 10 (G 4)
  top_10 : Safe 10 (Top 5)
  u_10 : Safe 10 (play (play (T 0) 2 .white) 1 .black)
  g3_12 : Safe 12 (G 3)
  g4_12 : Safe 12 (G 4)
  g5_12 : Safe 12 (G 5)
  top_12 : Safe 12 (Top 6)

structure Zones : Prop where
  c311 : ∀ m : Nat, 6 ≤ m → Safe (2 * m) P311
  c322 : ∀ m : Nat, 5 ≤ m → Safe (2 * m) P322
  c33311 : ∀ m : Nat, 5 ≤ m → Safe (2 * m) (play (play (T 0) 0 .white) 0 .black)
  s113 : ∀ m : Nat, 5 ≤ m → Safe (2 * m) (play (play (T 1) 2 .white) 1 .black)
  s123 : ∀ m : Nat, 5 ≤ m → Safe (2 * m) (play (play (T 2) 2 .white) 4 .black)
  side12 : ∀ (m b : Nat) (q : Fin 5), 5 ≤ m → (b = 1 ∨ b = 2) →
    (q = 0 ∨ q = 4) → Safe (2 * m) (Side b q)
  g1 : ∀ m : Nat, 5 ≤ m → Safe (2 * m) (G 1)
  g2 : ∀ m : Nat, 6 ≤ m → Safe (2 * m) (G 2)
  g4 : ∀ m : Nat, 7 ≤ m → Safe (2 * m) (G 4)
  u : ∀ m : Nat, 6 ≤ m → Safe (2 * m) (play (play (T 0) 2 .white) 1 .black)

structure StretchFamilies : Prop where
  top : ∀ m : Nat, 7 ≤ m → Safe (2 * m) (Top m)
  g3 : ∀ m : Nat, 7 ≤ m → Safe (2 * m) (G 3)
  g5_tight : ∀ b : Nat, 5 ≤ b → Safe (2 * (b + 1)) (G b)
  g5_mid : ∀ b : Nat, 5 ≤ b → Safe (2 * (b + 2)) (G b)
  g5_wide : ∀ m b : Nat, 5 ≤ b → b + 3 ≤ m → Safe (2 * m) (G b)

theorem mixed_side (Z : Zones) (m b : Nat) (q : Fin 5) (hm : 5 ≤ m)
    (h1 : 1 ≤ b) (hb : b + 1 ≤ m) (hq : q = 0 ∨ q = 4) : Safe (2 * m) (Side b q) := by
  by_cases h3 : 3 ≤ b
  · rcases hq with rfl | rfl
    · exact side_first b _ h3 (by omega) (by omega)
    · exact side_fifth b _ h3 (by omega) (by omega)
  · exact Z.side12 m b q hm (by omega) hq

theorem finite_chain5 (F : FiniteGaps) (Z : Zones) : ChainCells 5 where
  side := fun b q h1 hb hq => mixed_side Z 5 b q (by omega) h1 hb hq
  side3 := fun b h3 hb => side_third b _ h3 (by omega) (by omega)
  s113 := Z.s113 5 (by omega)
  s123 := Z.s123 5 (by omega)
  g := fun b h1 hb => by
    have h : b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 := by omega
    rcases h with rfl | rfl | rfl | rfl
    exacts [Z.g1 5 (by omega), F.g2_10, F.g3_10, F.g4_10]
  top := F.top_10
  c33311 := Z.c33311 5 (by omega)
  cU := F.u_10

theorem finite_chain6 (F : FiniteGaps) (Z : Zones) : ChainCells 6 where
  side := fun b q h1 hb hq => mixed_side Z 6 b q (by omega) h1 hb hq
  side3 := fun b h3 hb => side_third b _ h3 (by omega) (by omega)
  s113 := Z.s113 6 (by omega)
  s123 := Z.s123 6 (by omega)
  g := fun b h1 hb => by
    have h : b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 := by omega
    rcases h with rfl | rfl | rfl | rfl | rfl
    exacts [Z.g1 6 (by omega), Z.g2 6 (by omega), F.g3_12, F.g4_12, F.g5_12]
  top := F.top_12
  c33311 := Z.c33311 6 (by omega)
  cU := Z.u 6 (by omega)

theorem g5_dispatch (S : StretchFamilies) (m b : Nat) (hb : 5 ≤ b) (hbm : b + 1 ≤ m) :
    Safe (2 * m) (G b) := by
  have cases : m = b + 1 ∨ m = b + 2 ∨ b + 3 ≤ m := by omega
  rcases cases with rfl | rfl | wide
  · exact S.g5_tight b hb
  · exact S.g5_mid b hb
  · exact S.g5_wide m b hb wide

theorem large_chain (Z : Zones) (S : StretchFamilies) (m : Nat) (hm : 7 ≤ m) : ChainCells m where
  side := fun b q h1 hb hq => mixed_side Z m b q (by omega) h1 hb hq
  side3 := fun b h3 hb => side_third b _ h3 (by omega) (by omega)
  s113 := Z.s113 m (by omega)
  s123 := Z.s123 m (by omega)
  g := fun b h1 hb => by
    have h : b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ 5 ≤ b := by omega
    rcases h with rfl | rfl | rfl | rfl | high
    · exact Z.g1 m (by omega)
    · exact Z.g2 m (by omega)
    · exact S.g3 m hm
    · exact Z.g4 m hm
    · exact g5_dispatch S m b high hb
  top := S.top m hm
  c33311 := Z.c33311 m (by omega)
  cU := Z.u m (by omega)

theorem to_certificates (R : SmallRoots) (F : FiniteGaps) (Z : Zones)
    (S : StretchFamilies) : Certificates where
  small2 := R.h2
  c311 := fun m hm => by
    have cases : m ≤ 4 ∨ m = 5 ∨ 6 ≤ m := by omega
    rcases cases with small | rfl | large
    · exact R.c311 m hm small
    · exact F.c311_10
    · exact Z.c311 m large
  c322 := fun m hm => by
    by_cases small : m ≤ 4
    · exact R.c322 m hm small
    · exact Z.c322 m (by omega)
  t0_small := fun m hm h6 => by
    have cases : m ≤ 4 ∨ m = 5 ∨ m = 6 := by omega
    rcases cases with small | rfl | rfl
    · exact R.c333 m hm small
    · exact T0_safe (by omega) (finite_chain5 F Z)
    · exact T0_safe (by omega) (finite_chain6 F Z)
  chain := large_chain Z S

theorem even_draw_of_contracts (R : SmallRoots) (F : FiniteGaps) (Z : Zones)
    (S : StretchFamilies) {h : Nat} (h2 : 2 ≤ h) (he : h % 2 = 0) : IsDraw h (emptyBoard 5) := by
  have hh : 2 * (h / 2) = h := by omega
  exact ⟨black_nonloss_five_columns_of (to_certificates R F Z S) h2 he,
    hh ▸ FiveAllis.white_nonloss_five (h / 2) (by omega)⟩

#print axioms even_draw_of_contracts
end C4W5.Compact
