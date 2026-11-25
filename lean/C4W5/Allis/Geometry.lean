import C4W5.Allis.Columns

/-!
# Five-column White geometry (Allis §2.2 restricted to five columns)

Geometric core of the White-nonloss route: under the phase-2 and phase-3
column specifications for the fixed special pair `{2, 3}`, Black has no
four-in-a-row on a five-column board.

Phase 2 (`Spec5_2`): column 2 (Black's first entry into the pair) satisfies
`SQ`, column 3 (White's cross answer) satisfies `SEven`, and the ordinary
columns 0, 1, 4 satisfy `SOdd`.  The mirrored orientation (entry column 3)
is `Spec5_2'`, needed because the entry column is Black's choice.

Phase 3 (`Spec5_3 f`): the special column `f ∈ {2, 3}` is full and keeps its
phase-2 specification; the other special column is open (`SOpen`, plus the
bottom / nonempty side conditions carried over from the four-column `Spec3`).
The mirrored orientation is `Spec5_3' f`.

Blocking, from the specifications alone:
* vertical: each column's own spec forbids four consecutive indices
  (`SQ`/`SEven`/`SOdd` forbid two suitably chosen adjacent indices,
  `SOpen` forbids the adjacent pair at indices ≥ 1);
* horizontal: both 4-windows W0 = {0,1,2,3} and W1 = {1,2,3,4} contain
  column 1 and column 3, so odd rows are blocked by `SOdd` on column 1 and
  even rows by `SEven` on column 3 (phase 2, and phase 3 with f = 3);
  with f = 2 even rows split: row 0 is blocked by the bottom cell of the
  open column 3, rows ≥ 2 by `SQ` on column 2;
* diagonals: each 4-window contains two ordinary columns an odd column
  distance apart (W0 has 0, 1 at distance 1; W1 has 1, 4 at distance 3).
  A dx = ±1 diagonal steps one row per column, so those two Black stones
  sit at rows of opposite parity, and `SOdd` fails on one of them.
-/

namespace FiveAllis

open Connect4 (Player opponent)
open Connect4.NarrowBoards

/-! ## Diagonal parity across an odd column distance

The four-column baseline proves `diag_parity` for column distance one only.
A five-column board has two 4-windows, and the second needs distance three;
both are captured by the four lemmas below (rising and falling direction). -/

/-- Rising diagonal, columns one apart: Black stones at rows `y`, `y + 1`
cannot both sit at even 0-based indices. -/
theorem diag_parity_d1 {y : Int} {n1 n2 : Nat}
    (hn1 : (y + 1).toNat = n1) (hb1 : 0 ≤ y + 1) (hn2 : y.toNat = n2) (hb2 : 0 ≤ y)
    (p1 : n1 % 2 = 0) (p2 : n2 % 2 = 0) : False := by omega

/-- Rising diagonal, columns three apart: rows `y`, `y + 3`. -/
theorem diag_parity_d3 {y : Int} {n1 n2 : Nat}
    (hn1 : (y + 3).toNat = n1) (hb1 : 0 ≤ y + 3) (hn2 : y.toNat = n2) (hb2 : 0 ≤ y)
    (p1 : n1 % 2 = 0) (p2 : n2 % 2 = 0) : False := by omega

/-- Falling diagonal, columns one apart: rows `y`, `y - 1`. -/
theorem diag_parity_neg_d1 {y : Int} {n1 n2 : Nat}
    (hn1 : (y - 1).toNat = n1) (hb1 : 0 ≤ y - 1) (hn2 : y.toNat = n2) (hb2 : 0 ≤ y)
    (p1 : n1 % 2 = 0) (p2 : n2 % 2 = 0) : False := by omega

/-- Falling diagonal, columns three apart: rows `y`, `y - 3`. -/
theorem diag_parity_neg_d3 {y : Int} {n1 n2 : Nat}
    (hn1 : (y - 3).toNat = n1) (hb1 : 0 ≤ y - 3) (hn2 : y.toNat = n2) (hb2 : 0 ≤ y)
    (p1 : n1 % 2 = 0) (p2 : n2 % 2 = 0) : False := by omega

/-! ## Stone extraction on dx = 1 lines (five-column translation of the
private four-column `line_stones`) -/

/-- A stone of a dx = 1 line at column offset `k < 4`: its column is
`x + k` and its 0-based row is `(y + k * dy).toNat`. -/
private theorem line_stones5 {h : Nat} {P : Board 5} {x y dy : Int}
    (hd : HasFourDir h P .black x y 1 dy) (k : Nat) (hk : k < 4) :
    ∃ n : Nat, (y + (k : Int) * dy).toNat = n ∧ 0 ≤ y + (k : Int) * dy ∧
      ∀ c : Fin 5, (c : Int) = x + k → stone (P c) n = some .black := by
  have hdi := hd ⟨k, hk⟩
  obtain ⟨c, hxc, hyc, -, sc⟩ := cellAtInt_some hdi
  have hcoe : ((⟨k, hk⟩ : Fin 4) : Int) = (k : Int) := rfl
  rw [hcoe] at hxc hyc sc
  refine ⟨_, rfl, hyc, ?_⟩
  intro c' hc'
  have hce : c' = c := Fin.ext (by omega)
  rw [hce]
  exact sc

/-- `line_stones5` instantated at one concrete column. -/
private theorem stone_at_col {h : Nat} {P : Board 5} {x y dy : Int}
    (hd : HasFourDir h P .black x y 1 dy) (k : Nat) (hk : k < 4) (c : Fin 5)
    (hc : (c : Int) = x + k) :
    ∃ n : Nat, (y + (k : Int) * dy).toNat = n ∧ 0 ≤ y + (k : Int) * dy ∧
      stone (P c) n = some .black := by
  obtain ⟨n, hn, hb, hcc⟩ := line_stones5 hd k hk
  exact ⟨n, hn, hb, hcc c hc⟩

/-- Every dx = 1 line on five columns starts at column 0 or 1. -/
private theorem line_x01 {h : Nat} {P : Board 5} {x y dy : Int}
    (hd : HasFourDir h P .black x y 1 dy) : x = 0 ∨ x = 1 := by
  have s0 := hd ⟨0, by decide⟩
  have s3 := hd ⟨3, by decide⟩
  obtain ⟨c0, hx0, -, -, -⟩ := cellAtInt_some s0
  obtain ⟨c3, hx3, -, -, -⟩ := cellAtInt_some s3
  have hl0 : ((⟨0, by decide⟩ : Fin 4) : Int) = 0 := rfl
  have hl3 : ((⟨3, by decide⟩ : Fin 4) : Int) = 3 := rfl
  rw [hl0] at hx0
  rw [hl3] at hx3
  have hc0 := c0.isLt
  have hc3 := c3.isLt
  omega

/-- Three consecutive stones of a vertical line, all in one column. -/
private theorem vert_stones {h : Nat} {P : Board 5} {x y : Int}
    (hd : HasFourDir h P .black x y 0 1) :
    ∃ c : Fin 5, stone (P c) y.toNat = some .black ∧
      stone (P c) (y.toNat + 1) = some .black ∧
      stone (P c) (y.toNat + 2) = some .black := by
  have s0 : cellAtInt h P x y = some Player.black := by simpa using hd ⟨0, by decide⟩
  have s1 : cellAtInt h P x (y + 1) = some Player.black := by simpa using hd ⟨1, by decide⟩
  have s2 : cellAtInt h P x (y + 2) = some Player.black := by simpa using hd ⟨2, by decide⟩
  obtain ⟨c0, hx0, hy0, -, t0⟩ := cellAtInt_some s0
  obtain ⟨c1, hx1, -, -, t1⟩ := cellAtInt_some s1
  obtain ⟨c2, hx2, -, -, t2⟩ := cellAtInt_some s2
  have q1 : c1 = c0 := Fin.ext (by omega)
  have q2 : c2 = c0 := Fin.ext (by omega)
  rw [q1] at t1
  rw [q2] at t2
  have i1 : (y + 1).toNat = y.toNat + 1 := by omega
  have i2 : (y + 2).toNat = y.toNat + 2 := by omega
  rw [i1] at t1
  rw [i2] at t2
  exact ⟨c0, t0, t1, t2⟩

/-! ## Vertical four versus each column specification -/

private theorem vert_sOdd {l : List Player} {m : Nat}
    (t0 : stone l m = some .black) (t1 : stone l (m + 1) = some .black)
    (hs : SOdd l) : False := by
  by_cases hn : m % 2 = 0
  · have := hs (m + 1) t1; omega
  · have := hs m t0; omega

private theorem vert_sEven {l : List Player} {m : Nat}
    (t0 : stone l m = some .black) (t1 : stone l (m + 1) = some .black)
    (hs : SEven l) : False := by
  by_cases hn : m % 2 = 0
  · have := hs m t0; omega
  · have := hs (m + 1) t1; omega

private theorem vert_sQ {l : List Player} {m : Nat}
    (t1 : stone l (m + 1) = some .black) (t2 : stone l (m + 2) = some .black)
    (hs : SQ l) : False := by
  by_cases hn : m % 2 = 0
  · rcases hs (m + 2) t2 with hh | hh <;> omega
  · rcases hs (m + 1) t1 with hh | hh <;> omega

private theorem vert_sOpen {l : List Player} {m : Nat}
    (t1 : stone l (m + 1) = some .black) (t2 : stone l (m + 2) = some .black)
    (hs : SOpen l) : False := by
  have := hs (m + 1) t1 t2
  omega

/-! ## Horizontal four: column 1 blocks odd rows, column 3 even rows -/

/-- Odd row: every 4-window contains the ordinary column 1. -/
private theorem horiz_odd_R {h : Nat} {P : Board 5}
    (hR : ∀ c : Fin 5, c.val ≠ 2 ∧ c.val ≠ 3 → SOdd (P c))
    {x y : Int} (hd : HasFourDir h P .black x y 1 0) (hodd : y.toNat % 2 = 1) :
    False := by
  have s0 := hd ⟨0, by decide⟩
  obtain ⟨-, -, hy0, -, -⟩ := cellAtInt_some s0
  rcases line_x01 hd with hx | hx
  · subst hx
    obtain ⟨n, hn, -, s⟩ := stone_at_col hd 1 (by decide) 1 (by decide)
    have := hR 1 (by decide) _ s
    omega
  · subst hx
    obtain ⟨n, hn, -, s⟩ := stone_at_col hd 0 (by decide) 1 (by decide)
    have := hR 1 (by decide) _ s
    omega

/-- Even row with `SEven` on one special column: every 4-window contains
both special columns, so either one blocks. -/
private theorem horiz_even_sEven_col {h : Nat} {P : Board 5} {x y : Int}
    (hd : HasFourDir h P .black x y 1 0) (heven : y.toNat % 2 = 0)
    {c : Fin 5} (hc : c = 2 ∨ c = 3) (hs : SEven (P c)) : False := by
  rcases hc with hc | hc
  · subst hc
    rcases line_x01 hd with hx | hx
    · subst hx
      obtain ⟨n, hn, -, s⟩ := stone_at_col hd 2 (by decide) 2 (by decide)
      have := hs _ s
      omega
    · subst hx
      obtain ⟨n, hn, -, s⟩ := stone_at_col hd 1 (by decide) 2 (by decide)
      have := hs _ s
      omega
  · subst hc
    rcases line_x01 hd with hx | hx
    · subst hx
      obtain ⟨n, hn, -, s⟩ := stone_at_col hd 3 (by decide) 3 (by decide)
      have := hs _ s
      omega
    · subst hx
      obtain ⟨n, hn, -, s⟩ := stone_at_col hd 2 (by decide) 3 (by decide)
      have := hs _ s
      omega

/-- Even row when the kept column `u` carries `SQ` and the open column `v`
is the other special column: row 0 is blocked by the bottom cell of `v`,
rows ≥ 2 by `SQ` on `u`; both windows contain both columns. -/
private theorem horiz_even_sq_bot {h : Nat} {P : Board 5} {x y : Int}
    (hd : HasFourDir h P .black x y 1 0) (heven : y.toNat % 2 = 0)
    {u v : Fin 5} (huv : (u = 2 ∧ v = 3) ∨ (u = 3 ∧ v = 2))
    (hq : SQ (P u)) (hbot : stone (P v) 0 ≠ some .black) : False := by
  rcases huv with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · subst hu
    subst hv
    rcases line_x01 hd with hx | hx
    · subst hx
      by_cases h0 : y.toNat = 0
      · obtain ⟨n, hn, -, s⟩ := stone_at_col hd 3 (by decide) 3 (by decide)
        have hn0 : n = 0 := by omega
        rw [hn0] at s
        exact hbot s
      · obtain ⟨n, hn, -, s⟩ := stone_at_col hd 2 (by decide) 2 (by decide)
        rcases hq _ s with hh | hh <;> omega
    · subst hx
      by_cases h0 : y.toNat = 0
      · obtain ⟨n, hn, -, s⟩ := stone_at_col hd 2 (by decide) 3 (by decide)
        have hn0 : n = 0 := by omega
        rw [hn0] at s
        exact hbot s
      · obtain ⟨n, hn, -, s⟩ := stone_at_col hd 1 (by decide) 2 (by decide)
        rcases hq _ s with hh | hh <;> omega
  · subst hu
    subst hv
    rcases line_x01 hd with hx | hx
    · subst hx
      by_cases h0 : y.toNat = 0
      · obtain ⟨n, hn, -, s⟩ := stone_at_col hd 2 (by decide) 2 (by decide)
        have hn0 : n = 0 := by omega
        rw [hn0] at s
        exact hbot s
      · obtain ⟨n, hn, -, s⟩ := stone_at_col hd 3 (by decide) 3 (by decide)
        rcases hq _ s with hh | hh <;> omega
    · subst hx
      by_cases h0 : y.toNat = 0
      · obtain ⟨n, hn, -, s⟩ := stone_at_col hd 1 (by decide) 2 (by decide)
        have hn0 : n = 0 := by omega
        rw [hn0] at s
        exact hbot s
      · obtain ⟨n, hn, -, s⟩ := stone_at_col hd 2 (by decide) 3 (by decide)
        rcases hq _ s with hh | hh <;> omega

/-! ## Diagonals: two ordinary columns at odd distance in each window -/

/-- Rising diagonal. Window W0 uses ordinary columns 0, 1 (distance 1);
window W1 uses ordinary columns 1, 4 (distance 3). -/
private theorem no_diag5_up {h : Nat} {P : Board 5}
    (hR : ∀ c : Fin 5, c.val ≠ 2 ∧ c.val ≠ 3 → SOdd (P c))
    {x y : Int} (hd : HasFourDir h P .black x y 1 1) : False := by
  rcases line_x01 hd with hx | hx
  · subst hx
    obtain ⟨n1, hn1, hb1, s1⟩ := stone_at_col hd 0 (by decide) 0 (by decide)
    obtain ⟨n2, hn2, hb2, s2⟩ := stone_at_col hd 1 (by decide) 1 (by decide)
    have p1 := hR 0 (by decide) _ s1
    have p2 := hR 1 (by decide) _ s2
    have e2 : (y + 1).toNat = n2 := by omega
    have b2 : 0 ≤ y + 1 := by omega
    have e1 : y.toNat = n1 := by omega
    have b1 : 0 ≤ y := by omega
    exact diag_parity_d1 e2 b2 e1 b1 p2 p1
  · subst hx
    obtain ⟨n1, hn1, hb1, s1⟩ := stone_at_col hd 0 (by decide) 1 (by decide)
    obtain ⟨n2, hn2, hb2, s2⟩ := stone_at_col hd 3 (by decide) 4 (by decide)
    have p1 := hR 1 (by decide) _ s1
    have p2 := hR 4 (by decide) _ s2
    have e2 : (y + 3).toNat = n2 := by omega
    have b2 : 0 ≤ y + 3 := by omega
    have e1 : y.toNat = n1 := by omega
    have b1 : 0 ≤ y := by omega
    exact diag_parity_d3 e2 b2 e1 b1 p2 p1

/-- Falling diagonal, same two column pairs. -/
private theorem no_diag5_down {h : Nat} {P : Board 5}
    (hR : ∀ c : Fin 5, c.val ≠ 2 ∧ c.val ≠ 3 → SOdd (P c))
    {x y : Int} (hd : HasFourDir h P .black x y 1 (-1)) : False := by
  rcases line_x01 hd with hx | hx
  · subst hx
    obtain ⟨n1, hn1, hb1, s1⟩ := stone_at_col hd 0 (by decide) 0 (by decide)
    obtain ⟨n2, hn2, hb2, s2⟩ := stone_at_col hd 1 (by decide) 1 (by decide)
    have p1 := hR 0 (by decide) _ s1
    have p2 := hR 1 (by decide) _ s2
    have e2 : (y - 1).toNat = n2 := by omega
    have b2 : 0 ≤ y - 1 := by omega
    have e1 : y.toNat = n1 := by omega
    have b1 : 0 ≤ y := by omega
    exact diag_parity_neg_d1 e2 b2 e1 b1 p2 p1
  · subst hx
    obtain ⟨n1, hn1, hb1, s1⟩ := stone_at_col hd 0 (by decide) 1 (by decide)
    obtain ⟨n2, hn2, hb2, s2⟩ := stone_at_col hd 3 (by decide) 4 (by decide)
    have p1 := hR 1 (by decide) _ s1
    have p2 := hR 4 (by decide) _ s2
    have e2 : (y - 3).toNat = n2 := by omega
    have b2 : 0 ≤ y - 3 := by omega
    have e1 : y.toNat = n1 := by omega
    have b1 : 0 ≤ y := by omega
    exact diag_parity_neg_d3 e2 b2 e1 b1 p2 p1

/-! ## Phase 2 -/

/-- Phase-2 specification, fixed orientation: column 2 is Black's first
entry into the special pair (`SQ`), column 3 the cross answer (`SEven`),
columns 0, 1, 4 ordinary (`SOdd`). -/
def Spec5_2 (P : Board 5) : Prop :=
  SQ (P 2) ∧ SEven (P 3) ∧ (∀ c : Fin 5, c.val ≠ 2 ∧ c.val ≠ 3 → SOdd (P c))

theorem no_black_four_5col_phase2 {h : Nat} {P : Board 5} (hs : Spec5_2 P) :
    ¬ HasFour h P .black := by
  intro hf
  rcases hf with ⟨x, y, hd⟩ | ⟨x, y, hd⟩ | ⟨x, y, hd⟩ | ⟨x, y, hd⟩
  · obtain ⟨c, t0, t1, t2⟩ := vert_stones hd
    have hv := c.isLt
    by_cases hz : c.val = 0
    · have hce : c = 0 := Fin.ext hz
      rw [hce] at t0 t1
      exact vert_sOdd t0 t1 (hs.2.2 0 (by decide))
    · by_cases hone : c.val = 1
      · have hce : c = 1 := Fin.ext hone
        rw [hce] at t0 t1
        exact vert_sOdd t0 t1 (hs.2.2 1 (by decide))
      · by_cases htwo : c.val = 2
        · have hce : c = 2 := Fin.ext htwo
          rw [hce] at t1 t2
          exact vert_sQ t1 t2 hs.1
        · by_cases hthree : c.val = 3
          · have hce : c = 3 := Fin.ext hthree
            rw [hce] at t0 t1
            exact vert_sEven t0 t1 hs.2.1
          · have hce : c = 4 := Fin.ext (by omega)
            rw [hce] at t0 t1
            exact vert_sOdd t0 t1 (hs.2.2 4 (by decide))
  · by_cases hodd : y.toNat % 2 = 1
    · exact horiz_odd_R hs.2.2 hd hodd
    · exact horiz_even_sEven_col hd (by omega) (Or.inr rfl) hs.2.1
  · exact no_diag5_up hs.2.2 hd
  · exact no_diag5_down hs.2.2 hd

/-! ## Mirrored phase-2 orientation -/

/-- Phase-2 specification, mirrored orientation: Black's first entry into
the special pair is column 3 (`SQ`), White's cross answer column 2
(`SEven`); the ordinary columns are unchanged. -/
def Spec5_2' (P : Board 5) : Prop :=
  SQ (P 3) ∧ SEven (P 2) ∧ (∀ c : Fin 5, c.val ≠ 2 ∧ c.val ≠ 3 → SOdd (P c))

theorem no_black_four_5col_phase2' {h : Nat} {P : Board 5} (hs : Spec5_2' P) :
    ¬ HasFour h P .black := by
  intro hf
  rcases hf with ⟨x, y, hd⟩ | ⟨x, y, hd⟩ | ⟨x, y, hd⟩ | ⟨x, y, hd⟩
  · obtain ⟨c, t0, t1, t2⟩ := vert_stones hd
    have hv := c.isLt
    by_cases hz : c.val = 0
    · have hce : c = 0 := Fin.ext hz
      rw [hce] at t0 t1
      exact vert_sOdd t0 t1 (hs.2.2 0 (by decide))
    · by_cases hone : c.val = 1
      · have hce : c = 1 := Fin.ext hone
        rw [hce] at t0 t1
        exact vert_sOdd t0 t1 (hs.2.2 1 (by decide))
      · by_cases htwo : c.val = 2
        · have hce : c = 2 := Fin.ext htwo
          rw [hce] at t0 t1
          exact vert_sEven t0 t1 hs.2.1
        · by_cases hthree : c.val = 3
          · have hce : c = 3 := Fin.ext hthree
            rw [hce] at t1 t2
            exact vert_sQ t1 t2 hs.1
          · have hce : c = 4 := Fin.ext (by omega)
            rw [hce] at t0 t1
            exact vert_sOdd t0 t1 (hs.2.2 4 (by decide))
  · by_cases hodd : y.toNat % 2 = 1
    · exact horiz_odd_R hs.2.2 hd hodd
    · exact horiz_even_sEven_col hd (by omega) (Or.inl rfl) hs.2.1
  · exact no_diag5_up hs.2.2 hd
  · exact no_diag5_down hs.2.2 hd

/-! ## Phase 3 -/

/-- The special column other than `f`. -/
def other5 (f : Fin 5) : Fin 5 := if f = 2 then 3 else 2

theorem other5_2 : other5 (2 : Fin 5) = 3 := by decide
theorem other5_3 : other5 (3 : Fin 5) = 2 := by decide

/-- Phase-3 specification: the special column `f` is filled and keeps its
phase-2 specification (`SQ` if f = 2, `SEven` if f = 3); the other special
column is open, with the bottom / nonempty side conditions of the
four-column `Spec3`. -/
structure Spec5_3 (f : Fin 5) (P : Board 5) : Prop where
  fPair : f = 2 ∨ f = 3
  rOdd : ∀ c : Fin 5, c.val ≠ 2 ∧ c.val ≠ 3 → SOdd (P c)
  keptQ : f = 2 → SQ (P 2)
  keptE : f = 3 → SEven (P 3)
  openCol : SOpen (P (other5 f))
  bottom : f = 2 → stone (P (other5 f)) 0 ≠ some .black
  nonempty : 1 ≤ (P (other5 f)).length

/-- Phase 3, filled column f = 2: column 2 keeps `SQ`, column 3 is open. -/
private theorem nbf5_f2 {h : Nat} {P : Board 5}
    (hR : ∀ c : Fin 5, c.val ≠ 2 ∧ c.val ≠ 3 → SOdd (P c))
    (hq : SQ (P 2)) (ho : SOpen (P 3)) (hbot : stone (P 3) 0 ≠ some .black) :
    ¬ HasFour h P .black := by
  intro hf
  rcases hf with ⟨x, y, hd⟩ | ⟨x, y, hd⟩ | ⟨x, y, hd⟩ | ⟨x, y, hd⟩
  · obtain ⟨c, t0, t1, t2⟩ := vert_stones hd
    have hv := c.isLt
    by_cases hz : c.val = 0
    · have hce : c = 0 := Fin.ext hz
      rw [hce] at t0 t1
      exact vert_sOdd t0 t1 (hR 0 (by decide))
    · by_cases hone : c.val = 1
      · have hce : c = 1 := Fin.ext hone
        rw [hce] at t0 t1
        exact vert_sOdd t0 t1 (hR 1 (by decide))
      · by_cases htwo : c.val = 2
        · have hce : c = 2 := Fin.ext htwo
          rw [hce] at t1 t2
          exact vert_sQ t1 t2 hq
        · by_cases hthree : c.val = 3
          · have hce : c = 3 := Fin.ext hthree
            rw [hce] at t1 t2
            exact vert_sOpen t1 t2 ho
          · have hce : c = 4 := Fin.ext (by omega)
            rw [hce] at t0 t1
            exact vert_sOdd t0 t1 (hR 4 (by decide))
  · by_cases hodd : y.toNat % 2 = 1
    · exact horiz_odd_R hR hd hodd
    · exact horiz_even_sq_bot hd (by omega) (Or.inl ⟨rfl, rfl⟩) hq hbot
  · exact no_diag5_up hR hd
  · exact no_diag5_down hR hd

/-- Phase 3, filled column f = 3: column 3 keeps `SEven`, column 2 is open. -/
private theorem nbf5_f3 {h : Nat} {P : Board 5}
    (hR : ∀ c : Fin 5, c.val ≠ 2 ∧ c.val ≠ 3 → SOdd (P c))
    (he : SEven (P 3)) (ho : SOpen (P 2)) :
    ¬ HasFour h P .black := by
  intro hf
  rcases hf with ⟨x, y, hd⟩ | ⟨x, y, hd⟩ | ⟨x, y, hd⟩ | ⟨x, y, hd⟩
  · obtain ⟨c, t0, t1, t2⟩ := vert_stones hd
    have hv := c.isLt
    by_cases hz : c.val = 0
    · have hce : c = 0 := Fin.ext hz
      rw [hce] at t0 t1
      exact vert_sOdd t0 t1 (hR 0 (by decide))
    · by_cases hone : c.val = 1
      · have hce : c = 1 := Fin.ext hone
        rw [hce] at t0 t1
        exact vert_sOdd t0 t1 (hR 1 (by decide))
      · by_cases htwo : c.val = 2
        · have hce : c = 2 := Fin.ext htwo
          rw [hce] at t1 t2
          exact vert_sOpen t1 t2 ho
        · by_cases hthree : c.val = 3
          · have hce : c = 3 := Fin.ext hthree
            rw [hce] at t0 t1
            exact vert_sEven t0 t1 he
          · have hce : c = 4 := Fin.ext (by omega)
            rw [hce] at t0 t1
            exact vert_sOdd t0 t1 (hR 4 (by decide))
  · by_cases hodd : y.toNat % 2 = 1
    · exact horiz_odd_R hR hd hodd
    · exact horiz_even_sEven_col hd (by omega) (Or.inr rfl) he
  · exact no_diag5_up hR hd
  · exact no_diag5_down hR hd

theorem no_black_four_5col_phase3 {h : Nat} {f : Fin 5} {P : Board 5}
    (hs : Spec5_3 f P) : ¬ HasFour h P .black := by
  rcases hs.fPair with hf | hf
  · subst hf
    have ho : SOpen (P 3) := by rw [← other5_2]; exact hs.openCol
    have hb : stone (P 3) 0 ≠ some .black := by rw [← other5_2]; exact hs.bottom rfl
    exact nbf5_f2 hs.rOdd (hs.keptQ rfl) ho hb
  · subst hf
    have ho : SOpen (P 2) := by rw [← other5_3]; exact hs.openCol
    exact nbf5_f3 hs.rOdd (hs.keptE rfl) ho

/-! ## Mirrored phase-3 orientation -/

/-- Phase-3 specification, mirrored orientation (Black's first entry into
the pair was column 3): the filled column `f` keeps `SQ` when f = 3 and
`SEven` when f = 2; the other special column is open. -/
structure Spec5_3' (f : Fin 5) (P : Board 5) : Prop where
  fPair : f = 2 ∨ f = 3
  rOdd : ∀ c : Fin 5, c.val ≠ 2 ∧ c.val ≠ 3 → SOdd (P c)
  keptQ : f = 3 → SQ (P 3)
  keptE : f = 2 → SEven (P 2)
  openCol : SOpen (P (other5 f))
  bottom : f = 3 → stone (P (other5 f)) 0 ≠ some .black
  nonempty : 1 ≤ (P (other5 f)).length

/-- Mirrored phase 3, filled column f = 2: column 2 keeps `SEven`,
column 3 is open. -/
private theorem nbf5_f2' {h : Nat} {P : Board 5}
    (hR : ∀ c : Fin 5, c.val ≠ 2 ∧ c.val ≠ 3 → SOdd (P c))
    (he : SEven (P 2)) (ho : SOpen (P 3)) :
    ¬ HasFour h P .black := by
  intro hf
  rcases hf with ⟨x, y, hd⟩ | ⟨x, y, hd⟩ | ⟨x, y, hd⟩ | ⟨x, y, hd⟩
  · obtain ⟨c, t0, t1, t2⟩ := vert_stones hd
    have hv := c.isLt
    by_cases hz : c.val = 0
    · have hce : c = 0 := Fin.ext hz
      rw [hce] at t0 t1
      exact vert_sOdd t0 t1 (hR 0 (by decide))
    · by_cases hone : c.val = 1
      · have hce : c = 1 := Fin.ext hone
        rw [hce] at t0 t1
        exact vert_sOdd t0 t1 (hR 1 (by decide))
      · by_cases htwo : c.val = 2
        · have hce : c = 2 := Fin.ext htwo
          rw [hce] at t0 t1
          exact vert_sEven t0 t1 he
        · by_cases hthree : c.val = 3
          · have hce : c = 3 := Fin.ext hthree
            rw [hce] at t1 t2
            exact vert_sOpen t1 t2 ho
          · have hce : c = 4 := Fin.ext (by omega)
            rw [hce] at t0 t1
            exact vert_sOdd t0 t1 (hR 4 (by decide))
  · by_cases hodd : y.toNat % 2 = 1
    · exact horiz_odd_R hR hd hodd
    · exact horiz_even_sEven_col hd (by omega) (Or.inl rfl) he
  · exact no_diag5_up hR hd
  · exact no_diag5_down hR hd

/-- Mirrored phase 3, filled column f = 3: column 3 keeps `SQ`,
column 2 is open. -/
private theorem nbf5_f3' {h : Nat} {P : Board 5}
    (hR : ∀ c : Fin 5, c.val ≠ 2 ∧ c.val ≠ 3 → SOdd (P c))
    (hq : SQ (P 3)) (ho : SOpen (P 2)) (hbot : stone (P 2) 0 ≠ some .black) :
    ¬ HasFour h P .black := by
  intro hf
  rcases hf with ⟨x, y, hd⟩ | ⟨x, y, hd⟩ | ⟨x, y, hd⟩ | ⟨x, y, hd⟩
  · obtain ⟨c, t0, t1, t2⟩ := vert_stones hd
    have hv := c.isLt
    by_cases hz : c.val = 0
    · have hce : c = 0 := Fin.ext hz
      rw [hce] at t0 t1
      exact vert_sOdd t0 t1 (hR 0 (by decide))
    · by_cases hone : c.val = 1
      · have hce : c = 1 := Fin.ext hone
        rw [hce] at t0 t1
        exact vert_sOdd t0 t1 (hR 1 (by decide))
      · by_cases htwo : c.val = 2
        · have hce : c = 2 := Fin.ext htwo
          rw [hce] at t1 t2
          exact vert_sOpen t1 t2 ho
        · by_cases hthree : c.val = 3
          · have hce : c = 3 := Fin.ext hthree
            rw [hce] at t1 t2
            exact vert_sQ t1 t2 hq
          · have hce : c = 4 := Fin.ext (by omega)
            rw [hce] at t0 t1
            exact vert_sOdd t0 t1 (hR 4 (by decide))
  · by_cases hodd : y.toNat % 2 = 1
    · exact horiz_odd_R hR hd hodd
    · exact horiz_even_sq_bot hd (by omega) (Or.inr ⟨rfl, rfl⟩) hq hbot
  · exact no_diag5_up hR hd
  · exact no_diag5_down hR hd

theorem no_black_four_5col_phase3' {h : Nat} {f : Fin 5} {P : Board 5}
    (hs : Spec5_3' f P) : ¬ HasFour h P .black := by
  rcases hs.fPair with hf | hf
  · subst hf
    have ho : SOpen (P 3) := by rw [← other5_2]; exact hs.openCol
    exact nbf5_f2' hs.rOdd (hs.keptE rfl) ho
  · subst hf
    have ho : SOpen (P 2) := by rw [← other5_3]; exact hs.openCol
    have hb : stone (P 2) 0 ≠ some .black := by rw [← other5_3]; exact hs.bottom rfl
    exact nbf5_f3' hs.rOdd (hs.keptQ rfl) ho hb

end FiveAllis
