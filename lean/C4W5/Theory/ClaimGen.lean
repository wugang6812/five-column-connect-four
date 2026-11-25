import C4W5.Theory.ShiftDownGen
import C4W5.Base.Steps

/-!
# Unified Color-Polymorphic Claim Criterion (`ClaimGen`)

Unifies BOTH empty-cell parity regimes for an arbitrary defender `me : Player`
(attacker `opp := opponent me`) on a 5-column board of arbitrary height `H`:
1. **Odd-Empty Regime** (`(H + turnParity opp) % 2 = 1`): Even-height Black, Odd-height White.
   - `claim_odd_safe` (`ClaimOddHyp`): claims a single column `q` with `(H - |R q|) % 2 = 1`.
2. **Even-Empty Regime** (`(H + turnParity opp) % 2 = 0`): Odd-height Black, Even-height White.
   - `claim_even_safe` (`ClaimEvenHyp`): simultaneously claims ALL non-full columns `c` with
     `(H - |R c|) % 2 = 0` (strictly dominant, O(1) bitmask without subset search).

Also proves the color-polymorphic truncation lifting lemma `dead_of_trunc_gen`
(lifting `LinesDeadSet` from `trunc K R` to `R` for any `K ≤ H`).

Zero `sorry`, zero custom axioms.
-/

namespace C4W5Gen
open Connect4 (Player opponent)
open Connect4.NarrowBoards
open C4W5

set_option linter.deprecated false

/-- Turn parity: Black moves on even stone counts (0), White on odd stone counts (1). -/
def turnParity : Player → Nat
  | .black => 0
  | .white => 1

/-- Parity of remaining empty cells `5 * H - totalStones R` when `toMove R = opp`. -/
def emptyParity (H : Nat) (opp : Player) : Nat :=
  (H + turnParity opp) % 2

/-- Defender global safety parameterized by defender color `me`. -/
abbrev SafeP (H : Nat) (me : Player) (R : Board 5) : Prop :=
  CanAvoidLoss H me R

@[simp] theorem opponent_involution (p : Player) : opponent (opponent p) = p := by
  cases p <;> rfl

theorem ne_opponent (p : Player) : p ≠ opponent p := by
  cases p <;> decide

theorem totalStones_mod2_of_toMove {R : Board 5} {p : Player} (h : toMove R = p) :
    totalStones R % 2 = turnParity p := by
  unfold toMove at h
  by_cases he : totalStones R % 2 = 0
  · rw [if_pos he] at h; subst h; simp [turnParity, he]
  · rw [if_neg he] at h; subst h; simp [turnParity]; omega


theorem stone_eq_none_of_ge (l : List Player) (r : Nat) (h : l.length ≤ r) :
    stone l r = none := by
  induction l generalizing r with
  | nil => simp [stone]
  | cons a l ih =>
    cases r with
    | zero => simp at h
    | succ r => exact ih r (by simp at h; omega)

theorem cellAtInt_play_ne_gen {H : Nat} (R : Board 5) (c : Fin 5) (p : Player) (x y : Int)
    (hne : ¬ (x = (c.val : Int) ∧ y = ((R c).length : Int))) :
    cellAtInt H (play R c p) x y = cellAtInt H R x y := by
  unfold cellAtInt
  by_cases hx : 0 ≤ x ∧ x < (5 : Nat)
  · rw [dif_pos hx, dif_pos hx]
    by_cases hy : 0 ≤ y ∧ y < (H : Int)
    · rw [if_pos hy, if_pos hy]
      set d : Fin 5 := ⟨x.toNat, by omega⟩
      by_cases hdc : d = c
      · rw [hdc, play_eq, stone_append]
        by_cases hlt : y.toNat < (R c).length
        · rw [if_pos hlt]
        · rw [if_neg hlt]
          have hyne : y.toNat ≠ (R c).length := by
            intro heq; apply hne
            have hdv : (d.val : Int) = x := by dsimp [d]; omega
            rw [hdc] at hdv
            exact ⟨hdv.symm, by omega⟩
          have h1 : stone (R c) y.toNat = none :=
            stone_eq_none_of_ge (R c) y.toNat (by omega)
          rw [if_neg hyne, h1]
      · rw [play_ne _ _ _ _ hdc]
    · rw [if_neg hy, if_neg hy]
  · rw [dif_neg hx, dif_neg hx]

theorem hasFour_play_other_gen {H : Nat} {R : Board 5} {c : Fin 5} {p q : Player} (hne : p ≠ q)
    (hf : HasFour H (play R c p) q) : HasFour H R q := by
  have dir : ∀ {x y dx dy}, HasFourDir H (play R c p) q x y dx dy → HasFourDir H R q x y dx dy := by
    intro x y dx dy hd i
    have hi := hd i
    have hnot : ¬ (x + (i : Int) * dx = (c.val : Int) ∧ y + (i : Int) * dy = ((R c).length : Int)) := by
      intro ⟨hx, hy⟩
      rw [hx, hy] at hi
      obtain ⟨c2, hxc2, hy0, hyh, hs⟩ := cellAtInt_some hi
      have hc2 : c2 = c := Fin.ext (by omega)
      rw [hc2, play_eq, stone_append, if_neg (by omega)] at hs
      rw [if_pos (by omega)] at hs
      exact hne (Option.some.inj hs)
    rw [cellAtInt_play_ne_gen R c p _ _ hnot] at hi
    exact hi
  rcases hf with ⟨x, y, h⟩ | ⟨x, y, h⟩ | ⟨x, y, h⟩ | ⟨x, y, h⟩
  · exact Or.inl ⟨x, y, dir h⟩
  · exact Or.inr (Or.inl ⟨x, y, dir h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨x, y, dir h⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨x, y, dir h⟩))

theorem total_of_others_full_gen {H : Nat} {R : Board 5} {q : Fin 5}
    (h : ∀ e, e ≠ q → (R e).length = H) : totalStones R = (R q).length + 4 * H := by
  have htot : totalStones R = (R 0).length + (R 1).length + (R 2).length + (R 3).length + (R 4).length := by
    unfold totalStones; simp [Fin.sum_univ_five]
  rw [htot]
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 := by
    rcases q with ⟨v, hv⟩
    match v with
    | 0 => exact Or.inl (Fin.ext rfl)
    | 1 => exact Or.inr (Or.inl (Fin.ext rfl))
    | 2 => exact Or.inr (Or.inr (Or.inl (Fin.ext rfl)))
    | 3 => exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext rfl))))
    | 4 => exact Or.inr (Or.inr (Or.inr (Or.inr (Fin.ext rfl))))
    | _ + 5 => omega
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · rw [h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide)]; omega
  · rw [h 0 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide)]; omega
  · rw [h 0 (by decide), h 1 (by decide), h 3 (by decide), h 4 (by decide)]; omega
  · rw [h 0 (by decide), h 1 (by decide), h 2 (by decide), h 4 (by decide)]; omega
  · rw [h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide)]; omega

/-- Generic 2-ply invariant induction for `SafeP H me` (generalizing `Zone.safe_of_inv2`). -/
theorem safeP_of_inv2 {H : Nat} {me : Player} (Inv : Board 5 → Prop)
    (hInv : ∀ R, Inv R → toMove R = opponent me ∧ ¬ HasFour H R (opponent me))
    (hStep : ∀ R, Inv R → ∀ c : Fin 5, Legal H R c →
      ¬ HasFour H (play R c (opponent me)) (opponent me) ∧
        (BoardFull H (play R c (opponent me)) ∨
          ∃ e : Fin 5, Legal H (play R c (opponent me)) e ∧
            (HasFour H (play (play R c (opponent me)) e me) me ∨
              Inv (play (play R c (opponent me)) e me)))) :
    ∀ R, Inv R → SafeP H me R := by
  have key : ∀ k R, Inv R → SafeFor H me k R := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro R hR
      obtain ⟨htm, hno⟩ := hInv R hR
      cases k with
      | zero => exact hno
      | succ k1 =>
        refine ⟨hno, Or.inr (Or.inr ?_)⟩
        rw [if_neg (by rw [htm]; exact (ne_opponent me).symm)]
        intro c hc
        rw [htm]
        obtain ⟨hno1, hrest⟩ := hStep R hR c hc
        cases k1 with
        | zero => exact hno1
        | succ k2 =>
          refine ⟨hno1, ?_⟩
          have htm1 : toMove (play R c (opponent me)) = me := by
            unfold toMove at htm ⊢
            rw [totalStones_play]
            by_cases h0 : totalStones R % 2 = 0
            · rw [if_pos h0] at htm; rw [if_neg (by omega)]; cases me with | black => cases htm | white => rfl
            · rw [if_neg h0] at htm; rw [if_pos (by omega)]; cases me with | black => rfl | white => cases htm
          rcases hrest with hfull | ⟨e, he, hwin | hR2⟩
          · exact Or.inr (Or.inl hfull)
          · right; right
            rw [if_pos htm1]
            refine ⟨e, he, ?_⟩
            rw [htm1]
            cases k2 with
            | zero =>
              intro hf
              exact hno1 (hasFour_play_other_gen (ne_opponent me) hf)
            | succ k3 =>
              refine ⟨fun hf => hno1 (hasFour_play_other_gen (ne_opponent me) hf), Or.inl hwin⟩
          · right; right
            rw [if_pos htm1]
            refine ⟨e, he, ?_⟩
            rw [htm1]
            exact ih k2 (by omega) _ hR2
  exact fun R hR k => key k R hR

/-- Next playable cell of column `c` is empty or sits atop an attacker `opp` stone. -/
def PotExcP (opp : Player) (H : Nat) (R : Board 5) (c : Fin 5) (r : Nat) : Prop :=
  r = (R c).length ∧ (R c).length < H ∧
    ((R c).length = 0 ∨ stone (R c) ((R c).length - 1) = some opp)

/-- Multi-column claimed cells for a boolean column set `Q` with baseline heights `h0`. -/
def ClaimedSet (Q : Fin 5 → Bool) (h0 : Fin 5 → Nat) (x y : Int) : Prop :=
  ∃ q : Fin 5, Q q = true ∧ x = (q.val : Int) ∧ (h0 q : Int) < y ∧ (y - h0 q) % 2 = 1

/-- Non-vertical line `(x, y) + j * (1, dy)` is dead for attacker `opponent me`. -/
def LineOKSet (me : Player) (H : Nat) (R : Board 5) (Q : Fin 5 → Bool) (h0 : Fin 5 → Nat)
    (x y dy : Int) : Prop :=
  ∃ j : Fin 4,
    cellAtInt H R (x + (j : Int) * 1) (y + (j : Int) * dy) = some me ∨
    ClaimedSet Q h0 (x + (j : Int) * 1) (y + (j : Int) * dy) ∨
    ¬ (0 ≤ x + (j : Int) * 1 ∧ x + (j : Int) * 1 < 5 ∧
       0 ≤ y + (j : Int) * dy ∧ y + (j : Int) * dy < (H : Int))

/-- All non-vertical 4-lines through `(c, r)` are dead. -/
def LinesDeadSet (me : Player) (H : Nat) (R : Board 5) (Q : Fin 5 → Bool) (h0 : Fin 5 → Nat)
    (c : Fin 5) (r : Nat) : Prop :=
  ∀ dy ∈ ([0, 1, -1] : List Int), ∀ i : Fin 4,
    LineOKSet me H R Q h0 ((c.val : Int) - (i : Int) * 1) ((r : Int) - (i : Int) * dy) dy

/-- Column `c` has three consecutive attacker `opp` stones at its top. -/
def TopThreeP (opp : Player) (R : Board 5) (c : Fin 5) : Prop :=
  3 ≤ (R c).length ∧
    stone (R c) ((R c).length - 1) = some opp ∧
    stone (R c) ((R c).length - 2) = some opp ∧
    stone (R c) ((R c).length - 3) = some opp

theorem cell_play_mono_gen {H : Nat} {R : Board 5} {x y : Int} {p : Player}
    (hs : cellAtInt H R x y = some p) (c : Fin 5) (p' : Player) :
    cellAtInt H (play R c p') x y = some p := by
  obtain ⟨c2, hx, hy0, hyh, hst⟩ := cellAtInt_some hs
  rw [hx, cellAtInt_fin _ c2 _ hy0 hyh]
  by_cases hc : c2 = c
  · subst hc; rw [play_eq, stone_append, if_pos (stone_bound _ _ _ hst)]; exact hst
  · rw [play_ne _ _ _ _ hc]; exact hst

theorem linesDeadSet_play {me : Player} {H : Nat} {R : Board 5} {Q : Fin 5 → Bool} {h0 : Fin 5 → Nat}
    {c : Fin 5} {r : Nat} (h : LinesDeadSet me H R Q h0 c r) (e : Fin 5) (p : Player) :
    LinesDeadSet me H (play R e p) Q h0 c r := by
  intro dy hdy i
  obtain ⟨j, hj | hj | hj⟩ := h dy hdy i
  · exact ⟨j, Or.inl (cell_play_mono_gen hj e p)⟩
  · exact ⟨j, Or.inr (Or.inl hj)⟩
  · exact ⟨j, Or.inr (Or.inr hj)⟩

theorem no_opp_line_gen {me : Player} {H : Nat} {R R' : Board 5} {Q : Fin 5 → Bool} {h0 : Fin 5 → Nat}
    {x y dy : Int}
    (hok : LineOKSet me H R Q h0 x y dy)
    (hdef : ∀ x y, cellAtInt H R x y = some me → cellAtInt H R' x y = some me)
    (hcl : ∀ x y, ClaimedSet Q h0 x y → cellAtInt H R' x y ≠ some (opponent me)) :
    ¬ HasFourDir H R' (opponent me) x y 1 dy := by
  intro hf
  obtain ⟨j, hj | hj | hj⟩ := hok
  · have := hf j
    rw [hdef _ _ hj] at this
    exact ne_opponent me (Option.some.inj this)
  · exact hcl _ _ hj (hf j)
  · obtain ⟨c, hx, hy0, hyh, -⟩ := cellAtInt_some (hf j)
    have := c.isLt
    exact hj ⟨by omega, by omega, hy0, hyh⟩

/-- Unified multi-column claim invariant for defender `me`, claimed column set `Q`, baselines `h0`. -/
structure CInvGen (me : Player) (H : Nat) (Q : Fin 5 → Bool) (h0 : Fin 5 → Nat) (R : Board 5) : Prop where
  tm    : toMove R = opponent me
  nopp  : ¬ HasFour H R (opponent me)
  nme   : ¬ HasFour H R me
  valid : Valid H R
  ge    : ∀ q, Q q = true → h0 q ≤ (R q).length
  par   : ∀ q, Q q = true → (R q).length < H → (R q).length % 2 = h0 q % 2
  alt   : ∀ q, Q q = true → ∀ r, h0 q < r → r < (R q).length → (r - h0 q) % 2 = 1 →
            stone (R q) r = some me
  ntr   : ∀ c, (R c).length < H → ¬ TopThreeP (opponent me) R c
  dead  : ∀ c r, ExceptionalP (opponent me) R c r ∨ PotExcP (opponent me) H R c r →
            LinesDeadSet me H R Q h0 c r

theorem claimedSet_not_opp {me : Player} {H : Nat} {Q : Fin 5 → Bool} {h0 : Fin 5 → Nat}
    {R : Board 5} (inv : CInvGen me H Q h0 R) (c : Fin 5) (hl : Legal H R c)
    (x y : Int) (hc : ClaimedSet Q h0 x y) :
    cellAtInt H (play R c (opponent me)) x y ≠ some (opponent me) := by
  intro hs
  obtain ⟨q, hQq, hx, hygt, hypar⟩ := hc
  obtain ⟨c2, hx2, hy0, hyh, hst⟩ := cellAtInt_some hs
  have hcq : c2 = q := Fin.ext (by omega)
  subst c2
  have h1 : h0 q < y.toNat := by omega
  have h2 : (y.toNat - h0 q) % 2 = 1 := by omega
  by_cases hc2 : q = c
  · rw [hc2, play_eq, stone_append] at hst
    by_cases hlt : y.toNat < (R c).length
    · rw [if_pos hlt] at hst
      rw [← hc2] at hlt
      have := inv.alt q hQq _ h1 hlt h2
      rw [hc2] at this; rw [this] at hst
      exact ne_opponent me (Option.some.inj hst)
    · rw [if_neg hlt] at hst
      by_cases heq : y.toNat = (R c).length
      · have hge := inv.ge q hQq
        have hp := inv.par q hQq (by rw [hc2]; exact hl)
        rw [hc2] at hge hp h1 h2; omega
      · rw [if_neg heq] at hst; cases hst
  · rw [play_ne _ _ _ _ hc2] at hst
    have hlt := stone_bound _ _ _ hst
    have := inv.alt q hQq _ h1 hlt h2
    rw [this] at hst
    exact ne_opponent me (Option.some.inj hst)

theorem cinvGen_opp_no_four {me : Player} {H : Nat} {Q : Fin 5 → Bool} {h0 : Fin 5 → Nat}
    {R : Board 5} (inv : CInvGen me H Q h0 R) (c : Fin 5) (hl : Legal H R c) :
    ¬ HasFour H (play R c (opponent me)) (opponent me) := by
  intro hf
  have hnb1 : ¬ HasFour H (play R c (opponent me)) me :=
    fun hb => inv.nme (hasFour_play_other_gen (ne_opponent me).symm hb)
  rcases hf with ⟨x, y, hdir⟩ | ⟨x, y, hdir⟩ | ⟨x, y, hdir⟩ | ⟨x, y, hdir⟩
  · -- Vertical (0, 1): would require TopThreeP (opponent me) R c
    have hnew : ∃ i : Fin 4, x = (c.val : Int) ∧ y + (i : Int) * 1 = ((R c).length : Int) := by
      by_contra hcon
      apply inv.nopp
      left; refine ⟨x, y, fun i => ?_⟩
      have hi := hdir i
      rw [cellAtInt_play_ne_gen R c (opponent me) _ _ (fun ⟨h1, h2⟩ => hcon ⟨i, by omega, by omega⟩)] at hi
      exact hi
    obtain ⟨i, hx, hy⟩ := hnew
    have htop : ∀ j : Fin 4, y + (j : Int) * 1 ≤ ((R c).length : Int) := by
      intro j
      obtain ⟨cj, hxj, _, _, hsj⟩ := cellAtInt_some (hdir j)
      have hcj : cj = c := Fin.ext (by omega)
      subst cj
      have hb := stone_bound _ _ _ hsj
      rw [play_eq] at hb; simp at hb; omega
    have hi3 : i.val = 3 := by have := htop 3; omega
    apply inv.ntr c hl
    have hge3 : 3 ≤ (R c).length := by
      obtain ⟨_, _, hy0, _, _⟩ := cellAtInt_some (hdir 0); omega
    refine ⟨hge3, ?_, ?_, ?_⟩
    · have h2 := hdir 2
      rw [cellAtInt_play_ne_gen R c (opponent me) _ _ (by omega)] at h2
      obtain ⟨c2, hx2, _, _, hs2⟩ := cellAtInt_some h2
      have hc2 : c2 = c := Fin.ext (by omega); subst c2
      have e : (y + ((2 : Fin 4) : Int) * (1 : Int)).toNat = (R c).length - 1 := by omega
      rwa [e] at hs2
    · have h1 := hdir 1
      rw [cellAtInt_play_ne_gen R c (opponent me) _ _ (by omega)] at h1
      obtain ⟨c1, hx1, _, _, hs1⟩ := cellAtInt_some h1
      have hc1 : c1 = c := Fin.ext (by omega); subst c1
      have e : (y + ((1 : Fin 4) : Int) * (1 : Int)).toNat = (R c).length - 2 := by omega
      rwa [e] at hs1
    · have h0' := hdir 0
      rw [cellAtInt_play_ne_gen R c (opponent me) _ _ (by omega)] at h0'
      obtain ⟨c0, hx0, _, _, hs0⟩ := cellAtInt_some h0'
      have hc0 : c0 = c := Fin.ext (by omega); subst c0
      have e : (y + ((0 : Fin 4) : Int) * (1 : Int)).toNat = (R c).length - 3 := by omega
      rwa [e] at hs0
  · -- Horizontal (1, 0)
    have hdir' : (1 : Int) = 0 ∧ (0 : Int) = 1 ∨ (1 : Int) = 1 ∧ (0 : Int) = 0 ∨
        (1 : Int) = 1 ∧ (0 : Int) = 1 ∨ (1 : Int) = 1 ∧ (0 : Int) = -1 := Or.inr (Or.inl ⟨rfl, rfl⟩)
    obtain ⟨i, ce, hxe, he⟩ := exists_exceptional_in_line_gen hdir' (by rw [opponent_involution]; exact hnb1) hdir
    have hcell : ExceptionalP (opponent me) R ce (y + (i : Int) * 0).toNat ∨
        PotExcP (opponent me) H R ce (y + (i : Int) * 0).toNat := by
      obtain ⟨hs, hbot⟩ := he
      by_cases hnew : ce = c ∧ (y + (i : Int) * 0).toNat = (R c).length
      · right
        obtain ⟨hce, hr⟩ := hnew; subst ce
        refine ⟨hr, hl, ?_⟩
        by_cases hrz : (R c).length = 0
        · exact Or.inl hrz
        · rcases hbot with hz | hprev
          · exact Or.inl (by omega)
          · right; rw [hr] at hprev; rw [play_eq, stone_append, if_pos (by omega)] at hprev; exact hprev
      · left
        have hlt : (y + (i : Int) * 0).toNat < (R ce).length := by
          by_cases hce : ce = c
          · subst hce; have hb := stone_bound _ _ _ hs; rw [play_eq] at hb; simp at hb; omega
          · rw [play_ne _ _ _ _ hce] at hs; exact stone_bound _ _ _ hs
        refine ⟨?_, ?_⟩
        · by_cases hce : ce = c
          · subst hce; rw [play_eq, stone_append, if_pos hlt] at hs; exact hs
          · rw [play_ne _ _ _ _ hce] at hs; exact hs
        · rcases hbot with hz | hprev
          · exact Or.inl hz
          · right
            by_cases hce : ce = c
            · subst hce; rw [play_eq, stone_append, if_pos (by omega)] at hprev; exact hprev
            · rw [play_ne _ _ _ _ hce] at hprev; exact hprev
    have hok := inv.dead ce _ hcell 0 (by simp) i
    have hx0 : (ce.val : Int) - (i : Int) * 1 = x := by omega
    have hy0 : ((y + (i : Int) * 0).toNat : Int) - (i : Int) * 0 = y := by
      obtain ⟨_, _, hyge, _, _⟩ := cellAtInt_some (hdir i); omega
    rw [hx0, hy0] at hok
    exact no_opp_line_gen hok (fun _ _ hs => cell_play_mono_gen hs c (opponent me))
      (claimedSet_not_opp inv c hl) hdir
  · -- Rising diagonal (1, 1)
    have hdir' : (1 : Int) = 0 ∧ (1 : Int) = 1 ∨ (1 : Int) = 1 ∧ (1 : Int) = 0 ∨
        (1 : Int) = 1 ∧ (1 : Int) = 1 ∨ (1 : Int) = 1 ∧ (1 : Int) = -1 := Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
    obtain ⟨i, ce, hxe, he⟩ := exists_exceptional_in_line_gen hdir' (by rw [opponent_involution]; exact hnb1) hdir
    have hcell : ExceptionalP (opponent me) R ce (y + (i : Int) * 1).toNat ∨
        PotExcP (opponent me) H R ce (y + (i : Int) * 1).toNat := by
      obtain ⟨hs, hbot⟩ := he
      by_cases hnew : ce = c ∧ (y + (i : Int) * 1).toNat = (R c).length
      · right; obtain ⟨hce, hr⟩ := hnew; subst ce; refine ⟨hr, hl, ?_⟩
        by_cases hrz : (R c).length = 0
        · exact Or.inl hrz
        · rcases hbot with hz | hprev
          · exact Or.inl (by omega)
          · right; rw [hr] at hprev; rw [play_eq, stone_append, if_pos (by omega)] at hprev; exact hprev
      · left
        have hlt : (y + (i : Int) * 1).toNat < (R ce).length := by
          by_cases hce : ce = c
          · subst hce; have hb := stone_bound _ _ _ hs; rw [play_eq] at hb; simp at hb; omega
          · rw [play_ne _ _ _ _ hce] at hs; exact stone_bound _ _ _ hs
        refine ⟨?_, ?_⟩
        · by_cases hce : ce = c
          · subst hce; rw [play_eq, stone_append, if_pos hlt] at hs; exact hs
          · rw [play_ne _ _ _ _ hce] at hs; exact hs
        · rcases hbot with hz | hprev
          · exact Or.inl hz
          · right
            by_cases hce : ce = c
            · subst hce; rw [play_eq, stone_append, if_pos (by omega)] at hprev; exact hprev
            · rw [play_ne _ _ _ _ hce] at hprev; exact hprev
    have hok := inv.dead ce _ hcell 1 (by simp) i
    have hx0 : (ce.val : Int) - (i : Int) * 1 = x := by omega
    have hy0 : ((y + (i : Int) * 1).toNat : Int) - (i : Int) * 1 = y := by
      obtain ⟨_, _, hyge, _, _⟩ := cellAtInt_some (hdir i); omega
    rw [hx0, hy0] at hok
    exact no_opp_line_gen hok (fun _ _ hs => cell_play_mono_gen hs c (opponent me))
      (claimedSet_not_opp inv c hl) hdir
  · -- Falling diagonal (1, -1)
    have hdir' : (1 : Int) = 0 ∧ (-1 : Int) = 1 ∨ (1 : Int) = 1 ∧ (-1 : Int) = 0 ∨
        (1 : Int) = 1 ∧ (-1 : Int) = 1 ∨ (1 : Int) = 1 ∧ (-1 : Int) = -1 := Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
    obtain ⟨i, ce, hxe, he⟩ := exists_exceptional_in_line_gen hdir' (by rw [opponent_involution]; exact hnb1) hdir
    have hcell : ExceptionalP (opponent me) R ce (y + (i : Int) * (-1)).toNat ∨
        PotExcP (opponent me) H R ce (y + (i : Int) * (-1)).toNat := by
      obtain ⟨hs, hbot⟩ := he
      by_cases hnew : ce = c ∧ (y + (i : Int) * (-1)).toNat = (R c).length
      · right; obtain ⟨hce, hr⟩ := hnew; subst ce; refine ⟨hr, hl, ?_⟩
        by_cases hrz : (R c).length = 0
        · exact Or.inl hrz
        · rcases hbot with hz | hprev
          · exact Or.inl (by omega)
          · right; rw [hr] at hprev; rw [play_eq, stone_append, if_pos (by omega)] at hprev; exact hprev
      · left
        have hlt : (y + (i : Int) * (-1)).toNat < (R ce).length := by
          by_cases hce : ce = c
          · subst hce; have hb := stone_bound _ _ _ hs; rw [play_eq] at hb; simp at hb; omega
          · rw [play_ne _ _ _ _ hce] at hs; exact stone_bound _ _ _ hs
        refine ⟨?_, ?_⟩
        · by_cases hce : ce = c
          · subst hce; rw [play_eq, stone_append, if_pos hlt] at hs; exact hs
          · rw [play_ne _ _ _ _ hce] at hs; exact hs
        · rcases hbot with hz | hprev
          · exact Or.inl hz
          · right
            by_cases hce : ce = c
            · subst hce; rw [play_eq, stone_append, if_pos (by omega)] at hprev; exact hprev
            · rw [play_ne _ _ _ _ hce] at hprev; exact hprev
    have hok := inv.dead ce _ hcell (-1) (by simp) i
    have hx0 : (ce.val : Int) - (i : Int) * 1 = x := by omega
    have hy0 : ((y + (i : Int) * (-1)).toNat : Int) - (i : Int) * (-1) = y := by
      obtain ⟨_, _, hyge, _, _⟩ := cellAtInt_some (hdir i); omega
    rw [hx0, hy0] at hok
    exact no_opp_line_gen hok (fun _ _ hs => cell_play_mono_gen hs c (opponent me))
      (claimedSet_not_opp inv c hl) hdir

theorem cinvGen_step {me : Player} {H : Nat} {Q : Fin 5 → Bool} {h0 : Fin 5 → Nat}
    {R : Board 5} (inv : CInvGen me H Q h0 R) (c : Fin 5) (hl : Legal H R c)
    (e : Fin 5) (he : Legal H (play R c (opponent me)) e)
    (hcase : e = c ∨ ((R c).length + 1 = H ∧ Q e = false))
    (hnb2 : ¬ HasFour H (play (play R c (opponent me)) e me) me) :
    CInvGen me H Q h0 (play (play R c (opponent me)) e me) := by
  set R1 := play R c (opponent me)
  set R2 := play R1 e me
  have hnw1 := cinvGen_opp_no_four inv c hl
  have hnw2 : ¬ HasFour H R2 (opponent me) :=
    fun hf => hnw1 (hasFour_play_other_gen (ne_opponent me) hf)
  have htm2 : toMove R2 = opponent me := by
    unfold toMove at *
    have ht : totalStones R2 = totalStones R + 2 := by
      simp only [R2, R1, totalStones_play]
    rw [ht]
    have hm : (totalStones R + 2) % 2 = totalStones R % 2 := by omega
    rw [hm]; exact inv.tm
  have hv2 : Valid H R2 := play_valid (play_valid inv.valid hl) he
  refine ⟨htm2, hnw2, hnb2, hv2, ?_, ?_, ?_, ?_, ?_⟩
  · -- ge
    intro q hQq
    have := inv.ge q hQq
    have h1 : (R q).length ≤ (R1 q).length := by
      by_cases hqc : q = c
      · subst hqc; simp [R1, play_eq]
      · simp [R1, play_ne _ _ _ _ hqc]
    have h2 : (R1 q).length ≤ (R2 q).length := by
      by_cases hqe : q = e
      · subst hqe; simp [R2, play_eq]
      · simp [R2, play_ne _ _ _ _ hqe]
    omega
  · -- par
    intro q hQq hlt
    rcases hcase with hce | ⟨hcap, hQe⟩
    · by_cases hqc : q = c
      · have hlen : (R2 q).length = (R q).length + 2 := by
          simp only [R2, R1, hce, hqc, play_eq, List.length_append]; simp
        have hp := inv.par q hQq (by rw [hqc]; exact hl)
        omega
      · have hlen : (R2 q).length = (R q).length := by
          simp only [R2, R1, hce, play_ne _ _ _ _ hqc]
        rw [hlen] at hlt ⊢
        exact inv.par q hQq hlt
    · have hqe : q ≠ e := fun h => by rw [h, hQe] at hQq; cases hQq
      by_cases hqc : q = c
      · have hce : c ≠ e := by rw [← hqc]; exact hqe
        have hlen : (R2 q).length = (R q).length + 1 := by
          rw [hqc]; simp only [R2, R1, play_ne _ _ _ _ hce, play_eq, List.length_append]; simp
        rw [hqc] at hlt hlen; omega
      · have hlen : (R2 q).length = (R q).length := by
          simp only [R2, R1, play_ne _ _ _ _ hqe, play_ne _ _ _ _ hqc]
        rw [hlen] at hlt ⊢
        exact inv.par q hQq hlt
  · -- alt
    intro q hQq r hgt hlt hodd
    rcases hcase with hce | ⟨hcap, hQe⟩
    · by_cases hqc : q = c
      · have hlen : (R2 q).length = (R q).length + 2 := by
          simp only [R2, R1, hce, hqc, play_eq, List.length_append]; simp
        by_cases hr : r < (R q).length
        · simp only [R2, R1, hce, hqc, play_eq]
          rw [stone_append, if_pos (by simp; rw [← hqc]; omega), stone_append, if_pos (by rw [← hqc]; exact hr)]
          rw [← hqc]; exact inv.alt q hQq r hgt hr hodd
        · have hp := inv.par q hQq (by rw [hqc]; exact hl)
          have hreq : r = (R q).length + 1 := by omega
          simp only [R2, R1, hce, hqc, play_eq]
          rw [stone_append, if_neg (by simp; rw [← hqc]; omega), if_pos (by simp; rw [← hqc]; omega)]
      · simp only [R2, R1, hce, play_ne _ _ _ _ hqc] at hlt ⊢
        exact inv.alt q hQq r hgt hlt hodd
    · have hqe : q ≠ e := fun h => by rw [h, hQe] at hQq; cases hQq
      by_cases hqc : q = c
      · have hce : c ≠ e := by rw [← hqc]; exact hqe
        have hlen : (R2 q).length = (R q).length + 1 := by
          rw [hqc]; simp only [R2, R1, play_ne _ _ _ _ hce, play_eq, List.length_append]; simp
        have hp := inv.par q hQq (by rw [hqc]; exact hl)
        have hr : r < (R q).length := by omega
        rw [hqc]; simp only [R2, R1, play_ne _ _ _ _ hce, play_eq]
        rw [stone_append, if_pos (by rw [← hqc]; exact hr)]
        rw [← hqc]; exact inv.alt q hQq r hgt hr hodd
      · simp only [R2, R1, play_ne _ _ _ _ hqe, play_ne _ _ _ _ hqc] at hlt ⊢
        exact inv.alt q hQq r hgt hlt hodd
  · -- ntr: defender's stone at e kills TopThree on e; c either equals e or is full
    intro d hlt ht
    by_cases hde : d = e
    · subst hde
      obtain ⟨h3, t1, -, -⟩ := ht
      simp only [R2, play_eq] at t1
      rw [stone_append, if_neg (by simp), if_pos (by simp)] at t1
      exact ne_opponent me (Option.some.inj t1)
    · have hdc : d ≠ c := by
        intro h; subst h
        rcases hcase with rfl | ⟨hcap, -⟩
        · exact hde rfl
        · simp only [R2, R1, play_ne _ _ _ _ hde, play_eq] at hlt; simp at hlt; omega
      have eqd : R2 d = R d := by simp [R2, R1, play_ne _ _ _ _ hde, play_ne _ _ _ _ hdc]
      unfold TopThreeP at ht
      rw [eqd] at hlt ht
      exact inv.ntr d hlt ht
  · -- dead: every Exceptional or PotExc in R2 was already Exceptional or PotExc in R
    intro d r hcell
    apply linesDeadSet_play (linesDeadSet_play _ c (opponent me)) e me
    apply inv.dead d r
    rcases hcell with ⟨hs, hbot⟩ | ⟨hr, hlt, htop⟩
    · by_cases hde : d = e
      · subst hde
        have hlt1 : r < (R1 d).length := by
          simp only [R2, play_eq] at hs
          rw [stone_append] at hs
          by_cases h : r < (R1 d).length
          · exact h
          · rw [if_neg h] at hs
            by_cases heq : r = (R1 d).length
            · rw [if_pos heq] at hs; exact absurd (Option.some.inj hs) (ne_opponent me)
            · rw [if_neg heq] at hs; cases hs
        simp only [R2, play_eq] at hs hbot
        rw [stone_append, if_pos hlt1] at hs
        have hbot1 : r = 0 ∨ stone (R1 d) (r - 1) = some (opponent me) := by
          rcases hbot with hz | hp
          · exact Or.inl hz
          · right; rw [stone_append, if_pos (by omega)] at hp; exact hp
        by_cases hdc : d = c
        · subst hdc
          by_cases hr0 : r = (R d).length
          · right; refine ⟨hr0, hl, ?_⟩
            by_cases hrz : (R d).length = 0
            · exact Or.inl hrz
            · rcases hbot1 with hz | hp
              · exact Or.inl (by omega)
              · right; rw [hr0] at hp; simp only [R1, play_eq] at hp; rw [stone_append, if_pos (by omega)] at hp; exact hp
          · left
            have hrlt : r < (R d).length := by simp [R1, play_eq] at hlt1; omega
            simp only [R1, play_eq] at hs hbot1
            rw [stone_append, if_pos hrlt] at hs
            refine ⟨hs, ?_⟩
            rcases hbot1 with hz | hp
            · exact Or.inl hz
            · right; rw [stone_append, if_pos (by omega)] at hp; exact hp
        · left
          simp only [R1, play_ne _ _ _ _ hdc] at hs hbot1
          exact ⟨hs, hbot1⟩
      · simp only [R2, play_ne _ _ _ _ hde] at hs hbot
        by_cases hdc : d = c
        · subst hdc
          by_cases hr0 : r = (R d).length
          · right; refine ⟨hr0, hl, ?_⟩
            by_cases hrz : (R d).length = 0
            · exact Or.inl hrz
            · rcases hbot with hz | hp
              · exact Or.inl (by omega)
              · right; rw [hr0] at hp; simp only [R1, play_eq] at hp; rw [stone_append, if_pos (by omega)] at hp; exact hp
          · left
            have hrlt : r < (R d).length := by
              have hb := stone_bound _ _ _ hs; simp [R1, play_eq] at hb; omega
            simp only [R1, play_eq] at hs hbot
            rw [stone_append, if_pos hrlt] at hs
            refine ⟨hs, ?_⟩
            rcases hbot with hz | hp
            · exact Or.inl hz
            · right; rw [stone_append, if_pos (by omega)] at hp; exact hp
        · left
          simp only [R1, play_ne _ _ _ _ hdc] at hs hbot
          exact ⟨hs, hbot⟩
    · -- PotExcP in R2: cannot be at e (top is me) or at c (either c=e or c is full)
      have hde : d ≠ e := by
        intro h; subst h
        rcases htop with hz | hst
        · simp [R2, play_eq] at hz
        · simp only [R2, play_eq] at hst
          rw [stone_append, if_neg (by simp), if_pos (by simp)] at hst
          exact ne_opponent me (Option.some.inj hst)
      have hdc : d ≠ c := by
        intro h; subst h
        rcases hcase with rfl | ⟨hcap, -⟩
        · exact hde rfl
        · simp only [R2, R1, play_ne _ _ _ _ hde, play_eq] at hlt; simp at hlt; omega
      have eqd : R2 d = R d := by simp [R2, R1, play_ne _ _ _ _ hde, play_ne _ _ _ _ hdc]
      rw [eqd] at hr hlt htop
      exact Or.inr ⟨hr, hlt, htop⟩

/-! ## Regime 1: Odd-Empty Single-Column Claim (`ClaimOddHyp`, Even-H Black / Odd-H White) -/

structure ClaimOddHyp (me : Player) (h : Nat) (A : Board 5) (q : Fin 5) : Prop where
  regime : emptyParity h (opponent me) = 1
  valid  : Valid h A
  odd    : (h - (A q).length) % 2 = 1
  ntr    : ∀ c, (A c).length < h → ¬ TopThreeP (opponent me) A c
  dead   : ∀ c r, ExceptionalP (opponent me) A c r ∨ PotExcP (opponent me) h A c r →
             LinesDeadSet me h A (fun d => decide (d = q)) (fun d => (A d).length) c r

theorem claim_odd_safe {me : Player} {H : Nat} {R : Board 5} {q : Fin 5}
    (hy : ClaimOddHyp me H R q)
    (htm : toMove R = opponent me) (hnopp : ¬ HasFour H R (opponent me)) (hnme : ¬ HasFour H R me) :
    SafeP H me R := by
  let Q : Fin 5 → Bool := fun d => decide (d = q)
  let h0 : Fin 5 → Nat := fun d => (R d).length
  have root : CInvGen me H Q h0 R :=
    ⟨htm, hnopp, hnme, hy.valid, fun _ _ => le_refl _, fun _ _ _ => rfl,
     fun _ _ _ h1 h2 _ => by dsimp only [h0] at h1 h2; omega, hy.ntr, hy.dead⟩
  refine safeP_of_inv2 (CInvGen me H Q h0) (fun R inv => ⟨inv.tm, inv.nopp⟩) ?_ R root
  intro R inv c hl
  refine ⟨cinvGen_opp_no_four inv c hl, ?_⟩
  by_cases hfull : BoardFull H (play R c (opponent me))
  · exact Or.inl hfull
  right
  have fin : ∀ e, Legal H (play R c (opponent me)) e →
      (e = c ∨ ((R c).length + 1 = H ∧ Q e = false)) →
      Legal H (play R c (opponent me)) e ∧
        (HasFour H (play (play R c (opponent me)) e me) me ∨
          CInvGen me H Q h0 (play (play R c (opponent me)) e me)) := by
    intro e he hcase
    refine ⟨he, ?_⟩
    by_cases hwin : HasFour H (play (play R c (opponent me)) e me) me
    · exact Or.inl hwin
    · exact Or.inr (cinvGen_step inv c hl e he hcase hwin)
  by_cases hcap : (R c).length + 1 < H
  · exact ⟨c, fin c (by unfold Legal; simpa [play_eq] using hcap) (Or.inl rfl)⟩
  · have hl' : (R c).length < H := hl
    have hcapeq : (R c).length + 1 = H := by omega
    have hex : ∃ e, Q e = false ∧ (play R c (opponent me) e).length ≠ H := by
      by_contra hcon
      have hall : ∀ e, e ≠ q → (play R c (opponent me) e).length = H := by
        intro e heq; by_contra hne
        exact hcon ⟨e, by simp [Q, heq], hne⟩
      by_cases hqfull : (play R c (opponent me) q).length = H
      · apply hfull; intro e
        by_cases heq : e = q
        · subst heq; exact hqfull
        · exact hall e heq
      · have ht := total_of_others_full_gen hall
        rw [totalStones_play] at ht
        have htm2 := totalStones_mod2_of_toMove inv.tm
        have hqc : q ≠ c := by rintro rfl; apply hqfull; simp [play_eq, List.length_append]; omega
        rw [play_ne _ _ _ _ hqc] at ht hqfull
        have hvq := inv.valid q
        have hpar := inv.par q (by simp [Q]) (by omega)
        have hreg := hy.regime
        unfold emptyParity at hreg
        have hodd := hy.odd
        have h0q : h0 q ≤ H := hy.valid q
        dsimp only [h0] at hpar h0q
        omega
    obtain ⟨e, hQe, hne⟩ := hex
    have hle : (play R c (opponent me) e).length ≤ H := play_valid inv.valid hl e
    exact ⟨e, fin e (by unfold Legal; omega) (Or.inr ⟨hcapeq, hQe⟩)⟩

/-! ## Regime 2: Even-Empty Multi-Column Claim (`ClaimEvenHyp`, Odd-H Black / Even-H White) -/

/-- Canonical maximal even-remaining column set for `ClaimEvenHyp`. -/
def evenCols (h : Nat) (A : Board 5) : Fin 5 → Bool :=
  fun d => decide ((A d).length < h ∧ (h - (A d).length) % 2 = 0)

structure ClaimEvenHyp (me : Player) (h : Nat) (A : Board 5) : Prop where
  regime : emptyParity h (opponent me) = 0
  valid  : Valid h A
  ntr    : ∀ c, (A c).length < h → ¬ TopThreeP (opponent me) A c
  dead   : ∀ c r, ExceptionalP (opponent me) A c r ∨ PotExcP (opponent me) h A c r →
             LinesDeadSet me h A (evenCols h A) (fun d => (A d).length) c r

theorem sum_even_of_all_even {H : Nat} {R : Board 5} {Q : Fin 5 → Bool}
    (hall : ∀ e, Q e = false → (R e).length = H)
    (heven : ∀ q, Q q = true → (H - (R q).length) % 2 = 0)
    (hv : Valid H R) :
    (5 * H - totalStones R) % 2 = 0 := by
  have hbound : ∀ c : Fin 5, (R c).length ≤ H := hv
  have hcol : ∀ c : Fin 5, (H - (R c).length) % 2 = 0 := by
    intro c
    cases hQc : Q c with
    | false => have := hall c hQc; omega
    | true => exact heven c hQc
  have h0 := hcol 0; have h1 := hcol 1; have h2 := hcol 2; have h3 := hcol 3; have h4 := hcol 4
  have b0 := hbound 0; have b1 := hbound 1; have b2 := hbound 2; have b3 := hbound 3; have b4 := hbound 4
  have htot : totalStones R = (R 0).length + (R 1).length + (R 2).length + (R 3).length + (R 4).length := by
    unfold totalStones
    simp [Fin.sum_univ_five]
  omega

theorem claim_even_safe {me : Player} {H : Nat} {R : Board 5}
    (hy : ClaimEvenHyp me H R)
    (htm : toMove R = opponent me) (hnopp : ¬ HasFour H R (opponent me)) (hnme : ¬ HasFour H R me) :
    SafeP H me R := by
  let Q : Fin 5 → Bool := evenCols H R
  let h0 : Fin 5 → Nat := fun d => (R d).length
  have hQeven : ∀ q, Q q = true → (H - h0 q) % 2 = 0 := by
    intro q hQq
    simp only [Q, evenCols, decide_eq_true_eq] at hQq
    exact hQq.2
  have root : CInvGen me H Q h0 R :=
    ⟨htm, hnopp, hnme, hy.valid, fun _ _ => le_refl _, fun _ _ _ => rfl,
     fun _ _ _ h1 h2 _ => by dsimp only [h0] at h1 h2; omega, hy.ntr, hy.dead⟩
  refine safeP_of_inv2 (CInvGen me H Q h0) (fun R inv => ⟨inv.tm, inv.nopp⟩) ?_ R root
  intro R inv c hl
  refine ⟨cinvGen_opp_no_four inv c hl, ?_⟩
  by_cases hfull : BoardFull H (play R c (opponent me))
  · exact Or.inl hfull
  right
  have fin : ∀ e, Legal H (play R c (opponent me)) e →
      (e = c ∨ ((R c).length + 1 = H ∧ Q e = false)) →
      Legal H (play R c (opponent me)) e ∧
        (HasFour H (play (play R c (opponent me)) e me) me ∨
          CInvGen me H Q h0 (play (play R c (opponent me)) e me)) := by
    intro e he hcase
    refine ⟨he, ?_⟩
    by_cases hwin : HasFour H (play (play R c (opponent me)) e me) me
    · exact Or.inl hwin
    · exact Or.inr (cinvGen_step inv c hl e he hcase hwin)
  by_cases hcap : (R c).length + 1 < H
  · exact ⟨c, fin c (by unfold Legal; simpa [play_eq] using hcap) (Or.inl rfl)⟩
  · have hl' : (R c).length < H := hl
    have hcapeq : (R c).length + 1 = H := by omega
    -- Column c cannot be in Q (every column in Q has even remaining capacity, hence cannot be capped!)
    have hQc_false : Q c = false := by
      cases hQc : Q c with
      | false => rfl
      | true =>
        have hp := inv.par c hQc hl
        have hev := hQeven c hQc
        have hvc := inv.valid c
        have h0c : h0 c ≤ H := hy.valid c
        omega
    -- Some column e with Q e = false must still be non-full in `play R c (opponent me)`
    have hex : ∃ e, Q e = false ∧ (play R c (opponent me) e).length ≠ H := by
      by_contra hcon
      have hall : ∀ e, Q e = false → (play R c (opponent me) e).length = H := by
        intro e hQe; by_contra hne; exact hcon ⟨e, hQe, hne⟩
      have hev1 : ∀ q, Q q = true → (H - (play R c (opponent me) q).length) % 2 = 0 := by
        intro q hQq
        have hqc : q ≠ c := fun h => by subst h; simp [hQq] at hQc_false
        rw [play_ne _ _ _ _ hqc]
        by_cases hqf : (R q).length = H
        · omega
        · have hvq := inv.valid q
          have hp := inv.par q hQq (by omega)
          have hev := hQeven q hQq
          have h0q : h0 q ≤ H := hy.valid q
          omega
      have hv1 : Valid H (play R c (opponent me)) := play_valid inv.valid hl
      have hsum := sum_even_of_all_even hall hev1 hv1
      rw [totalStones_play] at hsum
      have htm2 := totalStones_mod2_of_toMove inv.tm
      have hreg := hy.regime
      unfold emptyParity at hreg
      have hle5 : totalStones R + 1 ≤ 5 * H := by
        have b0 := hv1 0; have b1 := hv1 1; have b2 := hv1 2; have b3 := hv1 3; have b4 := hv1 4
        have htot : totalStones (play R c (opponent me)) =
            (play R c (opponent me) 0).length + (play R c (opponent me) 1).length +
            (play R c (opponent me) 2).length + (play R c (opponent me) 3).length +
            (play R c (opponent me) 4).length := by
          unfold totalStones; simp [Fin.sum_univ_five]
        rw [totalStones_play] at htot; omega
      omega
    obtain ⟨e, hQe, hne⟩ := hex
    have hle : (play R c (opponent me) e).length ≤ H := play_valid inv.valid hl e
    exact ⟨e, fin e (by unfold Legal; omega) (Or.inr ⟨hcapeq, hQe⟩)⟩

#print axioms claim_odd_safe
#print axioms claim_even_safe

end C4W5Gen
