import C4W5.Theory.ClaimGen

/-!
# Parity-Unified Color-Polymorphic One-Sided Zone Theorem (`ZoneGen`)

Generalizes `C4W5/Theory/Zone.lean` and `C4W5/Theory/ZoneL.lean` in three ways:
1. **Color-polymorphic**: parameterized over defender `me : Player` (attacker `opp := opponent me`).
2. **Parity-unified**: replaces `(hK : K % 2 = 0) (hH : H % 2 = 0)` with the single
   same-parity hypothesis `(hpar : K % 2 = H % 2)`, covering BOTH even heights (`5 × 2m`)
   and odd heights (`5 × (2m+1)`) uniformly.
3. **Pluggable leaf predicates**: abstracts `ZoneLeafSound me Leaf` so BOTH `ClaimOddHyp`
   (Odd-H White, Even-H Black) and `ClaimEvenHyp` (Odd-H Black) plug straight into `zone_safeL_gen`.

Zero `sorry`, zero custom axioms.
-/

namespace C4W5Gen
open Connect4 (Player opponent)
open Connect4.NarrowBoards
open C4W5

set_option linter.deprecated false

/-- Bottom `K` rows of `R`. -/
def truncG (K : Nat) (R : Board 5) : Board 5 := fun c => (R c).take K

theorem truncG_length (K : Nat) (R : Board 5) (c : Fin 5) :
    (truncG K R c).length = min K (R c).length := by
  simp [truncG]

theorem cell_truncG {K H : Nat} (hKH : K ≤ H) (R : Board 5) (x y : Int) (hy : y < (K : Int)) :
    cellAtInt K (truncG K R) x y = cellAtInt H R x y := by
  unfold cellAtInt
  by_cases hx : 0 ≤ x ∧ x < (5 : Nat)
  · rw [dif_pos hx, dif_pos hx]
    by_cases hy0 : 0 ≤ y
    · have hK : 0 ≤ y ∧ y < (K : Int) := ⟨hy0, hy⟩
      have hH : 0 ≤ y ∧ y < (H : Int) := ⟨hy0, by omega⟩
      rw [if_pos hK, if_pos hH]
      dsimp only [truncG]; exact stone_take _ K _ (by omega)
    · have hK : ¬ (0 ≤ y ∧ y < (K : Int)) := by omega
      have hH : ¬ (0 ≤ y ∧ y < (H : Int)) := by omega
      rw [if_neg hK, if_neg hH]
  · rw [dif_neg hx, dif_neg hx]

theorem hasFour_of_truncG {K H : Nat} (hKH : K ≤ H) {R : Board 5} {p : Player}
    (hf : HasFour K (truncG K R) p) : HasFour H R p := by
  have dir : ∀ {x y dx dy}, HasFourDir K (truncG K R) p x y dx dy → HasFourDir H R p x y dx dy := by
    intro x y dx dy hd i
    have hi := hd i
    obtain ⟨_, _, _, hyK, _⟩ := cellAtInt_some hi
    rw [← cell_truncG hKH R _ _ hyK]; exact hi
  rcases hf with ⟨x, y, h⟩ | ⟨x, y, h⟩ | ⟨x, y, h⟩ | ⟨x, y, h⟩
  · exact Or.inl ⟨x, y, dir h⟩
  · exact Or.inr (Or.inl ⟨x, y, dir h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨x, y, dir h⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨x, y, dir h⟩))

theorem truncG_play_low {K : Nat} {R : Board 5} {c : Fin 5} (p : Player) (hl : (R c).length < K) :
    truncG K (play R c p) = play (truncG K R) c p := by
  funext d
  by_cases hd : d = c
  · subst hd
    simp only [truncG, play_eq]
    rw [List.take_of_length_le (by simp; omega), List.take_of_length_le (by omega)]
  · simp only [truncG, play_ne _ _ _ _ hd]

theorem truncG_play_high {K : Nat} {R : Board 5} {c : Fin 5} (p : Player) (hl : K ≤ (R c).length) :
    truncG K (play R c p) = truncG K R := by
  funext d
  by_cases hd : d = c
  · subst hd
    simp only [truncG, play_eq, List.take_append_of_le_length hl]
  · simp only [truncG, play_ne _ _ _ _ hd]

/-- Discipline: every exceptional attacker stone sits at 0-based row `≤ K - 4`. -/
def DiscEP (opp : Player) (K : Nat) (R : Board 5) : Prop :=
  ∀ c r, ExceptionalP opp R c r → r + 4 ≤ K

/-- Discipline: every non-full column that is empty or has an attacker top sits at height `≤ K - 4`. -/
def TColP (opp : Player) (K H : Nat) (R : Board 5) (c : Fin 5) : Prop :=
  (R c).length < H →
    ((R c).length = 0 ∨ stone (R c) ((R c).length - 1) = some opp) →
    (R c).length + 4 ≤ K

theorem discEP_play_me {me : Player} {K : Nat} {R : Board 5} (hE : DiscEP (opponent me) K R) (e : Fin 5) :
    DiscEP (opponent me) K (play R e me) := by
  intro c r ⟨hs, hbot⟩
  by_cases hc : c = e
  · subst hc
    rw [play_eq, stone_append] at hs
    by_cases hlt : r < (R c).length
    · rw [if_pos hlt] at hs
      apply hE c r; refine ⟨hs, ?_⟩
      rcases hbot with hz | hp
      · exact Or.inl hz
      · right; rw [play_eq, stone_append, if_pos (by omega)] at hp; exact hp
    · rw [if_neg hlt] at hs
      by_cases heq : r = (R c).length
      · rw [if_pos heq] at hs; exact absurd (Option.some.inj hs) (ne_opponent me)
      · rw [if_neg heq] at hs; cases hs
  · rw [play_ne _ _ _ _ hc] at hs hbot
    exact hE c r ⟨hs, hbot⟩

theorem discEP_play_opp {opp : Player} {K H : Nat} {R : Board 5} (hE : DiscEP opp K R)
    (c : Fin 5) (hT : TColP opp K H R c) (hl : Legal H R c) :
    DiscEP opp K (play R c opp) := by
  intro d r ⟨hs, hbot⟩
  by_cases hd : d = c
  · subst hd
    rw [play_eq, stone_append] at hs
    by_cases hlt : r < (R d).length
    · rw [if_pos hlt] at hs
      apply hE d r; refine ⟨hs, ?_⟩
      rcases hbot with hz | hp
      · exact Or.inl hz
      · right; rw [play_eq, stone_append, if_pos (by omega)] at hp; exact hp
    · rw [if_neg hlt] at hs
      by_cases heq : r = (R d).length
      · subst heq
        apply hT hl
        by_cases hrz : (R d).length = 0
        · exact Or.inl hrz
        · rcases hbot with hz | hp
          · exact Or.inl hz
          · right; rw [play_eq, stone_append, if_pos (by omega)] at hp; exact hp
      · rw [if_neg heq] at hs; cases hs
  · rw [play_ne _ _ _ _ hd] at hs hbot
    exact hE d r ⟨hs, hbot⟩

theorem tcolP_play_self_me {me : Player} (K H : Nat) (R : Board 5) (e : Fin 5) :
    TColP (opponent me) K H (play R e me) e := by
  intro _ htop
  rcases htop with hz | hs
  · simp [play_eq] at hz
  · rw [play_eq, stone_append, if_neg (by simp), if_pos (by simp)] at hs
    exact absurd (Option.some.inj hs) (ne_opponent me)

theorem tcolP_play_ne {opp : Player} {K H : Nat} {R : Board 5} {e d : Fin 5} (p : Player) (hd : d ≠ e) :
    TColP opp K H (play R e p) d ↔ TColP opp K H R d := by
  simp [TColP, play_ne _ _ _ _ hd]

/-- Core zone localization: under `DiscEP` and `¬ HasFour H R me`, every attacker four-in-a-row
    lies completely inside the bottom `K` rows `truncG K R`. -/
theorem oppFour_low {me : Player} {K H : Nat} (hKH : K ≤ H) {R : Board 5}
    (hE : DiscEP (opponent me) K R) (hnme : ¬ HasFour H R me)
    (hf : HasFour H R (opponent me)) : HasFour K (truncG K R) (opponent me) := by
  have dir : ∀ {x y dx dy},
      ((dx = 0 ∧ dy = 1) ∨ (dx = 1 ∧ dy = 0) ∨ (dx = 1 ∧ dy = 1) ∨ (dx = 1 ∧ dy = -1)) →
      HasFourDir H R (opponent me) x y dx dy →
      HasFourDir K (truncG K R) (opponent me) x y dx dy := by
    intro x y dx dy hdir hd
    obtain ⟨i, ce, _, he⟩ := exists_exceptional_in_line_gen hdir (by rw [opponent_involution]; exact hnme) hd
    have hlow := hE ce _ he
    intro j
    have hj := hd j
    obtain ⟨_, _, hy0, _, _⟩ := cellAtInt_some hj
    obtain ⟨_, _, hyi0, _, _⟩ := cellAtInt_some (hd i)
    have hjK : y + (j : Int) * dy < (K : Int) := by
      rcases hdir with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
    rw [cell_truncG hKH R _ _ hjK]; exact hj
  rcases hf with ⟨x, y, h⟩ | ⟨x, y, h⟩ | ⟨x, y, h⟩ | ⟨x, y, h⟩
  · exact Or.inl ⟨x, y, dir (Or.inl ⟨rfl, rfl⟩) h⟩
  · exact Or.inr (Or.inl ⟨x, y, dir (Or.inr (Or.inl ⟨rfl, rfl⟩)) h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨x, y, dir (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))) h⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨x, y, dir (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))) h⟩))

/-! ## Upper-Zone Column Labels & Parity-Unified Zone Certificate -/

inductive LabG where
  | low | odd | dead
  deriving DecidableEq

def labOfG (H K : Nat) (l : List Player) : LabG :=
  if l.length ≤ K then .low else if (H - l.length) % 2 = 1 then .odd else .dead

def labsG (H K : Nat) (R : Board 5) : Fin 5 → LabG := fun c => labOfG H K (R c)

theorem labsG_play (H K : Nat) (R : Board 5) (e : Fin 5) (p : Player) :
    labsG H K (play R e p) = Function.update (labsG H K R) e (labOfG H K (R e ++ [p])) := by
  funext d
  by_cases hd : d = e
  · subst hd; simp [labsG, play_eq]
  · simp [labsG, play_ne _ _ _ _ hd, Function.update, hd]

theorem labOfG_low {H K : Nat} {l : List Player} (h : labOfG H K l = .low) : l.length ≤ K := by
  unfold labOfG at h
  by_cases h1 : l.length ≤ K
  · exact h1
  · rw [if_neg h1] at h; by_cases h2 : (H - l.length) % 2 = 1 <;> simp [h2] at h

theorem labOfG_odd {H K : Nat} {l : List Player} (h : labOfG H K l = .odd) :
    K < l.length ∧ (H - l.length) % 2 = 1 := by
  unfold labOfG at h
  by_cases h1 : l.length ≤ K
  · rw [if_pos h1] at h; cases h
  · rw [if_neg h1] at h
    by_cases h2 : (H - l.length) % 2 = 1
    · exact ⟨by omega, h2⟩
    · rw [if_neg h2] at h; cases h

def DefOut (me : Player) (K : Nat) (J : Board 5 → (Fin 5 → LabG) → Prop)
    (L : Board 5) (ℓ : Fin 5 → LabG) (e : Fin 5) : Prop :=
  (ℓ e = .low ∧ (L e).length < K ∧ J (play L e me) ℓ) ∨
  (ℓ e = .low ∧ (L e).length = K ∧ J L (Function.update ℓ e .odd)) ∨
  (ℓ e = .odd ∧ J L (Function.update ℓ e .dead))

def DefWin (me : Player) (K : Nat) (L : Board 5) (ℓ : Fin 5 → LabG) : Prop :=
  ∃ e, ℓ e = .low ∧ (L e).length < K ∧ HasFour K (play L e me) me

def ZoneCert2P (me : Player) (K : Nat) (I J : Board 5 → (Fin 5 → LabG) → Prop) : Prop :=
  ∀ L ℓ, I L ℓ → ∀ c : Fin 5,
    (ℓ c = .low → (L c).length < K →
      ¬ HasFour K (play L c (opponent me)) (opponent me) ∧
      (DefWin me K (play L c (opponent me)) ℓ ∨
        ∃ e, (e = c ∨ (L c).length + 5 ≤ K) ∧ DefOut me K J (play L c (opponent me)) ℓ e)) ∧
    (ℓ c = .low → (L c).length = K → J L (Function.update ℓ c .dead)) ∧
    (ℓ c = .odd → (∀ d, Function.update ℓ c .dead d = .dead) ∨
      DefWin me K L (Function.update ℓ c .dead) ∨
      ∃ e, DefOut me K J L (Function.update ℓ c .dead) e)

structure ZInvP (me : Player) (K H : Nat) (I : Board 5 → (Fin 5 → LabG) → Prop) (R : Board 5) : Prop where
  tm    : toMove R = opponent me
  nopp  : ¬ HasFour H R (opponent me)
  nme   : ¬ HasFour H R me
  dE    : DiscEP (opponent me) K R
  dT    : ∀ c, TColP (opponent me) K H R c
  valid : Valid H R
  abs   : I (truncG K R) (labsG H K R) ∨ ∀ c : Fin 5, K < (R c).length

/-- Carrying out an abstract defender move on the real board.
    Notice: ONLY needs `hpar : K % 2 = H % 2` (NOT `K % 2 = 0` or `H % 2 = 0`)! -/
theorem defOut_real {me : Player} {K H : Nat} (hpar : K % 2 = H % 2) (hKH : K + 2 ≤ H)
    {J : Board 5 → (Fin 5 → LabG) → Prop} {R1 : Board 5} {e : Fin 5}
    (ho : DefOut me K J (truncG K R1) (labsG H K R1) e) :
    Legal H R1 e ∧ J (truncG K (play R1 e me)) (labsG H K (play R1 e me)) := by
  rcases ho with ⟨hl, hlen, hJ⟩ | ⟨hl, hlen, hJ⟩ | ⟨hl, hJ⟩
  · have h1 := labOfG_low hl
    rw [truncG_length] at hlen
    have hlt : (R1 e).length < K := by omega
    refine ⟨by unfold Legal; omega, ?_⟩
    rw [truncG_play_low _ hlt, labsG_play]
    have : labOfG H K (R1 e ++ [me]) = labsG H K R1 e := by
      rw [hl]; unfold labOfG; rw [if_pos (by simp; omega)]
    rw [this, Function.update_eq_self]; exact hJ
  · have h1 := labOfG_low hl
    rw [truncG_length] at hlen
    have heq : (R1 e).length = K := by omega
    refine ⟨by unfold Legal; omega, ?_⟩
    rw [truncG_play_high _ (by omega), labsG_play]
    have : labOfG H K (R1 e ++ [me]) = .odd := by
      unfold labOfG
      rw [if_neg (by simp; omega), if_pos (by simp; omega)]
    rw [this]; exact hJ
  · obtain ⟨h1, h2⟩ := labOfG_odd hl
    refine ⟨by unfold Legal; omega, ?_⟩
    rw [truncG_play_high _ (by omega), labsG_play]
    have : labOfG H K (R1 e ++ [me]) = .dead := by
      unfold labOfG
      rw [if_neg (by simp; omega), if_neg (by simp; omega)]
    rw [this]; exact hJ

theorem defWin_real {me : Player} {K H : Nat} (hKH : K + 2 ≤ H) {R1 : Board 5}
    (hw : DefWin me K (truncG K R1) (labsG H K R1)) :
    ∃ e, Legal H R1 e ∧ HasFour H (play R1 e me) me := by
  obtain ⟨e, hl, hlen, hf⟩ := hw
  have h1 := labOfG_low hl
  rw [truncG_length] at hlen
  have hlt : (R1 e).length < K := by omega
  refine ⟨e, by unfold Legal; omega, ?_⟩
  rw [← truncG_play_low _ hlt] at hf
  exact hasFour_of_truncG (by omega) hf

/-- Soundness interface for pluggable zone leaves (e.g. `ClaimOddHyp` or `ClaimEvenHyp`). -/
def ZoneLeafSound (me : Player) (Leaf : Nat → Board 5 → Prop) : Prop :=
  ∀ {K H : Nat} {R : Board 5},
    K % 2 = H % 2 → K ≤ H →
    toMove R = opponent me → ¬ HasFour H R (opponent me) → ¬ HasFour H R me →
    Valid H R → DiscEP (opponent me) K R → (∀ c, TColP (opponent me) K H R c) →
    Leaf K (truncG K R) → SafeP H me R

/-- **Parity-unified, color-polymorphic one-sided zone theorem with pluggable leaves.**
    Requires ONLY `hpar : K % 2 = H % 2` and `hKH : K + 2 ≤ H`. -/
theorem zone_safeL_gen {me : Player} {K H : Nat} (hpar : K % 2 = H % 2) (hKH : K + 2 ≤ H)
    {Leaf : Nat → Board 5 → Prop} (hLeaf : ZoneLeafSound me Leaf)
    {I : Board 5 → (Fin 5 → LabG) → Prop}
    (hI : ZoneCert2P me K I (fun L ℓ => I L ℓ ∨ Leaf K L))
    {R : Board 5} (inv : ZInvP me K H I R) :
    SafeP H me R := by
  have key : ∀ k R, ZInvP me K H I R → SafeFor H me k R := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro R inv
      cases k with
      | zero => exact inv.nopp
      | succ k1 =>
        refine ⟨inv.nopp, Or.inr (Or.inr ?_)⟩
        rw [if_neg (by rw [inv.tm]; exact (ne_opponent me).symm)]
        intro c hc
        rw [inv.tm]
        have hcl : (R c).length < H := hc
        have hE1 : DiscEP (opponent me) K (play R c (opponent me)) :=
          discEP_play_opp inv.dE c (inv.dT c) hc
        have hnb1 : ¬ HasFour H (play R c (opponent me)) me :=
          fun hf => inv.nme (hasFour_play_other_gen (ne_opponent me).symm hf)
        have hv1 : Valid H (play R c (opponent me)) := play_valid inv.valid hc
        have htm1 : toMove (play R c (opponent me)) = me := by
          have htm0 := inv.tm
          unfold toMove at htm0 ⊢
          rw [totalStones_play]
          by_cases h0 : totalStones R % 2 = 0
          · rw [if_pos h0] at htm0; rw [if_neg (by omega)]; cases me with | black => cases htm0 | white => rfl
          · rw [if_neg h0] at htm0; rw [if_pos (by omega)]; cases me with | black => rfl | white => cases htm0
        -- Helper to close after choosing reply e
        have finishReply : ∀ (hno1 : ¬ HasFour H (play R c (opponent me)) (opponent me))
            (e : Fin 5) (he : Legal H (play R c (opponent me)) e)
            (hT2 : ∀ d, TColP (opponent me) K H (play (play R c (opponent me)) e me) d)
            (habs2 : (I (truncG K (play (play R c (opponent me)) e me))
                        (labsG H K (play (play R c (opponent me)) e me)) ∨
                      Leaf K (truncG K (play (play R c (opponent me)) e me))) ∨
                     ∀ d : Fin 5, K < (play (play R c (opponent me)) e me d).length),
            SafeFor H me k1 (play R c (opponent me)) := by
          intro hno1 e he hT2 habs2
          cases k1 with
          | zero => exact hno1
          | succ k2 =>
            refine ⟨hno1, Or.inr (Or.inr ?_)⟩
            rw [if_pos htm1]
            refine ⟨e, he, ?_⟩
            rw [htm1]
            by_cases hwin2 : HasFour H (play (play R c (opponent me)) e me) me
            · cases k2 with
              | zero => exact fun hf => hno1 (hasFour_play_other_gen (ne_opponent me) hf)
              | succ k3 => exact ⟨fun hf => hno1 (hasFour_play_other_gen (ne_opponent me) hf), Or.inl hwin2⟩
            · have htm2 : toMove (play (play R c (opponent me)) e me) = opponent me := by
                unfold toMove at *; rw [totalStones_play, totalStones_play]
                have hm : (totalStones R + 1 + 1) % 2 = totalStones R % 2 := by omega
                rw [hm]; exact inv.tm
              have hno2 : ¬ HasFour H (play (play R c (opponent me)) e me) (opponent me) :=
                fun hf => hno1 (hasFour_play_other_gen (ne_opponent me) hf)
              have hE2 := discEP_play_me hE1 e
              have hv2 : Valid H (play (play R c (opponent me)) e me) := play_valid hv1 he
              rcases habs2 with (hI2 | hLf) | hhigh2
              · exact ih k2 (by omega) _ ⟨htm2, hno2, hwin2, hE2, hT2, hv2, Or.inl hI2⟩
              · exact hLeaf hpar (by omega) htm2 hno2 hwin2 hv2 hE2 hT2 hLf k2
              · exact ih k2 (by omega) _ ⟨htm2, hno2, hwin2, hE2, hT2, hv2, Or.inr hhigh2⟩
        -- Case split on height of c relative to K
        by_cases hltK : (R c).length < K
        · -- Low move inside bottom K rows
          have hI0 : I (truncG K R) (labsG H K R) := by
            rcases inv.abs with h | hall
            · exact h
            · have := hall c; omega
          have hlab : labsG H K R c = .low := by simp [labsG, labOfG, show (R c).length ≤ K by omega]
          have htlen : (truncG K R c).length < K := by rw [truncG_length]; omega
          obtain ⟨hnwK, hreply⟩ := (hI _ _ hI0 c).1 hlab htlen
          have htr1 : truncG K (play R c (opponent me)) = play (truncG K R) c (opponent me) :=
            truncG_play_low _ hltK
          have hlabs1 : labsG H K (play R c (opponent me)) = labsG H K R := by
            rw [labsG_play]
            have : labOfG H K (R c ++ [opponent me]) = labsG H K R c := by
              rw [hlab]; unfold labOfG; rw [if_pos (by simp; omega)]
            rw [this, Function.update_eq_self]
          have hno1 : ¬ HasFour H (play R c (opponent me)) (opponent me) := by
            intro hf
            have hfl := oppFour_low (by omega) hE1 hnb1 hf
            rw [htr1] at hfl; exact hnwK hfl
          rcases hreply with hw | ⟨e, hcond, hout⟩
          · rw [← htr1, ← hlabs1] at hw
            obtain ⟨e, he, hwin⟩ := defWin_real hKH hw
            cases k1 with
            | zero => exact hno1
            | succ k2 =>
              refine ⟨hno1, Or.inr (Or.inr ?_)⟩
              rw [if_pos htm1]
              refine ⟨e, he, ?_⟩
              rw [htm1]
              cases k2 with
              | zero => exact fun hf => hno1 (hasFour_play_other_gen (ne_opponent me) hf)
              | succ k3 => exact ⟨fun hf => hno1 (hasFour_play_other_gen (ne_opponent me) hf), Or.inl hwin⟩
          · rw [← htr1, ← hlabs1] at hout
            obtain ⟨he, hJ2⟩ := defOut_real hpar hKH hout
            have hT2 : ∀ d, TColP (opponent me) K H (play (play R c (opponent me)) e me) d := by
              intro d
              by_cases hde : d = e
              · subst hde; exact tcolP_play_self_me K H _ d
              · rw [tcolP_play_ne _ hde]
                by_cases hdc : d = c
                · subst hdc
                  rcases hcond with rfl | hroom
                  · exact absurd rfl hde
                  · rw [truncG_length] at hroom
                    intro _ _; rw [play_eq, List.length_append]; simp; omega
                · rw [tcolP_play_ne _ hdc]; exact inv.dT d
            exact finishReply hno1 e he hT2 (Or.inl hJ2)
        · -- High move: K ≤ (R c).length
          have htr1 : truncG K (play R c (opponent me)) = truncG K R := truncG_play_high _ (by omega)
          have hno1 : ¬ HasFour H (play R c (opponent me)) (opponent me) := by
            intro hf
            have hfl := oppFour_low (by omega) hE1 hnb1 hf
            rw [htr1] at hfl
            exact inv.nopp (hasFour_of_truncG (by omega) hfl)
          by_cases hcap : (R c).length + 1 = H
          · -- Attacker caps column c (must have (R c).length > K since K + 2 ≤ H)
            by_cases hfull : BoardFull H (play R c (opponent me))
            · cases k1 with
              | zero => exact hno1
              | succ _ => exact ⟨hno1, Or.inr (Or.inl hfull)⟩
            · rcases inv.abs with hI0 | hhigh
              · have hlab : labsG H K R c = .odd := by
                  simp only [labsG, labOfG]
                  rw [if_neg (by omega), if_pos (by omega)]
                have hlabs1 : labsG H K (play R c (opponent me)) = Function.update (labsG H K R) c .dead := by
                  rw [labsG_play]
                  have : labOfG H K (R c ++ [opponent me]) = .dead := by
                    unfold labOfG; rw [if_neg (by simp; omega), if_neg (by simp; omega)]
                  rw [this]
                rcases (hI _ _ hI0 c).2.2 hlab with hallD | hw | ⟨e, hout⟩
                · have hex : ∃ e : Fin 5, Legal H (play R c (opponent me)) e := by
                    by_contra hnone; apply hfull; intro d
                    have := hv1 d; by_contra hne; exact hnone ⟨d, by unfold Legal; omega⟩
                  obtain ⟨e, he⟩ := hex
                  have hT2 : ∀ d, TColP (opponent me) K H (play (play R c (opponent me)) e me) d := by
                    intro d
                    by_cases hde : d = e
                    · subst hde; exact tcolP_play_self_me K H _ d
                    · rw [tcolP_play_ne _ hde]
                      by_cases hdc : d = c
                      · subst hdc; intro hlt; rw [play_eq, List.length_append] at hlt; simp at hlt; omega
                      · rw [tcolP_play_ne _ hdc]; exact inv.dT d
                  have hhigh2 : ∀ d : Fin 5, K < (play (play R c (opponent me)) e me d).length := by
                    intro d
                    have hd := hallD d
                    rw [← hlabs1] at hd
                    have hgt : K < (play R c (opponent me) d).length := by
                      unfold labsG labOfG at hd
                      by_cases h1 : (play R c (opponent me) d).length ≤ K
                      · rw [if_pos h1] at hd; cases hd
                      · omega
                    by_cases hde : d = e
                    · subst hde; rw [play_eq, List.length_append]; simp; omega
                    · rw [play_ne _ _ _ _ hde]; exact hgt
                  exact finishReply hno1 e he hT2 (Or.inr hhigh2)
                · rw [← htr1, ← hlabs1] at hw
                  obtain ⟨e, he, hwin⟩ := defWin_real hKH hw
                  cases k1 with
                  | zero => exact hno1
                  | succ k2 =>
                    refine ⟨hno1, Or.inr (Or.inr ?_)⟩
                    rw [if_pos htm1]
                    refine ⟨e, he, ?_⟩
                    rw [htm1]
                    cases k2 with
                    | zero => exact fun hf => hno1 (hasFour_play_other_gen (ne_opponent me) hf)
                    | succ k3 => exact ⟨fun hf => hno1 (hasFour_play_other_gen (ne_opponent me) hf), Or.inl hwin⟩
                · rw [← htr1, ← hlabs1] at hout
                  obtain ⟨he, hJ2⟩ := defOut_real hpar hKH hout
                  have hT2 : ∀ d, TColP (opponent me) K H (play (play R c (opponent me)) e me) d := by
                    intro d
                    by_cases hde : d = e
                    · subst hde; exact tcolP_play_self_me K H _ d
                    · rw [tcolP_play_ne _ hde]
                      by_cases hdc : d = c
                      · subst hdc; intro hlt; rw [play_eq, List.length_append] at hlt; simp at hlt; omega
                      · rw [tcolP_play_ne _ hdc]; exact inv.dT d
                  exact finishReply hno1 e he hT2 (Or.inl hJ2)
              · -- All columns already > K: pick ANY non-full column e, preserving `∀ d, K < len`!
                have hex : ∃ e : Fin 5, Legal H (play R c (opponent me)) e := by
                  by_contra hnone; apply hfull; intro d
                  have := hv1 d; by_contra hne; exact hnone ⟨d, by unfold Legal; omega⟩
                obtain ⟨e, he⟩ := hex
                have hT2 : ∀ d, TColP (opponent me) K H (play (play R c (opponent me)) e me) d := by
                  intro d
                  by_cases hde : d = e
                  · subst hde; exact tcolP_play_self_me K H _ d
                  · rw [tcolP_play_ne _ hde]
                    by_cases hdc : d = c
                    · subst hdc; intro hlt; rw [play_eq, List.length_append] at hlt; simp at hlt; omega
                    · rw [tcolP_play_ne _ hdc]; exact inv.dT d
                have hhigh2 : ∀ d : Fin 5, K < (play (play R c (opponent me)) e me d).length := by
                  intro d
                  have hd := hhigh d
                  by_cases hde : d = e
                  · subst hde
                    by_cases hdc : d = c
                    · subst hdc; simp [play_eq]; omega
                    · simp [play_eq, play_ne _ _ _ _ hdc]; omega
                  · rw [play_ne _ _ _ _ hde]
                    by_cases hdc : d = c
                    · subst hdc; rw [play_eq, List.length_append]; simp; omega
                    · rw [play_ne _ _ _ _ hdc]; exact hd
                exact finishReply hno1 e he hT2 (Or.inr hhigh2)
          · -- Non-capping high move: defender simply covers in column c!
            have he : Legal H (play R c (opponent me)) c := by
              unfold Legal; rw [play_eq, List.length_append]; simp; omega
            have hT2 : ∀ d, TColP (opponent me) K H (play (play R c (opponent me)) c me) d := by
              intro d
              by_cases hdc : d = c
              · subst hdc; exact tcolP_play_self_me K H _ d
              · rw [tcolP_play_ne _ hdc, tcolP_play_ne _ hdc]; exact inv.dT d
            have habs2 : (I (truncG K (play (play R c (opponent me)) c me))
                            (labsG H K (play (play R c (opponent me)) c me)) ∨
                          Leaf K (truncG K (play (play R c (opponent me)) c me))) ∨
                         ∀ d : Fin 5, K < (play (play R c (opponent me)) c me d).length := by
              rcases inv.abs with hI0 | hhigh
              · left
                have htr2 : truncG K (play (play R c (opponent me)) c me) = truncG K R := by
                  rw [truncG_play_high _ (by rw [play_eq, List.length_append]; simp; omega), htr1]
                have hlabs2 : labsG H K (play (play R c (opponent me)) c me) =
                    Function.update (labsG H K R) c (labOfG H K (play R c (opponent me) c ++ [me])) := by
                  rw [labsG_play, labsG_play, Function.update_idem]
                rw [htr2, hlabs2]
                have hlen2 : (play R c (opponent me) c ++ [me]).length = (R c).length + 2 := by
                  simp [play_eq]
                by_cases hKc : (R c).length = K
                · have hlab : labsG H K R c = .low := by simp [labsG, labOfG, hKc]
                  have : labOfG H K (play R c (opponent me) c ++ [me]) = .dead := by
                    unfold labOfG; rw [hlen2, if_neg (by omega), if_neg (by omega)]
                  rw [this]
                  exact (hI _ _ hI0 c).2.1 hlab (by rw [truncG_length]; omega)
                · have : labOfG H K (play R c (opponent me) c ++ [me]) = labsG H K R c := by
                    have hpar2 : (H - ((R c).length + 2)) % 2 = (H - (R c).length) % 2 := by omega
                    simp only [labsG, labOfG]
                    rw [hlen2, if_neg (show ¬ (R c).length + 2 ≤ K by omega), if_neg (show ¬ (R c).length ≤ K by omega), hpar2]
                  rw [this, Function.update_eq_self]
                  exact Or.inl hI0
              · right; intro d
                have := hhigh d
                by_cases hdc : d = c
                · subst hdc; simp [play_eq]; omega
                · rw [play_ne _ _ _ _ hdc, play_ne _ _ _ _ hdc]; exact this
            exact finishReply hno1 c he hT2 habs2
  exact fun k => key k R inv

#print axioms zone_safeL_gen

end C4W5Gen
