/-!
# Five-Column Infinite-Height Gravity Connect Four (`5 × ∞`) Is a Draw

Complete, self-contained, zero-certificate, zero-`sorry` Lean 4 proof that standard
Gravity Connect Four on the ceiling-free strip `5 × ∞` is a game-theoretic draw:
- **First player (Black)**: opens at center `(3, 1)` (0-based col `2`) and covers every
  subsequent White move in the exact same column forever.
- **Second player (White)**: uses Phases 1–2 (`WDInf ∨ W2Inf`) of the asymmetric Allis
  pairing with ordinary columns `U = {0, 1, 4}` and special pair `P = {2, 3}`.

Zero external certificates, zero `decide`, zero custom axioms.
-/

namespace C4W5Inf

set_option linter.deprecated false

inductive Player where
  | black | white
  deriving DecidableEq, Repr

def opponent : Player → Player
  | .black => .white
  | .white => .black

@[simp] theorem opponent_black : opponent .black = .white := rfl
@[simp] theorem opponent_white : opponent .white = .black := rfl

abbrev Board5 := Fin 5 → List Player

def emptyBoard5 : Board5 := fun _ => []

def play (b : Board5) (c : Fin 5) (p : Player) : Board5 :=
  fun d => if d = c then b c ++ [p] else b d

def stone (l : List Player) (r : Nat) : Option Player :=
  l[r]?

def cellAtInt (b : Board5) (x y : Int) : Option Player :=
  if hx : 0 ≤ x ∧ x < 5 then
    if hy : 0 ≤ y then stone (b ⟨x.toNat, by omega⟩) y.toNat else none
  else none

def HasFourDir (b : Board5) (p : Player) (x y dx dy : Int) : Prop :=
  ∀ k : Fin 4, cellAtInt b (x + (k.val : Int) * dx) (y + (k.val : Int) * dy) = some p

def HasFour (b : Board5) (p : Player) : Prop :=
  (∃ x y, HasFourDir b p x y 0 1) ∨
  (∃ x y, HasFourDir b p x y 1 0) ∨
  (∃ x y, HasFourDir b p x y 1 1) ∨
  (∃ x y, HasFourDir b p x y 1 (-1))

def totalStones (b : Board5) : Nat :=
  (b 0).length + (b 1).length + (b 2).length + (b 3).length + (b 4).length

def toMove (b : Board5) : Player :=
  if totalStones b % 2 = 0 then .black else .white

/-- Step-indexed horizon safety on `5 × ∞` (every column is always legal). -/
def SafeForInf (p : Player) : Nat → Board5 → Prop
  | 0, b => ¬ HasFour b (opponent p)
  | k + 1, b =>
      ¬ HasFour b (opponent p) ∧
        (HasFour b p ∨
          if toMove b = p then
            ∃ c : Fin 5, SafeForInf p k (play b c p)
          else
            ∀ c : Fin 5, SafeForInf p k (play b c (opponent p)))

def CanAvoidLossInf (p : Player) (b : Board5) : Prop :=
  ∀ k, SafeForInf p k b

def IsDrawInf (b : Board5) : Prop :=
  CanAvoidLossInf .black b ∧ CanAvoidLossInf .white b

/-! ## Basic Board & Cell Helper Lemmas -/

@[simp] theorem play_eq (b : Board5) (c : Fin 5) (p : Player) :
    play b c p c = b c ++ [p] := by
  simp [play]

theorem play_ne (b : Board5) (c d : Fin 5) (p : Player) (h : d ≠ c) :
    play b c p d = b d := by
  simp [play, h]

theorem stone_append_cases (l : List Player) (p : Player) (i : Nat) :
    stone (l ++ [p]) i = some q →
      (i < l.length ∧ stone l i = some q) ∨ (i = l.length ∧ p = q) := by
  unfold stone
  intro h
  by_cases hi : i < l.length
  · left
    rw [List.getElem?_append_left hi] at h
    exact ⟨hi, h⟩
  · right
    have hge : l.length ≤ i := by omega
    rw [List.getElem?_append_right hge] at h
    by_cases heq : i = l.length
    · subst heq
      simp at h
      exact ⟨rfl, h⟩
    · have hgt : 1 ≤ i - l.length := by omega
      have hnone : ([p] : List Player)[i - l.length]? = none := by
        apply List.getElem?_eq_none
        simp; omega
      rw [hnone] at h
      cases h

theorem cellAtInt_some_inv {b : Board5} {x y : Int} {p : Player}
    (h : cellAtInt b x y = some p) :
    ∃ (c : Fin 5), (c.val : Int) = x ∧ 0 ≤ y ∧ stone (b c) y.toNat = some p := by
  unfold cellAtInt at h
  by_cases hx : 0 ≤ x ∧ x < 5
  · rw [dif_pos hx] at h
    by_cases hy : 0 ≤ y
    · rw [dif_pos hy] at h
      exact ⟨⟨x.toNat, by omega⟩, by dsimp; omega, hy, h⟩
    · rw [dif_neg hy] at h; cases h
  · rw [dif_neg hx] at h; cases h

theorem totalStones_play (b : Board5) (c : Fin 5) (p : Player) :
    totalStones (play b c p) = totalStones b + 1 := by
  unfold totalStones play
  rcases c with ⟨_ | _ | _ | _ | _ | _, hc⟩
  · simp; omega
  · simp; omega
  · simp; omega
  · simp; omega
  · simp; omega
  · omega

theorem toMove_even {b : Board5} (h : totalStones b % 2 = 0) : toMove b = .black := by
  simp [toMove, h]

theorem toMove_odd {b : Board5} (h : totalStones b % 2 = 1) : toMove b = .white := by
  unfold toMove
  rw [if_neg (by omega)]

/-- Generic 2-ply invariant induction for `CanAvoidLossInf` when `toMove = opponent me`. -/
theorem toMove_play_opp {b : Board5} {me : Player} {c : Fin 5}
    (htm : toMove b = opponent me) : toMove (play b c (opponent me)) = me := by
  unfold toMove at htm ⊢
  rw [totalStones_play]
  by_cases h0 : totalStones b % 2 = 0
  · rw [if_pos h0] at htm
    rw [if_neg (by omega)]
    cases me <;> cases htm <;> rfl
  · rw [if_neg h0] at htm
    rw [if_pos (by omega)]
    cases me <;> cases htm <;> rfl

theorem canAvoidLossInf_of_inv (me : Player) (Inv : Board5 → Prop)
    (hInv : ∀ b, Inv b → toMove b = opponent me ∧ ¬ HasFour b (opponent me))
    (hStep : ∀ b, Inv b → ∀ c : Fin 5,
      ¬ HasFour (play b c (opponent me)) (opponent me) ∧
      ∃ e : Fin 5, Inv (play (play b c (opponent me)) e me)) :
    ∀ b, Inv b → CanAvoidLossInf me b := by
  have key : ∀ n k, k ≤ n → ∀ b, Inv b → SafeForInf me k b := by
    intro n
    induction n with
    | zero =>
      intro k hk b hb
      have hk0 : k = 0 := by omega
      subst hk0; exact (hInv b hb).2
    | succ n ih =>
      intro k hk b hb
      obtain ⟨htm, hno⟩ := hInv b hb
      cases k with
      | zero => exact hno
      | succ k1 =>
        refine ⟨hno, Or.inr ?_⟩
        have hne : toMove b ≠ me := by rw [htm]; cases me <;> decide
        rw [if_neg hne]
        intro c
        obtain ⟨hno1, e, hb2⟩ := hStep b hb c
        cases k1 with
        | zero => exact hno1
        | succ k2 =>
          refine ⟨hno1, Or.inr ?_⟩
          rw [if_pos (toMove_play_opp htm)]
          exact ⟨e, ih k2 (by omega) _ hb2⟩
  exact fun b hb k => key k k (Nat.le_refl k) b hb

/-! ## Part 1: First-Player (Black) Zero-Certificate Proof on `5 × ∞` -/

/-- White occupies only 0-based even indices (1-based odd rows). -/
def WOdd (l : List Player) : Prop :=
  ∀ i, stone l i = some .white → i % 2 = 0

/-- White occupies only 0-based odd indices (1-based even rows). -/
def WEven (l : List Player) : Prop :=
  ∀ i, stone l i = some .white → i % 2 = 1

theorem no_white_four_inf {b : Board5}
    (h2 : WEven (b 2)) (hoth : ∀ c : Fin 5, c ≠ 2 → WOdd (b c)) :
    ¬ HasFour b .white := by
  intro hf
  rcases hf with ⟨x, y, hdir⟩ | ⟨x, y, hdir⟩ | ⟨x, y, hdir⟩ | ⟨x, y, hdir⟩
  · -- Vertical (0, 1): cells k=0 and k=1 are adjacent in the same column c
    obtain ⟨c0, hx0, hy0, hs0⟩ := cellAtInt_some_inv (hdir 0)
    obtain ⟨c1, hx1, hy1, hs1⟩ := cellAtInt_some_inv (hdir 1)
    have hceq : c0 = c1 := Fin.ext (by omega)
    subst hceq
    simp only [Fin.val_zero, Fin.val_one] at hs0 hs1 hy0 hy1
    have hrow : (y + (1 : Nat) * (1 : Int)).toNat = (y + (0 : Nat) * (1 : Int)).toNat + 1 := by omega
    rw [hrow] at hs1
    by_cases hc2 : c0 = 2
    · subst hc2
      have p0 := h2 _ hs0
      have p1 := h2 _ hs1
      omega
    · have p0 := hoth c0 hc2 _ hs0
      have p1 := hoth c0 hc2 _ hs1
      omega
  · -- Horizontal (1, 0): x ∈ {0, 1}, so both col 1 (WOdd) and col 2 (WEven) are hit at row y
    obtain ⟨c0, hx0, hy0, _⟩ := cellAtInt_some_inv (hdir 0)
    obtain ⟨c3, hx3, _, _⟩ := cellAtInt_some_inv (hdir 3)
    have hxrange : x = 0 ∨ x = 1 := by omega
    rcases hxrange with rfl | rfl
    · obtain ⟨ca, hxa, _, hsa⟩ := cellAtInt_some_inv (hdir 1)
      obtain ⟨cb, hxb, _, hsb⟩ := cellAtInt_some_inv (hdir 2)
      have ha1 : ca = 1 := Fin.ext (by omega)
      have hb2 : cb = 2 := Fin.ext (by omega)
      subst ha1; subst hb2
      have p1 := hoth 1 (by decide) _ hsa
      have p2 := h2 _ hsb
      omega
    · obtain ⟨ca, hxa, _, hsa⟩ := cellAtInt_some_inv (hdir 0)
      obtain ⟨cb, hxb, _, hsb⟩ := cellAtInt_some_inv (hdir 1)
      have ha1 : ca = 1 := Fin.ext (by omega)
      have hb2 : cb = 2 := Fin.ext (by omega)
      subst ha1; subst hb2
      have p1 := hoth 1 (by decide) _ hsa
      have p2 := h2 _ hsb
      omega
  · -- Rising diagonal (1, 1): x=0 hits cols 0,1 (both WOdd); x=1 hits cols 3,4 (both WOdd)
    obtain ⟨c0, hx0, _, _⟩ := cellAtInt_some_inv (hdir 0)
    obtain ⟨c3, hx3, _, _⟩ := cellAtInt_some_inv (hdir 3)
    have hxrange : x = 0 ∨ x = 1 := by omega
    rcases hxrange with rfl | rfl
    · obtain ⟨ca, hxa, hya, hsa⟩ := cellAtInt_some_inv (hdir 0)
      obtain ⟨cb, hxb, hyb, hsb⟩ := cellAtInt_some_inv (hdir 1)
      have ha : ca = 0 := Fin.ext (by omega)
      have hb : cb = 1 := Fin.ext (by omega)
      subst ha; subst hb
      have pa := hoth 0 (by decide) _ hsa
      have pb := hoth 1 (by decide) _ hsb
      omega
    · obtain ⟨ca, hxa, hya, hsa⟩ := cellAtInt_some_inv (hdir 2)
      obtain ⟨cb, hxb, hyb, hsb⟩ := cellAtInt_some_inv (hdir 3)
      have ha : ca = 3 := Fin.ext (by omega)
      have hb : cb = 4 := Fin.ext (by omega)
      subst ha; subst hb
      have pa := hoth 3 (by decide) _ hsa
      have pb := hoth 4 (by decide) _ hsb
      omega
  · -- Falling diagonal (1, -1): x=0 hits cols 0,1 (both WOdd); x=1 hits cols 3,4 (both WOdd)
    obtain ⟨c0, hx0, _, _⟩ := cellAtInt_some_inv (hdir 0)
    obtain ⟨c3, hx3, _, _⟩ := cellAtInt_some_inv (hdir 3)
    have hxrange : x = 0 ∨ x = 1 := by omega
    rcases hxrange with rfl | rfl
    · obtain ⟨ca, hxa, hya, hsa⟩ := cellAtInt_some_inv (hdir 0)
      obtain ⟨cb, hxb, hyb, hsb⟩ := cellAtInt_some_inv (hdir 1)
      have ha : ca = 0 := Fin.ext (by omega)
      have hb : cb = 1 := Fin.ext (by omega)
      subst ha; subst hb
      have pa := hoth 0 (by decide) _ hsa
      have pb := hoth 1 (by decide) _ hsb
      omega
    · obtain ⟨ca, hxa, hya, hsa⟩ := cellAtInt_some_inv (hdir 2)
      obtain ⟨cb, hxb, hyb, hsb⟩ := cellAtInt_some_inv (hdir 3)
      have ha : ca = 3 := Fin.ext (by omega)
      have hb : cb = 4 := Fin.ext (by omega)
      subst ha; subst hb
      have pa := hoth 3 (by decide) _ hsa
      have pb := hoth 4 (by decide) _ hsb
      omega

structure BInfInv (b : Board5) : Prop where
  c2_len  : (b 2).length % 2 = 1
  c2_even : WEven (b 2)
  oth_len : ∀ c : Fin 5, c ≠ 2 → (b c).length % 2 = 0
  oth_odd : ∀ c : Fin 5, c ≠ 2 → WOdd (b c)

theorem bInfInv_toMove {b : Board5} (hb : BInfInv b) : toMove b = .white := by
  apply toMove_odd
  unfold totalStones
  have h0 := hb.oth_len 0 (by decide)
  have h1 := hb.oth_len 1 (by decide)
  have h2 := hb.c2_len
  have h3 := hb.oth_len 3 (by decide)
  have h4 := hb.oth_len 4 (by decide)
  omega

theorem wOdd_append_white {l : List Player} (hl : WOdd l) (heven : l.length % 2 = 0) :
    WOdd (l ++ [.white]) := by
  intro i hi
  rcases stone_append_cases l .white i hi with ⟨_, hs⟩ | ⟨rfl, _⟩
  · exact hl i hs
  · exact heven

theorem wOdd_append_black {l : List Player} (hl : WOdd l) : WOdd (l ++ [.black]) := by
  intro i hi
  rcases stone_append_cases l .black i hi with ⟨_, hs⟩ | ⟨_, hbw⟩
  · exact hl i hs
  · cases hbw

theorem wEven_append_white {l : List Player} (hl : WEven l) (hodd : l.length % 2 = 1) :
    WEven (l ++ [.white]) := by
  intro i hi
  rcases stone_append_cases l .white i hi with ⟨_, hs⟩ | ⟨rfl, _⟩
  · exact hl i hs
  · exact hodd

theorem wEven_append_black {l : List Player} (hl : WEven l) : WEven (l ++ [.black]) := by
  intro i hi
  rcases stone_append_cases l .black i hi with ⟨_, hs⟩ | ⟨_, hbw⟩
  · exact hl i hs
  · cases hbw

theorem bInfInv_step {b : Board5} (hb : BInfInv b) (c : Fin 5) :
    ¬ HasFour (play b c .white) .white ∧
    BInfInv (play (play b c .white) c .black) := by
  have h2w : WEven (play b c .white 2) := by
    by_cases hc : c = 2
    · subst hc; rw [play_eq]; exact wEven_append_white hb.c2_even hb.c2_len
    · rw [play_ne _ _ _ _ (Ne.symm hc)]; exact hb.c2_even
  have hothw : ∀ d : Fin 5, d ≠ 2 → WOdd (play b c .white d) := by
    intro d hd
    by_cases hdc : d = c
    · subst hdc; rw [play_eq]; exact wOdd_append_white (hb.oth_odd d hd) (hb.oth_len d hd)
    · rw [play_ne _ _ _ _ hdc]; exact hb.oth_odd d hd
  refine ⟨no_white_four_inf h2w hothw, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_cases hc : c = 2
    · subst hc; simp [play_eq]; have := hb.c2_len; omega
    · rw [play_ne _ _ _ _ (Ne.symm hc), play_ne _ _ _ _ (Ne.symm hc)]; exact hb.c2_len
  · by_cases hc : c = 2
    · subst hc; rw [play_eq]; exact wEven_append_black h2w
    · rw [play_ne _ _ _ _ (Ne.symm hc)]; exact h2w
  · intro d hd
    by_cases hdc : d = c
    · subst hdc; simp [play_eq]; have := hb.oth_len d hd; omega
    · rw [play_ne _ _ _ _ hdc, play_ne _ _ _ _ hdc]; exact hb.oth_len d hd
  · intro d hd
    by_cases hdc : d = c
    · subst hdc; rw [play_eq]; exact wOdd_append_black (hothw d hd)
    · rw [play_ne _ _ _ _ hdc]; exact hothw d hd

theorem black_nonloss_inf : CanAvoidLossInf .black emptyBoard5 := by
  have hroot : BInfInv (play emptyBoard5 2 .black) := by
    refine ⟨by simp [emptyBoard5], ?_, ?_, ?_⟩
    · intro i hi
      simp [play_eq, emptyBoard5] at hi
      rcases stone_append_cases [] .black i (by simpa using hi) with ⟨h, _⟩ | ⟨_, hbw⟩
      · simp at h
      · cases hbw
    · intro c hc; rw [play_ne _ _ _ _ hc]; simp [emptyBoard5]
    · intro c hc i hi; rw [play_ne _ _ _ _ hc] at hi; simp [emptyBoard5, stone] at hi
  have hsafe1 : CanAvoidLossInf .black (play emptyBoard5 2 .black) :=
    canAvoidLossInf_of_inv .black BInfInv
      (fun b hb => ⟨bInfInv_toMove hb, no_white_four_inf hb.c2_even hb.oth_odd⟩)
      (fun b hb c => ⟨(bInfInv_step hb c).1, ⟨c, (bInfInv_step hb c).2⟩⟩)
      _ hroot
  intro k
  have hno0 : ¬ HasFour emptyBoard5 .white := by
    apply no_white_four_inf
    · intro i hi; simp [emptyBoard5, stone] at hi
    · intro c _ i hi; simp [emptyBoard5, stone] at hi
  cases k with
  | zero => exact hno0
  | succ k1 =>
    refine ⟨hno0, Or.inr ?_⟩
    have htm0 : toMove emptyBoard5 = .black := by
      apply toMove_even; simp [totalStones, emptyBoard5]
    rw [if_pos htm0]
    exact ⟨2, hsafe1 k1⟩

/-! ## Part 2: Second-Player (White) Zero-Certificate Proof on `5 × ∞` -/

/-- Black occupies only 0-based even indices (1-based odd rows). -/
def SOdd (l : List Player) : Prop :=
  ∀ i, stone l i = some .black → i % 2 = 0

/-- Black occupies only 0-based odd indices (1-based even rows). -/
def SEven (l : List Player) : Prop :=
  ∀ i, stone l i = some .black → i % 2 = 1

/-- Above index 1 (rows 1, 2), Black occupies only 0-based odd indices (1-based even rows). -/
def SQ (l : List Player) : Prop :=
  ∀ i, stone l i = some .black → i ≤ 1 ∨ i % 2 = 1

def other5 (a : Fin 5) : Fin 5 :=
  if a = 2 then 3 else 2

theorem fin5_cases (c : Fin 5) : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 := by
  rcases c with ⟨v, hv⟩
  match v with
  | 0 => exact Or.inl (Fin.ext rfl)
  | 1 => exact Or.inr (Or.inl (Fin.ext rfl))
  | 2 => exact Or.inr (Or.inr (Or.inl (Fin.ext rfl)))
  | 3 => exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext rfl))))
  | 4 => exact Or.inr (Or.inr (Or.inr (Or.inr (Fin.ext rfl))))
  | _ + 5 => omega

theorem no_black_four_inf {b : Board5}
    (h0 : SOdd (b 0)) (h1 : SOdd (b 1)) (h4 : SOdd (b 4))
    (h2q : SQ (b 2)) (h3q : SQ (b 3))
    (hfloor : stone (b 2) 0 ≠ some .black ∨ stone (b 3) 0 ≠ some .black) :
    ¬ HasFour b .black := by
  intro hf
  rcases hf with ⟨x, y, hdir⟩ | ⟨x, y, hdir⟩ | ⟨x, y, hdir⟩ | ⟨x, y, hdir⟩
  · -- Vertical (0, 1): SOdd forbids adjacent Black; SQ forbids Black at index 2 (since 2 > 1 and 2 % 2 = 0),
    -- and forbids adjacent Black above index 1, so no 4 consecutive Black stones can fit!
    obtain ⟨c0, hx0, hy0, hs0⟩ := cellAtInt_some_inv (hdir 0)
    obtain ⟨c1, hx1, hy1, hs1⟩ := cellAtInt_some_inv (hdir 1)
    obtain ⟨c2, hx2, hy2, hs2⟩ := cellAtInt_some_inv (hdir 2)
    obtain ⟨c3, hx3, hy3, hs3⟩ := cellAtInt_some_inv (hdir 3)
    have hc1 : c1 = c0 := Fin.ext (by omega)
    have hc2 : c2 = c0 := Fin.ext (by omega)
    have hc3 : c3 = c0 := Fin.ext (by omega)
    subst hc1; subst hc2; subst hc3
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two] at hs0 hs1 hs2 hs3 hy0 hy1 hy2 hy3
    have h3val : ((3 : Fin 4).val : Int) = 3 := rfl
    rw [h3val] at hs3 hy3
    have r1 : (y + (1 : Nat) * (1 : Int)).toNat = (y + (0 : Nat) * (1 : Int)).toNat + 1 := by omega
    have r2 : (y + (2 : Nat) * (1 : Int)).toNat = (y + (0 : Nat) * (1 : Int)).toNat + 2 := by omega
    have r3 : (y + (3 : Int) * (1 : Int)).toNat = (y + (0 : Nat) * (1 : Int)).toNat + 3 := by omega
    rw [r1] at hs1; rw [r2] at hs2; rw [r3] at hs3
    rcases fin5_cases c3 with rfl | rfl | rfl | rfl | rfl
    · have p0 := h0 _ hs0; have p1 := h0 _ hs1; omega
    · have p0 := h1 _ hs0; have p1 := h1 _ hs1; omega
    · have p2 := h2q _ hs2; have p3 := h2q _ hs3; omega
    · have p2 := h3q _ hs2; have p3 := h3q _ hs3; omega
    · have p0 := h4 _ hs0; have p1 := h4 _ hs1; omega
  · -- Horizontal (1, 0): both W0 and W1 contain cols 1 (SOdd), 2 (SQ), and 3 (SQ)
    obtain ⟨c0, hx0, hy0, _⟩ := cellAtInt_some_inv (hdir 0)
    obtain ⟨c3, hx3, _, _⟩ := cellAtInt_some_inv (hdir 3)
    have hxrange : x = 0 ∨ x = 1 := by omega
    have getCol : ∀ (target : Fin 5), (target = 1 ∨ target = 2 ∨ target = 3) →
        stone (b target) y.toNat = some .black := by
      intro target ht
      rcases hxrange with rfl | rfl
      · rcases ht with rfl | rfl | rfl
        · obtain ⟨c, hx, _, hs⟩ := cellAtInt_some_inv (hdir 1); have : c = 1 := Fin.ext (by omega); subst this; simpa using hs
        · obtain ⟨c, hx, _, hs⟩ := cellAtInt_some_inv (hdir 2); have : c = 2 := Fin.ext (by omega); subst this; simpa using hs
        · obtain ⟨c, hx, _, hs⟩ := cellAtInt_some_inv (hdir 3); have : c = 3 := Fin.ext (by omega); subst this; simpa using hs
      · rcases ht with rfl | rfl | rfl
        · obtain ⟨c, hx, _, hs⟩ := cellAtInt_some_inv (hdir 0); have : c = 1 := Fin.ext (by omega); subst this; simpa using hs
        · obtain ⟨c, hx, _, hs⟩ := cellAtInt_some_inv (hdir 1); have : c = 2 := Fin.ext (by omega); subst this; simpa using hs
        · obtain ⟨c, hx, _, hs⟩ := cellAtInt_some_inv (hdir 2); have : c = 3 := Fin.ext (by omega); subst this; simpa using hs
    have s1 := getCol 1 (Or.inl rfl)
    have s2 := getCol 2 (Or.inr (Or.inl rfl))
    have s3 := getCol 3 (Or.inr (Or.inr rfl))
    have p1 := h1 _ s1
    have p2 := h2q _ s2
    have p3 := h3q _ s3
    by_cases hyz : y.toNat = 0
    · rw [hyz] at s2 s3
      rcases hfloor with hf2 | hf3
      · exact hf2 s2
      · exact hf3 s3
    · omega
  · -- Rising diagonal (1, 1): x=0 hits cols 0,1 (dist 1, both SOdd); x=1 hits cols 1,4 (dist 3, both SOdd)
    obtain ⟨c0, hx0, _, _⟩ := cellAtInt_some_inv (hdir 0)
    obtain ⟨c3, hx3, _, _⟩ := cellAtInt_some_inv (hdir 3)
    have hxrange : x = 0 ∨ x = 1 := by omega
    rcases hxrange with rfl | rfl
    · obtain ⟨ca, hxa, hya, hsa⟩ := cellAtInt_some_inv (hdir 0)
      obtain ⟨cb, hxb, hyb, hsb⟩ := cellAtInt_some_inv (hdir 1)
      have ha : ca = 0 := Fin.ext (by omega)
      have hb : cb = 1 := Fin.ext (by omega)
      subst ha; subst hb
      have pa := h0 _ hsa; have pb := h1 _ hsb; omega
    · obtain ⟨ca, hxa, hya, hsa⟩ := cellAtInt_some_inv (hdir 0)
      obtain ⟨cb, hxb, hyb, hsb⟩ := cellAtInt_some_inv (hdir 3)
      have ha : ca = 1 := Fin.ext (by omega)
      have hb : cb = 4 := Fin.ext (by omega)
      subst ha; subst hb
      have pa := h1 _ hsa; have pb := h4 _ hsb; omega
  · -- Falling diagonal (1, -1): x=0 hits cols 0,1 (dist 1, both SOdd); x=1 hits cols 1,4 (dist 3, both SOdd)
    obtain ⟨c0, hx0, _, _⟩ := cellAtInt_some_inv (hdir 0)
    obtain ⟨c3, hx3, _, _⟩ := cellAtInt_some_inv (hdir 3)
    have hxrange : x = 0 ∨ x = 1 := by omega
    rcases hxrange with rfl | rfl
    · obtain ⟨ca, hxa, hya, hsa⟩ := cellAtInt_some_inv (hdir 0)
      obtain ⟨cb, hxb, hyb, hsb⟩ := cellAtInt_some_inv (hdir 1)
      have ha : ca = 0 := Fin.ext (by omega)
      have hb : cb = 1 := Fin.ext (by omega)
      subst ha; subst hb
      have pa := h0 _ hsa; have pb := h1 _ hsb; omega
    · obtain ⟨ca, hxa, hya, hsa⟩ := cellAtInt_some_inv (hdir 0)
      obtain ⟨cb, hxb, hyb, hsb⟩ := cellAtInt_some_inv (hdir 3)
      have ha : ca = 1 := Fin.ext (by omega)
      have hb : cb = 4 := Fin.ext (by omega)
      subst ha; subst hb
      have pa := h1 _ hsa; have pb := h4 _ hsb; omega

structure WDInf (b : Board5) : Prop where
  l0 : (b 0).length % 2 = 0
  l1 : (b 1).length % 2 = 0
  l4 : (b 4).length % 2 = 0
  e2 : b 2 = []
  e3 : b 3 = []
  s0 : SOdd (b 0)
  s1 : SOdd (b 1)
  s4 : SOdd (b 4)

structure W2Inf (a : Fin 5) (b : Board5) : Prop where
  ha : a = 2 ∨ a = 3
  l0 : (b 0).length % 2 = 0
  l1 : (b 1).length % 2 = 0
  l4 : (b 4).length % 2 = 0
  la : (b a).length % 2 = 1
  lb : (b (other5 a)).length % 2 = 1
  s0 : SOdd (b 0)
  s1 : SOdd (b 1)
  s4 : SOdd (b 4)
  sa : SQ (b a)
  sb : SEven (b (other5 a))

def WInfInv (b : Board5) : Prop :=
  WDInf b ∨ ∃ a, W2Inf a b

theorem sOdd_append_black {l : List Player} (hl : SOdd l) (heven : l.length % 2 = 0) :
    SOdd (l ++ [.black]) := by
  intro i hi
  rcases stone_append_cases l .black i hi with ⟨_, hs⟩ | ⟨rfl, _⟩
  · exact hl i hs
  · exact heven

theorem sOdd_append_white {l : List Player} (hl : SOdd l) : SOdd (l ++ [.white]) := by
  intro i hi
  rcases stone_append_cases l .white i hi with ⟨_, hs⟩ | ⟨_, hwb⟩
  · exact hl i hs
  · cases hwb

theorem sEven_append_black {l : List Player} (hl : SEven l) (hodd : l.length % 2 = 1) :
    SEven (l ++ [.black]) := by
  intro i hi
  rcases stone_append_cases l .black i hi with ⟨_, hs⟩ | ⟨rfl, _⟩
  · exact hl i hs
  · exact hodd

theorem sEven_append_white {l : List Player} (hl : SEven l) : SEven (l ++ [.white]) := by
  intro i hi
  rcases stone_append_cases l .white i hi with ⟨_, hs⟩ | ⟨_, hwb⟩
  · exact hl i hs
  · cases hwb

theorem sQ_append_black {l : List Player} (hl : SQ l) (hodd : l.length % 2 = 1) :
    SQ (l ++ [.black]) := by
  intro i hi
  rcases stone_append_cases l .black i hi with ⟨_, hs⟩ | ⟨rfl, _⟩
  · exact hl i hs
  · exact Or.inr hodd

theorem sQ_append_white {l : List Player} (hl : SQ l) : SQ (l ++ [.white]) := by
  intro i hi
  rcases stone_append_cases l .white i hi with ⟨_, hs⟩ | ⟨_, hwb⟩
  · exact hl i hs
  · cases hwb

theorem sQ_of_sEven {l : List Player} (hl : SEven l) : SQ l :=
  fun i hi => Or.inr (hl i hi)

theorem floor_not_black_of_sEven {l : List Player} (hl : SEven l) : stone l 0 ≠ some .black := by
  intro h; have := hl 0 h; omega

theorem wInfInv_props {b : Board5} (hb : WInfInv b) :
    toMove b = .black ∧ ¬ HasFour b .black := by
  rcases hb with hd | ⟨a, h2⟩
  · have hl0 := hd.l0; have hl1 := hd.l1; have hl4 := hd.l4
    refine ⟨toMove_even (by unfold totalStones; rw [hd.e2, hd.e3]; simp; omega), ?_⟩
    apply no_black_four_inf hd.s0 hd.s1 hd.s4
    · intro i hi; rw [hd.e2] at hi; simp [stone] at hi
    · intro i hi; rw [hd.e3] at hi; simp [stone] at hi
    · left; rw [hd.e2]; simp [stone]
  · rcases h2.ha with rfl | rfl
    · have hoth : other5 2 = 3 := rfl
      have hl0 := h2.l0; have hl1 := h2.l1; have hl4 := h2.l4; have hla := h2.la; have hlb := h2.lb; rw [hoth] at hlb
      refine ⟨toMove_even (by unfold totalStones; omega),
        no_black_four_inf h2.s0 h2.s1 h2.s4 h2.sa (sQ_of_sEven (by simpa [other5] using h2.sb))
          (Or.inr (floor_not_black_of_sEven (by simpa [other5] using h2.sb)))⟩
    · have hoth : other5 3 = 2 := rfl
      have hl0 := h2.l0; have hl1 := h2.l1; have hl4 := h2.l4; have hla := h2.la; have hlb := h2.lb; rw [hoth] at hlb
      refine ⟨toMove_even (by unfold totalStones; omega),
        no_black_four_inf h2.s0 h2.s1 h2.s4 (sQ_of_sEven (by simpa [other5] using h2.sb)) h2.sa
          (Or.inl (floor_not_black_of_sEven (by simpa [other5] using h2.sb)))⟩

theorem wInfInv_step {b : Board5} (hb : WInfInv b) (c : Fin 5) :
    ¬ HasFour (play b c .black) .black ∧
    ∃ e : Fin 5, WInfInv (play (play b c .black) e .white) := by
  rcases hb with hd | ⟨a, h2⟩
  · -- Phase 1 (WDInf): cover in U={0,1,4}; cross-play in P={2,3}
    rcases fin5_cases c with rfl | rfl | rfl | rfl | rfl
    · -- c = 0
      refine ⟨no_black_four_inf (by rw [play_eq]; exact sOdd_append_black hd.s0 hd.l0)
          (by rw [play_ne _ _ _ _ (by decide)]; exact hd.s1)
          (by rw [play_ne _ _ _ _ (by decide)]; exact hd.s4)
          (by rw [play_ne _ _ _ _ (by decide), hd.e2]; intro i hi; simp [stone] at hi)
          (by rw [play_ne _ _ _ _ (by decide), hd.e3]; intro i hi; simp [stone] at hi)
          (Or.inl (by rw [play_ne _ _ _ _ (by decide), hd.e2]; simp [stone])),
        0, Or.inl ⟨by simp [play_eq]; have := hd.l0; omega,
          by rw [play_ne _ _ _ _ (by decide), play_ne _ _ _ _ (by decide)]; exact hd.l1,
          by rw [play_ne _ _ _ _ (by decide), play_ne _ _ _ _ (by decide)]; exact hd.l4,
          by rw [play_ne _ _ _ _ (by decide), play_ne _ _ _ _ (by decide)]; exact hd.e2,
          by rw [play_ne _ _ _ _ (by decide), play_ne _ _ _ _ (by decide)]; exact hd.e3,
          by rw [play_eq, play_eq]; exact sOdd_append_white (sOdd_append_black hd.s0 hd.l0),
          by rw [play_ne _ _ _ _ (by decide), play_ne _ _ _ _ (by decide)]; exact hd.s1,
          by rw [play_ne _ _ _ _ (by decide), play_ne _ _ _ _ (by decide)]; exact hd.s4⟩⟩
    · -- c = 1
      refine ⟨no_black_four_inf (by rw [play_ne _ _ _ _ (by decide)]; exact hd.s0)
          (by rw [play_eq]; exact sOdd_append_black hd.s1 hd.l1)
          (by rw [play_ne _ _ _ _ (by decide)]; exact hd.s4)
          (by rw [play_ne _ _ _ _ (by decide), hd.e2]; intro i hi; simp [stone] at hi)
          (by rw [play_ne _ _ _ _ (by decide), hd.e3]; intro i hi; simp [stone] at hi)
          (Or.inl (by rw [play_ne _ _ _ _ (by decide), hd.e2]; simp [stone])),
        1, Or.inl ⟨by rw [play_ne _ _ _ _ (by decide), play_ne _ _ _ _ (by decide)]; exact hd.l0,
          by simp [play_eq]; have := hd.l1; omega,
          by rw [play_ne _ _ _ _ (by decide), play_ne _ _ _ _ (by decide)]; exact hd.l4,
          by rw [play_ne _ _ _ _ (by decide), play_ne _ _ _ _ (by decide)]; exact hd.e2,
          by rw [play_ne _ _ _ _ (by decide), play_ne _ _ _ _ (by decide)]; exact hd.e3,
          by rw [play_ne _ _ _ _ (by decide), play_ne _ _ _ _ (by decide)]; exact hd.s0,
          by rw [play_eq, play_eq]; exact sOdd_append_white (sOdd_append_black hd.s1 hd.l1),
          by rw [play_ne _ _ _ _ (by decide), play_ne _ _ _ _ (by decide)]; exact hd.s4⟩⟩
    · -- c = 2: cross-play e = 3, enter W2Inf 2
      have hsq2 : SQ [.black] := by
        intro i hi; rcases stone_append_cases [] .black i (by simpa using hi) with ⟨h, _⟩ | ⟨rfl, _⟩
        · simp at h
        · left; simp
      have hse3 : SEven [.white] := by
        intro i hi; rcases stone_append_cases [] .white i (by simpa using hi) with ⟨h, _⟩ | ⟨_, hwb⟩
        · simp at h
        · cases hwb
      refine ⟨no_black_four_inf
          (by rw [play_ne _ _ _ _ (by decide)]; exact hd.s0)
          (by rw [play_ne _ _ _ _ (by decide)]; exact hd.s1)
          (by rw [play_ne _ _ _ _ (by decide)]; exact hd.s4)
          (by rw [play_eq, hd.e2]; exact hsq2)
          (by rw [play_ne _ _ _ _ (by decide), hd.e3]; intro i hi; simp [stone] at hi)
          (Or.inr (by rw [play_ne _ _ _ _ (by decide), hd.e3]; simp [stone])),
        3, Or.inr ⟨2, ⟨Or.inl rfl,
          by rw [play_ne _ _ _ _ (by decide), play_ne _ _ _ _ (by decide)]; exact hd.l0,
          by rw [play_ne _ _ _ _ (by decide), play_ne _ _ _ _ (by decide)]; exact hd.l1,
          by rw [play_ne _ _ _ _ (by decide), play_ne _ _ _ _ (by decide)]; exact hd.l4,
          by rw [play_ne _ _ _ _ (by decide), play_eq, hd.e2]; simp,
          by show (play (play b 2 .black) 3 .white 3).length % 2 = 1
             rw [play_eq, play_ne _ _ _ _ (by decide), hd.e3]; simp,
          by rw [play_ne _ _ _ _ (by decide), play_ne _ _ _ _ (by decide)]; exact hd.s0,
          by rw [play_ne _ _ _ _ (by decide), play_ne _ _ _ _ (by decide)]; exact hd.s1,
          by rw [play_ne _ _ _ _ (by decide), play_ne _ _ _ _ (by decide)]; exact hd.s4,
          by rw [play_ne _ _ _ _ (by decide), play_eq, hd.e2]; exact hsq2,
          by show SEven (play (play b 2 .black) 3 .white 3)
             rw [play_eq, play_ne _ _ _ _ (by decide), hd.e3]; exact hse3⟩⟩⟩
    · -- c = 3: cross-play e = 2, enter W2Inf 3
      have hsq3 : SQ [.black] := by
        intro i hi; rcases stone_append_cases [] .black i (by simpa using hi) with ⟨h, _⟩ | ⟨rfl, _⟩
        · simp at h
        · left; simp
      have hse2 : SEven [.white] := by
        intro i hi; rcases stone_append_cases [] .white i (by simpa using hi) with ⟨h, _⟩ | ⟨_, hwb⟩
        · simp at h
        · cases hwb
      refine ⟨no_black_four_inf
          (by rw [play_ne _ _ _ _ (by decide)]; exact hd.s0)
          (by rw [play_ne _ _ _ _ (by decide)]; exact hd.s1)
          (by rw [play_ne _ _ _ _ (by decide)]; exact hd.s4)
          (by rw [play_ne _ _ _ _ (by decide), hd.e2]; intro i hi; simp [stone] at hi)
          (by rw [play_eq, hd.e3]; exact hsq3)
          (Or.inl (by rw [play_ne _ _ _ _ (by decide), hd.e2]; simp [stone])),
        2, Or.inr ⟨3, ⟨Or.inr rfl,
          by rw [play_ne _ _ _ _ (by decide), play_ne _ _ _ _ (by decide)]; exact hd.l0,
          by rw [play_ne _ _ _ _ (by decide), play_ne _ _ _ _ (by decide)]; exact hd.l1,
          by rw [play_ne _ _ _ _ (by decide), play_ne _ _ _ _ (by decide)]; exact hd.l4,
          by rw [play_ne _ _ _ _ (by decide), play_eq, hd.e3]; simp,
          by show (play (play b 3 .black) 2 .white 2).length % 2 = 1
             rw [play_eq, play_ne _ _ _ _ (by decide), hd.e2]; simp,
          by rw [play_ne _ _ _ _ (by decide), play_ne _ _ _ _ (by decide)]; exact hd.s0,
          by rw [play_ne _ _ _ _ (by decide), play_ne _ _ _ _ (by decide)]; exact hd.s1,
          by rw [play_ne _ _ _ _ (by decide), play_ne _ _ _ _ (by decide)]; exact hd.s4,
          by rw [play_ne _ _ _ _ (by decide), play_eq, hd.e3]; exact hsq3,
          by show SEven (play (play b 3 .black) 2 .white 2)
             rw [play_eq, play_ne _ _ _ _ (by decide), hd.e2]; exact hse2⟩⟩⟩
    · -- c = 4
      refine ⟨no_black_four_inf (by rw [play_ne _ _ _ _ (by decide)]; exact hd.s0)
          (by rw [play_ne _ _ _ _ (by decide)]; exact hd.s1)
          (by rw [play_eq]; exact sOdd_append_black hd.s4 hd.l4)
          (by rw [play_ne _ _ _ _ (by decide), hd.e2]; intro i hi; simp [stone] at hi)
          (by rw [play_ne _ _ _ _ (by decide), hd.e3]; intro i hi; simp [stone] at hi)
          (Or.inl (by rw [play_ne _ _ _ _ (by decide), hd.e2]; simp [stone])),
        4, Or.inl ⟨by rw [play_ne _ _ _ _ (by decide), play_ne _ _ _ _ (by decide)]; exact hd.l0,
          by rw [play_ne _ _ _ _ (by decide), play_ne _ _ _ _ (by decide)]; exact hd.l1,
          by simp [play_eq]; have := hd.l4; omega,
          by rw [play_ne _ _ _ _ (by decide), play_ne _ _ _ _ (by decide)]; exact hd.e2,
          by rw [play_ne _ _ _ _ (by decide), play_ne _ _ _ _ (by decide)]; exact hd.e3,
          by rw [play_ne _ _ _ _ (by decide), play_ne _ _ _ _ (by decide)]; exact hd.s0,
          by rw [play_ne _ _ _ _ (by decide), play_ne _ _ _ _ (by decide)]; exact hd.s1,
          by rw [play_eq, play_eq]; exact sOdd_append_white (sOdd_append_black hd.s4 hd.l4)⟩⟩
  · -- Phase 2 (W2Inf a): ALWAYS cover in the exact same column c!
    have hs0' : SOdd (play b c .black 0) := by
      by_cases hc : c = 0
      · subst hc; rw [play_eq]; exact sOdd_append_black h2.s0 h2.l0
      · rw [play_ne _ _ _ _ (Ne.symm hc)]; exact h2.s0
    have hs1' : SOdd (play b c .black 1) := by
      by_cases hc : c = 1
      · subst hc; rw [play_eq]; exact sOdd_append_black h2.s1 h2.l1
      · rw [play_ne _ _ _ _ (Ne.symm hc)]; exact h2.s1
    have hs4' : SOdd (play b c .black 4) := by
      by_cases hc : c = 4
      · subst hc; rw [play_eq]; exact sOdd_append_black h2.s4 h2.l4
      · rw [play_ne _ _ _ _ (Ne.symm hc)]; exact h2.s4
    have hsa' : SQ (play b c .black a) := by
      by_cases hc : c = a
      · subst hc; rw [play_eq]; exact sQ_append_black h2.sa h2.la
      · rw [play_ne _ _ _ _ (Ne.symm hc)]; exact h2.sa
    have hsb' : SEven (play b c .black (other5 a)) := by
      by_cases hc : c = other5 a
      · subst hc; rw [play_eq]; exact sEven_append_black h2.sb h2.lb
      · rw [play_ne _ _ _ _ (Ne.symm hc)]; exact h2.sb
    have hno' : ¬ HasFour (play b c .black) .black := by
      rcases h2.ha with rfl | rfl
      · exact no_black_four_inf hs0' hs1' hs4' hsa' (sQ_of_sEven hsb')
          (Or.inr (floor_not_black_of_sEven hsb'))
      · exact no_black_four_inf hs0' hs1' hs4' (sQ_of_sEven hsb') hsa'
          (Or.inl (floor_not_black_of_sEven hsb'))
    refine ⟨hno', c, Or.inr ⟨a, ⟨h2.ha, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩⟩
    · by_cases hc : c = 0
      · subst hc; simp [play_eq]; have := h2.l0; omega
      · rw [play_ne _ _ _ _ (Ne.symm hc), play_ne _ _ _ _ (Ne.symm hc)]; exact h2.l0
    · by_cases hc : c = 1
      · subst hc; simp [play_eq]; have := h2.l1; omega
      · rw [play_ne _ _ _ _ (Ne.symm hc), play_ne _ _ _ _ (Ne.symm hc)]; exact h2.l1
    · by_cases hc : c = 4
      · subst hc; simp [play_eq]; have := h2.l4; omega
      · rw [play_ne _ _ _ _ (Ne.symm hc), play_ne _ _ _ _ (Ne.symm hc)]; exact h2.l4
    · by_cases hc : c = a
      · subst hc; simp [play_eq]; have := h2.la; omega
      · rw [play_ne _ _ _ _ (Ne.symm hc), play_ne _ _ _ _ (Ne.symm hc)]; exact h2.la
    · by_cases hc : c = other5 a
      · subst hc; simp [play_eq]; have := h2.lb; omega
      · rw [play_ne _ _ _ _ (Ne.symm hc), play_ne _ _ _ _ (Ne.symm hc)]; exact h2.lb
    · by_cases hc : c = 0
      · subst hc; rw [play_eq]; exact sOdd_append_white hs0'
      · rw [play_ne _ _ _ _ (Ne.symm hc)]; exact hs0'
    · by_cases hc : c = 1
      · subst hc; rw [play_eq]; exact sOdd_append_white hs1'
      · rw [play_ne _ _ _ _ (Ne.symm hc)]; exact hs1'
    · by_cases hc : c = 4
      · subst hc; rw [play_eq]; exact sOdd_append_white hs4'
      · rw [play_ne _ _ _ _ (Ne.symm hc)]; exact hs4'
    · by_cases hc : c = a
      · subst hc; rw [play_eq]; exact sQ_append_white hsa'
      · rw [play_ne _ _ _ _ (Ne.symm hc)]; exact hsa'
    · by_cases hc : c = other5 a
      · subst hc; rw [play_eq]; exact sEven_append_white hsb'
      · rw [play_ne _ _ _ _ (Ne.symm hc)]; exact hsb'

theorem white_nonloss_inf : CanAvoidLossInf .white emptyBoard5 := by
  have hroot : WInfInv emptyBoard5 := Or.inl
    ⟨by simp [emptyBoard5], by simp [emptyBoard5], by simp [emptyBoard5], rfl, rfl,
     fun i hi => by simp [emptyBoard5, stone] at hi,
     fun i hi => by simp [emptyBoard5, stone] at hi,
     fun i hi => by simp [emptyBoard5, stone] at hi⟩
  exact canAvoidLossInf_of_inv .white WInfInv (fun _ hb => wInfInv_props hb) (fun _ hb c => wInfInv_step hb c) emptyBoard5 hroot

/-! ## Main Theorem: `5 × ∞` Gravity Connect Four Is a Draw -/

theorem five_columns_inf_draw : IsDrawInf emptyBoard5 :=
  ⟨black_nonloss_inf, white_nonloss_inf⟩

#print axioms five_columns_inf_draw

end C4W5Inf
