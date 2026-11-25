import C4W5.Allis.Geometry

/-!
# Five-column White state machine (W-STEP / W-ENTRY / W-MAIN)

The state-machine body of the White nonloss route (notes/white.md §4.4-4.6,
§5.1; Allis 1988 §2.2 restricted to five columns).  On top of the frozen
geometry core `C4W5.Allis.Geometry` this module proves

  theorem white_nonloss_five : WhiteGoal

White (the second player) answers the fixed special pair {2, 3}:

  * dormant phase `WD`: both special columns are empty; Black's move in an
    ordinary column {0, 1, 4} is capped in the same column (stay dormant),
    Black's first move e in {2, 3} is cross-answered at `other5 e`
    (enter phase 2 with orientation a := e);
  * phase 2 `W2 h a`: `SQ` on a, `SEven` on `other5 a`; Black's move e is
    capped when that stays legal, and when e (necessarily special) is filled
    by Black's move, White switches to the other special column, entering
    phase 3 with f := e;
  * phase 3 `W3 h a f`: f is full and keeps its phase-2 specification, the
    other special column is open (`SOpen` + side conditions); every Black
    move is capped in place.

Only Black-to-move invariants are named; the intermediate White-to-move
positions are handled inline by exhibiting White's reply and applying the
horizon-monotonicity lemma `safeFor_succ_mono`, which keeps the state count
at three (the four-column prototype instead carries `Open2`/`Open3`
White-to-move states; the two formulations are equivalent because
`SafeFor (k+1) → SafeFor k`).

Heights: Black-to-move positions have all ordinary columns even; the two
special columns odd in phase 2; all columns even in `WD` and in phase 3.
Since h is even, a column of even height < h always has room for one more stone,
a column of odd height ≤ h - 1 has room for one more, and the only way capping
fails is that Black's move itself filled a special column.

No `simp`/`unfold` is performed on `FiveColumns.*` definitions.
-/

namespace FiveAllis

open Connect4 (Player opponent)
open Connect4.NarrowBoards

/-! ## Small facts about the special pair -/

theorem other5_ne {a : Fin 5} (ha : a = 2 ∨ a = 3) : other5 a ≠ a := by
  rcases ha with e | e
  · subst e; rw [other5_2]; decide
  · subst e; rw [other5_3]; decide

theorem other5_pair {a : Fin 5} (ha : a = 2 ∨ a = 3) :
    other5 a = 2 ∨ other5 a = 3 := by
  rcases ha with e | e
  · subst e; rw [other5_2]; exact Or.inr rfl
  · subst e; rw [other5_3]; exact Or.inl rfl

theorem other5_invol {a : Fin 5} (ha : a = 2 ∨ a = 3) : other5 (other5 a) = a := by
  rcases ha with e | e
  · subst e; rw [other5_2, other5_3]
  · subst e; rw [other5_3, other5_2]

/-- Two special columns agree or are paired by `other5`. -/
theorem special_cases {c e : Fin 5} (hc : c = 2 ∨ c = 3) (he : e = 2 ∨ e = 3) :
    c = e ∨ c = other5 e := by
  rcases hc with ec | ec
  · rcases he with ee | ee
    · exact Or.inl (ec.trans ee.symm)
    · refine Or.inr ?_
      rw [ec, ee]
      exact other5_3.symm
  · rcases he with ee | ee
    · refine Or.inr ?_
      rw [ec, ee]
      exact other5_2.symm
    · exact Or.inl (ec.trans ee.symm)

theorem ordinary_ne_special {c e : Fin 5} (hc : c.val ≠ 2 ∧ c.val ≠ 3)
    (he : e = 2 ∨ e = 3) : c ≠ e := by
  intro ex
  subst ex
  rcases he with ey | ey
  · subst ey; exact absurd (by decide) hc.1
  · subst ey; exact absurd (by decide) hc.2

theorem empty5_apply (d : Fin 5) :
    Connect4.NarrowBoards.emptyBoard 5 d = ([] : List Player) := rfl

theorem sodd_nil : SOdd ([] : List Player) := by
  intro i hs
  simp [stone] at hs

theorem sEven_nil : SEven ([] : List Player) := by
  intro i hs
  simp [stone] at hs

theorem sq_nil : SQ ([] : List Player) := by
  intro i hs
  simp [stone] at hs

/-! ## Safety is downward closed in the horizon -/

theorem safeFor_succ_mono {w h : Nat} {p : Player} :
    ∀ (k : Nat) (b : Board w), SafeFor h p (k + 1) b → SafeFor h p k b := by
  intro k
  induction k with
  | zero => intro b hs; exact hs.1
  | succ k' ih =>
      intro b hs
      refine ⟨hs.1, ?_⟩
      rcases hs.2 with hw | hf | hm
      · exact Or.inl hw
      · exact Or.inr (Or.inl hf)
      · by_cases htm : Connect4.NarrowBoards.toMove b = p
        · rw [if_pos htm] at hm
          obtain ⟨c, hl, hsafe⟩ := hm
          refine Or.inr (Or.inr ?_)
          rw [if_pos htm]
          exact ⟨c, hl, ih _ hsafe⟩
        · rw [if_neg htm] at hm
          refine Or.inr (Or.inr ?_)
          rw [if_neg htm]
          intro c hl
          exact ih _ (hm c hl)

/-! ## The three Black-to-move invariants -/

/-- Phase-3 column specification, oriented by the entry column `a`: the
filled column `f` keeps `SQ` when f = a and `SEven` when f = other5 a;
the open column is `other5 f`.  Instantiates at `a = 2` to `Spec5_3 f P`
and at `a = 3` to `Spec5_3' f P`. -/
structure Spec3a (a f : Fin 5) (P : Board 5) : Prop where
  aPair : a = 2 ∨ a = 3
  fPair : f = 2 ∨ f = 3
  rOdd : ∀ c : Fin 5, c.val ≠ 2 ∧ c.val ≠ 3 → SOdd (P c)
  keptQ : f = a → SQ (P a)
  keptE : f = other5 a → SEven (P (other5 a))
  openCol : SOpen (P (other5 f))
  bottom : f = a → stone (P (other5 f)) 0 ≠ some Player.black
  nonempty : 1 ≤ (P (other5 f)).length

/-- Dormant phase: the special pair {2, 3} is untouched, Black to move. -/
def WD (h : Nat) (P : Board 5) : Prop :=
  (∀ c : Fin 5, c.val ≠ 2 ∧ c.val ≠ 3 → SOdd (P c)) ∧ Valid h P ∧
    P 2 = [] ∧ P 3 = [] ∧
    (∀ c : Fin 5, (P c).length % 2 = 0) ∧
    Connect4.NarrowBoards.toMove P = Player.black

/-- Phase 2, oriented by Black's first entry `a` into the special pair. -/
def W2 (h : Nat) (a : Fin 5) (P : Board 5) : Prop :=
  (a = 2 ∨ a = 3) ∧ SQ (P a) ∧ SEven (P (other5 a)) ∧
    (∀ c : Fin 5, c.val ≠ 2 ∧ c.val ≠ 3 → SOdd (P c)) ∧ Valid h P ∧
    (P a).length % 2 = 1 ∧ (P (other5 a)).length % 2 = 1 ∧
    (∀ c : Fin 5, c.val ≠ 2 ∧ c.val ≠ 3 → (P c).length % 2 = 0) ∧
    Connect4.NarrowBoards.toMove P = Player.black

/-- Phase 3: the special column `f` is full, `a` records the orientation. -/
def W3 (h : Nat) (a f : Fin 5) (P : Board 5) : Prop :=
  Spec3a a f P ∧ Valid h P ∧ TopNB (P (other5 f)) ∧ (P f).length = h ∧
    (∀ c : Fin 5, (P c).length % 2 = 0) ∧
    Connect4.NarrowBoards.toMove P = Player.black

/-! ## Geometry of each state (instances of the W-GEO core) -/

/-- Dormant geometry: ordinary `SOdd` plus empty special columns. -/
theorem no_four_wd {h : Nat} {P : Board 5}
    (hr : ∀ c : Fin 5, c.val ≠ 2 ∧ c.val ≠ 3 → SOdd (P c))
    (h2 : P 2 = []) (h3 : P 3 = []) : ¬ HasFour h P Player.black := by
  refine no_black_four_5col_phase2 ⟨?_, ?_, hr⟩
  · rw [h2]; exact sq_nil
  · rw [h3]; exact sEven_nil

/-- Phase-2 geometry for either orientation. -/
theorem no_four_w2 {h : Nat} {a : Fin 5} {P : Board 5} (ha : a = 2 ∨ a = 3)
    (hq : SQ (P a)) (he : SEven (P (other5 a)))
    (hr : ∀ c : Fin 5, c.val ≠ 2 ∧ c.val ≠ 3 → SOdd (P c)) :
    ¬ HasFour h P Player.black := by
  rcases ha with e | e
  · subst e
    rw [other5_2] at he
    exact no_black_four_5col_phase2 ⟨hq, he, hr⟩
  · subst e
    rw [other5_3] at he
    exact no_black_four_5col_phase2' ⟨hq, he, hr⟩

/-- Phase-3 geometry for either orientation. -/
theorem no_four_w3 {h : Nat} {a f : Fin 5} {P : Board 5} (hs : Spec3a a f P) :
    ¬ HasFour h P Player.black := by
  rcases hs.aPair with e | e
  · subst e
    have he := hs.keptE
    rw [other5_2] at he
    exact no_black_four_5col_phase3
      ⟨hs.fPair, hs.rOdd, hs.keptQ, he, hs.openCol, hs.bottom, hs.nonempty⟩
  · subst e
    have he := hs.keptE
    rw [other5_3] at he
    exact no_black_four_5col_phase3'
      ⟨hs.fPair, hs.rOdd, hs.keptQ, he, hs.openCol, hs.bottom, hs.nonempty⟩

/-! ## The first Black stone alone never makes a four -/

theorem first_nil {q d : Fin 5} (hd : d ≠ q) :
    Connect4.NarrowBoards.play (Connect4.NarrowBoards.emptyBoard 5) q Player.black d
      = ([] : List Player) := by
  rw [Connect4.NarrowBoards.play_ne _ _ _ _ hd, empty5_apply]

private theorem no_four_first_vert {h : Nat} {q : Fin 5} {x y : Int}
    (hd : HasFourDir h
      (Connect4.NarrowBoards.play (Connect4.NarrowBoards.emptyBoard 5) q Player.black)
      Player.black x y 0 1) : False := by
  have s0 : cellAtInt h
      (Connect4.NarrowBoards.play (Connect4.NarrowBoards.emptyBoard 5) q Player.black)
      x y = some Player.black := by simpa using hd ⟨0, by decide⟩
  have s3 : cellAtInt h
      (Connect4.NarrowBoards.play (Connect4.NarrowBoards.emptyBoard 5) q Player.black)
      x (y + 3) = some Player.black := by simpa using hd ⟨3, by decide⟩
  obtain ⟨-, -, hy0, -, -⟩ := cellAtInt_some s0
  obtain ⟨c3, -, -, -, t3⟩ := cellAtInt_some s3
  have hb := stone_bound _ _ _ t3
  have hl3 :
      ((Connect4.NarrowBoards.play (Connect4.NarrowBoards.emptyBoard 5) q Player.black) c3).length ≤ 1 := by
    by_cases h3 : c3 = q
    · subst h3
      rw [Connect4.NarrowBoards.play_eq]
      simp [Connect4.NarrowBoards.emptyBoard]
    · rw [first_nil h3]
      decide
  have h03 : (3 : Nat) ≤ (y + 3).toNat := by omega
  omega

private theorem no_four_first_dir {h : Nat} {q : Fin 5} {x y dy : Int}
    (hd : HasFourDir h
      (Connect4.NarrowBoards.play (Connect4.NarrowBoards.emptyBoard 5) q Player.black)
      Player.black x y 1 dy) : False := by
  have s0 : cellAtInt h
      (Connect4.NarrowBoards.play (Connect4.NarrowBoards.emptyBoard 5) q Player.black)
      x y = some Player.black := by simpa using hd ⟨0, by decide⟩
  have s1 : cellAtInt h
      (Connect4.NarrowBoards.play (Connect4.NarrowBoards.emptyBoard 5) q Player.black)
      (x + 1) (y + dy) = some Player.black := by
    simpa using hd ⟨1, by decide⟩
  obtain ⟨c0, hx0, -, -, t0⟩ := cellAtInt_some s0
  obtain ⟨c1, hx1, -, -, t1⟩ := cellAtInt_some s1
  have hne : c0 ≠ c1 := by
    intro ex
    rw [ex] at hx0
    omega
  by_cases h0 : c0 = q
  · have h1 : c1 ≠ q := fun ex => hne (ex.trans h0.symm).symm
    rw [first_nil h1] at t1
    simp [stone] at t1
  · rw [first_nil h0] at t0
    simp [stone] at t0

theorem no_four_after_first {h : Nat} (q : Fin 5) :
    ¬ HasFour h
      (Connect4.NarrowBoards.play (Connect4.NarrowBoards.emptyBoard 5) q Player.black)
      Player.black := by
  intro hf
  rcases hf with ⟨x, y, hd⟩ | ⟨x, y, hd⟩ | ⟨x, y, hd⟩ | ⟨x, y, hd⟩
  · exact no_four_first_vert hd
  · exact no_four_first_dir hd
  · exact no_four_first_dir hd
  · exact no_four_first_dir hd

/-! ## W-ENTRY: the two entry points -/

/-- Black's first move in an ordinary column: White caps it, dormant phase. -/
theorem wd_entry (h : Nat) (h2 : 2 ≤ h) (q : Fin 5) (hq2 : q ≠ 2) (hq3 : q ≠ 3) :
    WD h (Connect4.NarrowBoards.play
      (Connect4.NarrowBoards.play (Connect4.NarrowBoards.emptyBoard 5) q Player.black)
      q Player.white) := by
  have h2e : (2 : Fin 5) ≠ q := fun ex => hq2 ex.symm
  have h3e : (3 : Fin 5) ≠ q := fun ex => hq3 ex.symm
  have hlist : (Connect4.NarrowBoards.play
      (Connect4.NarrowBoards.play (Connect4.NarrowBoards.emptyBoard 5) q Player.black)
      q Player.white) q = [Player.black, Player.white] := by
    rw [Connect4.NarrowBoards.play_eq,
      show (Connect4.NarrowBoards.play (Connect4.NarrowBoards.emptyBoard 5) q Player.black) q
        = [Player.black] from Connect4.NarrowBoards.play_eq _ _ _]
    rfl
  have hnil : ∀ d : Fin 5, d ≠ q → (Connect4.NarrowBoards.play
      (Connect4.NarrowBoards.play (Connect4.NarrowBoards.emptyBoard 5) q Player.black)
      q Player.white) d = ([] : List Player) := by
    intro d hd
    rw [Connect4.NarrowBoards.play_ne _ q d Player.white hd,
      Connect4.NarrowBoards.play_ne _ q d Player.black hd, empty5_apply d]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc i hst
    by_cases hcq : c = q
    · subst hcq
      rw [hlist] at hst
      cases i with
      | zero => rfl
      | succ i =>
          cases i with
          | zero => simp [stone] at hst
          | succ i => simp [stone] at hst
    · rw [hnil c hcq] at hst
      simp [stone] at hst
  · intro d
    by_cases hdq : d = q
    · subst hdq
      rw [hlist]
      show (2 : Nat) ≤ h
      omega
    · rw [hnil d hdq]
      show (0 : Nat) ≤ h
      omega
  · rw [Connect4.NarrowBoards.play_ne _ q 2 Player.white h2e,
      Connect4.NarrowBoards.play_ne _ q 2 Player.black h2e, empty5_apply 2]
  · rw [Connect4.NarrowBoards.play_ne _ q 3 Player.white h3e,
      Connect4.NarrowBoards.play_ne _ q 3 Player.black h3e, empty5_apply 3]
  · intro c
    by_cases hcq : c = q
    · subst hcq
      rw [hlist]
      decide
    · rw [hnil c hcq]
      decide
  · rw [Connect4.NarrowBoards.toMove_play, Connect4.NarrowBoards.toMove_play,
      FiveAllis.toMove_empty]
    rfl

/-- Black's first move in a special column: White cross-answers, phase 2. -/
theorem w2_entry (h : Nat) (h2 : 2 ≤ h) (q : Fin 5) (hq : q = 2 ∨ q = 3) :
    W2 h q (Connect4.NarrowBoards.play
      (Connect4.NarrowBoards.play (Connect4.NarrowBoards.emptyBoard 5) q Player.black)
      (other5 q) Player.white) := by
  have hqo : q ≠ other5 q := fun ex => other5_ne hq ex.symm
  have hqcol : (Connect4.NarrowBoards.play
      (Connect4.NarrowBoards.play (Connect4.NarrowBoards.emptyBoard 5) q Player.black)
      (other5 q) Player.white) q = [Player.black] := by
    rw [Connect4.NarrowBoards.play_ne _ (other5 q) q Player.white hqo]
    exact Connect4.NarrowBoards.play_eq _ _ _
  have hocol : (Connect4.NarrowBoards.play
      (Connect4.NarrowBoards.play (Connect4.NarrowBoards.emptyBoard 5) q Player.black)
      (other5 q) Player.white) (other5 q) = [Player.white] := by
    rw [Connect4.NarrowBoards.play_eq,
      Connect4.NarrowBoards.play_ne _ q (other5 q) Player.black (other5_ne hq),
      empty5_apply (other5 q)]
    exact List.nil_append _
  have hncol : ∀ d : Fin 5, d ≠ q → d ≠ other5 q → (Connect4.NarrowBoards.play
      (Connect4.NarrowBoards.play (Connect4.NarrowBoards.emptyBoard 5) q Player.black)
      (other5 q) Player.white) d = ([] : List Player) := by
    intro d h1 h2'
    rw [Connect4.NarrowBoards.play_ne _ (other5 q) d Player.white h2',
      Connect4.NarrowBoards.play_ne _ q d Player.black h1, empty5_apply d]
  refine ⟨hq, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hqcol]
    intro i hst
    cases i with
    | zero => exact Or.inl (by omega)
    | succ i => simp [stone] at hst
  · rw [hocol]
    intro i hst
    cases i with
    | zero => simp [stone] at hst
    | succ i => simp [stone] at hst
  · intro c hc
    rw [hncol c (ordinary_ne_special hc hq) (ordinary_ne_special hc (other5_pair hq))]
    exact sodd_nil
  · intro d
    by_cases hdq : d = q
    · subst hdq
      rw [hqcol]
      show (1 : Nat) ≤ h
      omega
    · by_cases hdo : d = other5 q
      · subst hdo
        rw [hocol]
        show (1 : Nat) ≤ h
        omega
      · rw [hncol d hdq hdo]
        show (0 : Nat) ≤ h
        omega
  · rw [hqcol]
    decide
  · rw [hocol]
    decide
  · intro c hc
    rw [hncol c (ordinary_ne_special hc hq) (ordinary_ne_special hc (other5_pair hq))]
    decide
  · rw [Connect4.NarrowBoards.toMove_play, Connect4.NarrowBoards.toMove_play,
      FiveAllis.toMove_empty]
    rfl

/-! ## W-STEP: the dormant transition -/

/-- Black to move in the dormant phase.  Every legal Black move `e` is met:
`e` ordinary is capped in place (stay dormant), `e` special is cross-answered
at `other5 e` (enter phase 2 with orientation `e`). -/
private theorem wd_branch (h : Nat) (hh : h % 2 = 0) (h2 : 2 ≤ h) (P : Board 5)
    (hs : WD h P) (k : Nat)
    (A : ∀ Q : Board 5, WD h Q → SafeFor h .white k Q)
    (B : ∀ (a : Fin 5) (Q : Board 5), W2 h a Q → SafeFor h .white k Q) :
    SafeFor h .white (k + 1) P := by
  have hheight := hs.2.2.2.2.1
  refine ⟨no_four_wd hs.1 hs.2.2.1 hs.2.2.2.1, Or.inr (Or.inr ?_)⟩
  have htm : Connect4.NarrowBoards.toMove P ≠ Player.white := by
    rw [hs.2.2.2.2.2]
    decide
  rw [if_neg htm, hs.2.2.2.2.2]
  intro e he
  have hgeom : ¬ HasFour h (Connect4.NarrowBoards.play P e Player.black) Player.black := by
    by_cases hspec : e = 2 ∨ e = 3
    · have hPe : P e = [] := by
        rcases hspec with ex | ex
        · subst ex; exact hs.2.2.1
        · subst ex; exact hs.2.2.2.1
      have hPo : P (other5 e) = [] := by
        rcases hspec with ex | ex
        · subst ex; rw [other5_2]; exact hs.2.2.2.1
        · subst ex; rw [other5_3]; exact hs.2.2.1
      refine no_four_w2 hspec ?_ ?_ ?_
      · rw [Connect4.NarrowBoards.play_eq, hPe]
        intro i hst
        cases i with
        | zero => exact Or.inl (by omega)
        | succ i => simp [stone] at hst
      · rw [Connect4.NarrowBoards.play_ne P e (other5 e) Player.black (other5_ne hspec),
          hPo]
        exact sEven_nil
      · intro c hc
        rw [Connect4.NarrowBoards.play_ne P e c Player.black
          (ordinary_ne_special hc hspec)]
        exact hs.1 c hc
    · have hord : e.val ≠ 2 ∧ e.val ≠ 3 := by
        constructor
        · intro v; exact hspec (Or.inl (Fin.ext v))
        · intro v; exact hspec (Or.inr (Fin.ext v))
      refine no_four_wd ?_ ?_ ?_
      · intro c hc
        by_cases hce : c = e
        · rw [hce, Connect4.NarrowBoards.play_eq]
          exact sOdd_append_black (hs.1 e hord) (hheight e)
        · rw [Connect4.NarrowBoards.play_ne P e c Player.black hce]
          exact hs.1 c hc
      · rw [Connect4.NarrowBoards.play_ne P e 2 Player.black
          (fun ex => hspec (Or.inl ex.symm))]
        exact hs.2.2.1
      · rw [Connect4.NarrowBoards.play_ne P e 3 Player.black
          (fun ex => hspec (Or.inr ex.symm))]
        exact hs.2.2.2.1
  cases k with
  | zero => exact hgeom
  | succ k' =>
      have htw : Connect4.NarrowBoards.toMove
          (Connect4.NarrowBoards.play P e Player.black) = Player.white := by
        rw [Connect4.NarrowBoards.toMove_play, hs.2.2.2.2.2]
        rfl
      refine ⟨hgeom, Or.inr (Or.inr ?_)⟩
      rw [if_pos htw, htw]
      by_cases hspec : e = 2 ∨ e = 3
      · have hPe : P e = [] := by
          rcases hspec with ex | ex
          · subst ex; exact hs.2.2.1
          · subst ex; exact hs.2.2.2.1
        have hPo : P (other5 e) = [] := by
          rcases hspec with ex | ex
          · subst ex; rw [other5_2]; exact hs.2.2.2.1
          · subst ex; rw [other5_3]; exact hs.2.2.1
        have heo : e ≠ other5 e := fun ex => other5_ne hspec ex.symm
        have hcross : Legal h (Connect4.NarrowBoards.play P e Player.black) (other5 e) := by
          unfold Connect4.NarrowBoards.Legal
          rw [Connect4.NarrowBoards.play_ne P e (other5 e) Player.black
            (other5_ne hspec), hPo]
          show (0 : Nat) < h
          omega
        refine ⟨other5 e, hcross, safeFor_succ_mono k' _
          (B e _ ⟨hspec, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)⟩
        · rw [Connect4.NarrowBoards.play_ne _ (other5 e) e Player.white heo,
            Connect4.NarrowBoards.play_eq, hPe]
          intro i hst
          cases i with
          | zero => exact Or.inl (by omega)
          | succ i => simp [stone] at hst
        · rw [Connect4.NarrowBoards.play_eq,
            Connect4.NarrowBoards.play_ne P e (other5 e) Player.black
              (other5_ne hspec), hPo]
          intro i hst
          cases i with
          | zero => simp [stone] at hst
          | succ i => simp [stone] at hst
        · intro c hc
          rw [Connect4.NarrowBoards.play_ne _ (other5 e) c Player.white
              (ordinary_ne_special hc (other5_pair hspec)),
            Connect4.NarrowBoards.play_ne P e c Player.black
              (ordinary_ne_special hc hspec)]
          exact hs.1 c hc
        · exact play_valid (play_valid hs.2.1 he) hcross
        · rw [Connect4.NarrowBoards.play_ne _ (other5 e) e Player.white heo,
            Connect4.NarrowBoards.play_eq, hPe]
          decide
        · rw [Connect4.NarrowBoards.play_eq,
            Connect4.NarrowBoards.play_ne P e (other5 e) Player.black
              (other5_ne hspec), hPo]
          decide
        · intro c hc
          rw [Connect4.NarrowBoards.play_ne _ (other5 e) c Player.white
              (ordinary_ne_special hc (other5_pair hspec)),
            Connect4.NarrowBoards.play_ne P e c Player.black
              (ordinary_ne_special hc hspec)]
          exact hheight c
        · rw [Connect4.NarrowBoards.toMove_play, Connect4.NarrowBoards.toMove_play,
            hs.2.2.2.2.2]
          rfl
      · have hord : e.val ≠ 2 ∧ e.val ≠ 3 := by
          constructor
          · intro v; exact hspec (Or.inl (Fin.ext v))
          · intro v; exact hspec (Or.inr (Fin.ext v))
        have hcap : Legal h (Connect4.NarrowBoards.play P e Player.black) e := by
          unfold Connect4.NarrowBoards.Legal
          rw [Connect4.NarrowBoards.play_eq]
          simp only [List.length_append, List.length_singleton]
          have hep : (P e).length < h := he
          have := hheight e
          omega
        refine ⟨e, hcap, safeFor_succ_mono k' _ (A _ ⟨?_, ?_, ?_, ?_, ?_, ?_⟩)⟩
        · intro c hc
          by_cases hce : c = e
          · rw [hce, Connect4.NarrowBoards.play_eq, Connect4.NarrowBoards.play_eq]
            exact sOdd_append_white (sOdd_append_black (hs.1 e hord) (hheight e))
          · rw [Connect4.NarrowBoards.play_ne _ e c Player.white hce,
              Connect4.NarrowBoards.play_ne P e c Player.black hce]
            exact hs.1 c hc
        · exact play_valid (play_valid hs.2.1 he) hcap
        · rw [Connect4.NarrowBoards.play_ne _ e 2 Player.white
              (fun ex => hspec (Or.inl ex.symm)),
            Connect4.NarrowBoards.play_ne P e 2 Player.black
              (fun ex => hspec (Or.inl ex.symm))]
          exact hs.2.2.1
        · rw [Connect4.NarrowBoards.play_ne _ e 3 Player.white
              (fun ex => hspec (Or.inr ex.symm)),
            Connect4.NarrowBoards.play_ne P e 3 Player.black
              (fun ex => hspec (Or.inr ex.symm))]
          exact hs.2.2.2.1
        · intro c
          by_cases hce : c = e
          · rw [hce, Connect4.NarrowBoards.play_eq, Connect4.NarrowBoards.play_eq]
            simp only [List.length_append, List.length_singleton]
            have := hheight e
            omega
          · rw [Connect4.NarrowBoards.play_ne _ e c Player.white hce,
              Connect4.NarrowBoards.play_ne P e c Player.black hce]
            exact hheight c
        · rw [Connect4.NarrowBoards.toMove_play, Connect4.NarrowBoards.toMove_play,
            hs.2.2.2.2.2]
          rfl

/-! ## W-STEP: the phase-2 transition -/

/-- Black to move in phase 2.  Every legal Black move `e` is capped when that
is legal; otherwise `e` (necessarily a full special column) makes White switch
to the other special column, entering phase 3 with f := e. -/
private theorem w2_branch (h : Nat) (hh : h % 2 = 0) (a : Fin 5) (P : Board 5)
    (hs : W2 h a P) (k : Nat)
    (B : ∀ (a : Fin 5) (Q : Board 5), W2 h a Q → SafeFor h .white k Q)
    (D : ∀ (a f : Fin 5) (Q : Board 5), W3 h a f Q → SafeFor h .white k Q) :
    SafeFor h .white (k + 1) P := by
  have hspecodd : ∀ d : Fin 5, d = 2 ∨ d = 3 → (P d).length % 2 = 1 := by
    intro d hd
    rcases hs.1 with ea | ea
    · subst ea
      have ho := hs.2.2.2.2.2.2.1
      rw [other5_2] at ho
      rcases hd with ex | ex
      · subst ex; exact hs.2.2.2.2.2.1
      · subst ex; exact ho
    · subst ea
      have ho := hs.2.2.2.2.2.2.1
      rw [other5_3] at ho
      rcases hd with ex | ex
      · subst ex; exact ho
      · subst ex; exact hs.2.2.2.2.2.1
  refine ⟨no_four_w2 hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1, Or.inr (Or.inr ?_)⟩
  have htm : Connect4.NarrowBoards.toMove P ≠ Player.white := by
    rw [hs.2.2.2.2.2.2.2.2]
    decide
  rw [if_neg htm, hs.2.2.2.2.2.2.2.2]
  intro e he
  have hep : (P e).length < h := he
  have hvQ : Valid h (Connect4.NarrowBoards.play P e Player.black) :=
    play_valid hs.2.2.2.2.1 he
  have hgeom : ¬ HasFour h (Connect4.NarrowBoards.play P e Player.black) Player.black := by
    refine no_four_w2 hs.1 ?_ ?_ ?_
    · by_cases hea : a = e
      · have hsq : SQ (P e) := by rw [← hea]; exact hs.2.1
        have hpe : (P e).length % 2 = 1 := by rw [← hea]; exact hs.2.2.2.2.2.1
        rw [hea, Connect4.NarrowBoards.play_eq]
        exact sQ_append_black hsq hpe
      · rw [Connect4.NarrowBoards.play_ne P e a Player.black hea]
        exact hs.2.1
    · by_cases heo : other5 a = e
      · rw [← heo, Connect4.NarrowBoards.play_eq]
        exact sEven_append_black hs.2.2.1 hs.2.2.2.2.2.2.1
      · rw [Connect4.NarrowBoards.play_ne P e (other5 a) Player.black heo]
        exact hs.2.2.1
    · intro c hc
      by_cases hce : c = e
      · have hc' : e.val ≠ 2 ∧ e.val ≠ 3 := by rw [← hce]; exact hc
        rw [hce, Connect4.NarrowBoards.play_eq]
        exact sOdd_append_black (hs.2.2.2.1 e hc') (hs.2.2.2.2.2.2.2.1 e hc')
      · rw [Connect4.NarrowBoards.play_ne P e c Player.black hce]
        exact hs.2.2.2.1 c hc
  cases k with
  | zero => exact hgeom
  | succ k' =>
      have htw : Connect4.NarrowBoards.toMove
          (Connect4.NarrowBoards.play P e Player.black) = Player.white := by
        rw [Connect4.NarrowBoards.toMove_play, hs.2.2.2.2.2.2.2.2]
        rfl
      refine ⟨hgeom, Or.inr (Or.inr ?_)⟩
      rw [if_pos htw, htw]
      by_cases hcap : Legal h (Connect4.NarrowBoards.play P e Player.black) e
      · refine ⟨e, hcap, safeFor_succ_mono k' _
          (B a _ ⟨hs.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)⟩
        · by_cases hea : a = e
          · have hsq : SQ (P e) := by rw [← hea]; exact hs.2.1
            have hpe : (P e).length % 2 = 1 := by rw [← hea]; exact hs.2.2.2.2.2.1
            rw [hea, Connect4.NarrowBoards.play_eq, Connect4.NarrowBoards.play_eq]
            exact sQ_append_white (sQ_append_black hsq hpe)
          · rw [Connect4.NarrowBoards.play_ne _ e a Player.white hea,
              Connect4.NarrowBoards.play_ne P e a Player.black hea]
            exact hs.2.1
        · by_cases heo : other5 a = e
          · rw [← heo, Connect4.NarrowBoards.play_eq, Connect4.NarrowBoards.play_eq]
            exact sEven_append_white (sEven_append_black hs.2.2.1 hs.2.2.2.2.2.2.1)
          · rw [Connect4.NarrowBoards.play_ne _ e (other5 a) Player.white heo,
              Connect4.NarrowBoards.play_ne P e (other5 a) Player.black heo]
            exact hs.2.2.1
        · intro c hc
          by_cases hce : c = e
          · have hc' : e.val ≠ 2 ∧ e.val ≠ 3 := by rw [← hce]; exact hc
            rw [hce, Connect4.NarrowBoards.play_eq, Connect4.NarrowBoards.play_eq]
            exact sOdd_append_white
              (sOdd_append_black (hs.2.2.2.1 e hc') (hs.2.2.2.2.2.2.2.1 e hc'))
          · rw [Connect4.NarrowBoards.play_ne _ e c Player.white hce,
              Connect4.NarrowBoards.play_ne P e c Player.black hce]
            exact hs.2.2.2.1 c hc
        · exact play_valid hvQ hcap
        · by_cases hea : a = e
          · have hpe : (P e).length % 2 = 1 := by rw [← hea]; exact hs.2.2.2.2.2.1
            rw [hea, Connect4.NarrowBoards.play_eq, Connect4.NarrowBoards.play_eq]
            simp only [List.length_append, List.length_singleton]
            omega
          · rw [Connect4.NarrowBoards.play_ne _ e a Player.white hea,
              Connect4.NarrowBoards.play_ne P e a Player.black hea]
            exact hs.2.2.2.2.2.1
        · by_cases heo : other5 a = e
          · rw [← heo, Connect4.NarrowBoards.play_eq, Connect4.NarrowBoards.play_eq]
            simp only [List.length_append, List.length_singleton]
            have := hs.2.2.2.2.2.2.1
            omega
          · rw [Connect4.NarrowBoards.play_ne _ e (other5 a) Player.white heo,
              Connect4.NarrowBoards.play_ne P e (other5 a) Player.black heo]
            exact hs.2.2.2.2.2.2.1
        · intro c hc
          by_cases hce : c = e
          · have hc' : e.val ≠ 2 ∧ e.val ≠ 3 := by rw [← hce]; exact hc
            rw [hce, Connect4.NarrowBoards.play_eq, Connect4.NarrowBoards.play_eq]
            simp only [List.length_append, List.length_singleton]
            have := hs.2.2.2.2.2.2.2.1 e hc'
            omega
          · rw [Connect4.NarrowBoards.play_ne _ e c Player.white hce,
              Connect4.NarrowBoards.play_ne P e c Player.black hce]
            exact hs.2.2.2.2.2.2.2.1 c hc
        · rw [Connect4.NarrowBoards.toMove_play, Connect4.NarrowBoards.toMove_play,
            hs.2.2.2.2.2.2.2.2]
          rfl
      · have hqe : ((Connect4.NarrowBoards.play P e Player.black) e).length
            = (P e).length + 1 := by
          rw [Connect4.NarrowBoards.play_eq]
          simp only [List.length_append, List.length_singleton]
        have hfull : (P e).length + 1 = h := by
          have hv := hvQ e
          have hn : ¬ (((Connect4.NarrowBoards.play P e Player.black) e).length < h) := by
            unfold Connect4.NarrowBoards.Legal at hcap
            exact hcap
          rw [hqe] at hv hn
          omega
        have hespec : e = 2 ∨ e = 3 := by
          by_contra hns
          have hord : e.val ≠ 2 ∧ e.val ≠ 3 := by
            constructor
            · intro v; exact hns (Or.inl (Fin.ext v))
            · intro v; exact hns (Or.inr (Fin.ext v))
          have := hs.2.2.2.2.2.2.2.1 e hord
          omega
        have hcross : Legal h (Connect4.NarrowBoards.play P e Player.black) (other5 e) := by
          unfold Connect4.NarrowBoards.Legal
          rw [Connect4.NarrowBoards.play_ne P e (other5 e) Player.black
            (other5_ne hespec)]
          have hv := hs.2.2.2.2.1 (other5 e)
          have hp := hspecodd (other5 e) (other5_pair hespec)
          omega
        refine ⟨other5 e, hcross, safeFor_succ_mono k' _
          (D a e _ ⟨⟨hs.1, hespec, ?_, ?_, ?_, ?_, ?_, ?_⟩,
            play_valid hvQ hcross, ?_, ?_, ?_, ?_⟩)⟩
        · intro c hc
          rw [Connect4.NarrowBoards.play_ne _ (other5 e) c Player.white
              (ordinary_ne_special hc (other5_pair hespec)),
            Connect4.NarrowBoards.play_ne P e c Player.black
              (ordinary_ne_special hc hespec)]
          exact hs.2.2.2.1 c hc
        · intro hfa
          subst hfa
          rw [Connect4.NarrowBoards.play_ne _ (other5 e) e Player.white
              (fun ex => other5_ne hespec ex.symm), Connect4.NarrowBoards.play_eq]
          exact sQ_append_black hs.2.1 hs.2.2.2.2.2.1
        · intro hfe
          have hno : other5 a ≠ other5 e := by
            intro ex
            rw [hfe, other5_invol hs.1] at ex
            exact other5_ne hs.1 ex
          have hse : SEven (P e) := by rw [hfe]; exact hs.2.2.1
          have hpe : (P e).length % 2 = 1 := by rw [hfe]; exact hs.2.2.2.2.2.2.1
          rw [Connect4.NarrowBoards.play_ne _ (other5 e) (other5 a) Player.white hno,
              ← hfe, Connect4.NarrowBoards.play_eq]
          exact sEven_append_black hse hpe
        · rw [Connect4.NarrowBoards.play_eq,
            Connect4.NarrowBoards.play_ne P e (other5 e) Player.black
              (other5_ne hespec)]
          refine sOpen_append_white ?_
          by_cases hea : e = a
          · subst hea
            exact sEven_sOpen hs.2.2.1
          · have heother : e = other5 a := by
              rcases hespec with ey | ey
              · rcases hs.1 with ea | ea
                · subst ey; subst ea; exact absurd rfl hea
                · subst ey; subst ea; exact other5_3.symm
              · rcases hs.1 with ea | ea
                · subst ey; subst ea; exact other5_2.symm
                · subst ey; subst ea; exact absurd rfl hea
            rw [heother, other5_invol hs.1]
            exact sQ_sOpen hs.2.1
        · intro hfa
          have hse : SEven (P (other5 e)) := by rw [hfa]; exact hs.2.2.1
          intro hst
          rw [Connect4.NarrowBoards.play_eq,
            Connect4.NarrowBoards.play_ne P e (other5 e) Player.black
              (other5_ne hespec), stone_append] at hst
          by_cases hlen : (0 : Nat) < (P (other5 e)).length
          · rw [if_pos hlen] at hst
            have := hse 0 hst
            omega
          · rw [if_neg hlen] at hst
            by_cases hze : (0 : Nat) = (P (other5 e)).length
            · rw [if_pos hze] at hst
              exact absurd hst (by decide)
            · rw [if_neg hze] at hst
              exact absurd hst (by decide)
        · rw [Connect4.NarrowBoards.play_eq,
            Connect4.NarrowBoards.play_ne P e (other5 e) Player.black
              (other5_ne hespec)]
          simp only [List.length_append, List.length_singleton]
          omega
        · rw [Connect4.NarrowBoards.play_eq,
            Connect4.NarrowBoards.play_ne P e (other5 e) Player.black
              (other5_ne hespec)]
          exact topNB_append_white _
        · rw [Connect4.NarrowBoards.play_ne _ (other5 e) e Player.white
              (fun ex => other5_ne hespec ex.symm), Connect4.NarrowBoards.play_eq]
          simp only [List.length_append, List.length_singleton]
          omega
        · intro c
          by_cases hco : c = other5 e
          · rw [hco, Connect4.NarrowBoards.play_eq,
              Connect4.NarrowBoards.play_ne P e (other5 e) Player.black
                (other5_ne hespec)]
            simp only [List.length_append, List.length_singleton]
            have := hspecodd (other5 e) (other5_pair hespec)
            omega
          · by_cases hce : c = e
            · rw [hce, Connect4.NarrowBoards.play_ne _ (other5 e) e Player.white
                (fun ex => other5_ne hespec ex.symm), Connect4.NarrowBoards.play_eq]
              simp only [List.length_append, List.length_singleton]
              omega
            · have hcord : c.val ≠ 2 ∧ c.val ≠ 3 := by
                have hcsp : c = 2 ∨ c = 3 → False := by
                  intro hcs
                  rcases special_cases hcs hespec with ex | ex
                  · exact hce ex
                  · exact hco ex
                constructor
                · intro v; exact hcsp (Or.inl (Fin.ext v))
                · intro v; exact hcsp (Or.inr (Fin.ext v))
              rw [Connect4.NarrowBoards.play_ne _ (other5 e) c Player.white hco,
                  Connect4.NarrowBoards.play_ne P e c Player.black hce]
              exact hs.2.2.2.2.2.2.2.1 c hcord
        · rw [Connect4.NarrowBoards.toMove_play, Connect4.NarrowBoards.toMove_play,
            hs.2.2.2.2.2.2.2.2]
          rfl

/-! ## W-STEP: the phase-3 transition -/

/-- Black to move in phase 3.  Black cannot replay the full column `f`; every
legal Black move `e` is capped in place, staying in phase 3. -/
private theorem w3_branch (h : Nat) (hh : h % 2 = 0) (a f : Fin 5) (P : Board 5)
    (hs : W3 h a f P) (k : Nat)
    (D : ∀ (a f : Fin 5) (Q : Board 5), W3 h a f Q → SafeFor h .white k Q) :
    SafeFor h .white (k + 1) P := by
  refine ⟨no_four_w3 hs.1, Or.inr (Or.inr ?_)⟩
  have htm : Connect4.NarrowBoards.toMove P ≠ Player.white := by
    rw [hs.2.2.2.2.2]
    decide
  rw [if_neg htm, hs.2.2.2.2.2]
  intro e he
  have hep : (P e).length < h := he
  have hnef : e ≠ f := by
    intro ex
    rw [ex] at hep
    rw [hs.2.2.2.1] at hep
    omega
  have hvQ : Valid h (Connect4.NarrowBoards.play P e Player.black) :=
    play_valid hs.2.1 he
  have hspecQ : Spec3a a f (Connect4.NarrowBoards.play P e Player.black) := by
    refine ⟨hs.1.aPair, hs.1.fPair, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro c hc
      by_cases hce : c = e
      · have hc' : e.val ≠ 2 ∧ e.val ≠ 3 := by rw [← hce]; exact hc
        rw [hce, Connect4.NarrowBoards.play_eq]
        exact sOdd_append_black (hs.1.rOdd e hc') (hs.2.2.2.2.1 e)
      · rw [Connect4.NarrowBoards.play_ne P e c Player.black hce]
        exact hs.1.rOdd c hc
    · intro hfa
      subst hfa
      rw [Connect4.NarrowBoards.play_ne P e f Player.black (fun ex => hnef ex.symm)]
      exact hs.1.keptQ rfl
    · intro hfe
      have hnoa : other5 a ≠ e := by rw [← hfe]; exact fun ex => hnef ex.symm
      rw [Connect4.NarrowBoards.play_ne P e (other5 a) Player.black hnoa]
      exact hs.1.keptE hfe
    · by_cases heo : e = other5 f
      · rw [heo, Connect4.NarrowBoards.play_eq]
        exact sOpen_append_black hs.1.openCol hs.2.2.1
      · rw [Connect4.NarrowBoards.play_ne P e (other5 f) Player.black
          (fun ex => heo ex.symm)]
        exact hs.1.openCol
    · intro hfa
      by_cases heo : e = other5 f
      · rw [heo, Connect4.NarrowBoards.play_eq]
        intro hst
        rw [stone_append, if_pos (by have := hs.1.nonempty; omega :
          (0 : Nat) < (P (other5 f)).length)] at hst
        exact hs.1.bottom hfa hst
      · rw [Connect4.NarrowBoards.play_ne P e (other5 f) Player.black
          (fun ex => heo ex.symm)]
        exact hs.1.bottom hfa
    · by_cases heo : e = other5 f
      · rw [heo, Connect4.NarrowBoards.play_eq]
        simp only [List.length_append, List.length_singleton]
        omega
      · rw [Connect4.NarrowBoards.play_ne P e (other5 f) Player.black
          (fun ex => heo ex.symm)]
        exact hs.1.nonempty
  have hgeom : ¬ HasFour h (Connect4.NarrowBoards.play P e Player.black) Player.black :=
    no_four_w3 hspecQ
  cases k with
  | zero => exact hgeom
  | succ k' =>
      have htw : Connect4.NarrowBoards.toMove
          (Connect4.NarrowBoards.play P e Player.black) = Player.white := by
        rw [Connect4.NarrowBoards.toMove_play, hs.2.2.2.2.2]
        rfl
      refine ⟨hgeom, Or.inr (Or.inr ?_)⟩
      rw [if_pos htw, htw]
      have hcap : Legal h (Connect4.NarrowBoards.play P e Player.black) e := by
        unfold Connect4.NarrowBoards.Legal
        rw [Connect4.NarrowBoards.play_eq]
        simp only [List.length_append, List.length_singleton]
        have hv := hs.2.1 e
        have hp := hs.2.2.2.2.1 e
        omega
      have hXo : ∀ d : Fin 5, d = e →
          (Connect4.NarrowBoards.play (Connect4.NarrowBoards.play P e Player.black)
            e Player.white) d
            = (Connect4.NarrowBoards.play P e Player.black) d ++ [Player.white] := by
        intro d hde
        rw [hde, Connect4.NarrowBoards.play_eq]
      refine ⟨e, hcap, safeFor_succ_mono k' _
        (D a f _ ⟨⟨hs.1.aPair, hs.1.fPair, ?_, ?_, ?_, ?_, ?_, ?_⟩,
          play_valid hvQ hcap, ?_, ?_, ?_, ?_⟩)⟩
      · intro c hc
        by_cases hce : c = e
        · have hc' : e.val ≠ 2 ∧ e.val ≠ 3 := by rw [← hce]; exact hc
          rw [hce, hXo e rfl, Connect4.NarrowBoards.play_eq]
          exact sOdd_append_white (sOdd_append_black (hs.1.rOdd e hc')
            (hs.2.2.2.2.1 e))
        · rw [Connect4.NarrowBoards.play_ne _ e c Player.white hce]
          exact hspecQ.rOdd c hc
      · intro hfa
        subst hfa
        rw [Connect4.NarrowBoards.play_ne _ e f Player.white (fun ex => hnef ex.symm),
            Connect4.NarrowBoards.play_ne _ e f Player.black (fun ex => hnef ex.symm)]
        exact hs.1.keptQ rfl
      · intro hfe
        rw [Connect4.NarrowBoards.play_ne _ e (other5 a) Player.white
            (by rw [← hfe]; exact fun ex => hnef ex.symm),
            Connect4.NarrowBoards.play_ne _ e (other5 a) Player.black
              (by rw [← hfe]; exact fun ex => hnef ex.symm)]
        exact hs.1.keptE hfe
      · by_cases heo : e = other5 f
        · rw [hXo (other5 f) heo.symm]
          exact sOpen_append_white hspecQ.openCol
        · rw [Connect4.NarrowBoards.play_ne _ e (other5 f) Player.white
            (fun ex => heo ex.symm)]
          exact hspecQ.openCol
      · intro hfa
        by_cases heo : e = other5 f
        · intro hst
          rw [hXo (other5 f) heo.symm, stone_append,
            if_pos (by have := hspecQ.nonempty; omega :
              (0 : Nat) < ((Connect4.NarrowBoards.play P e Player.black)
                (other5 f)).length)] at hst
          exact hspecQ.bottom hfa hst
        · rw [Connect4.NarrowBoards.play_ne _ e (other5 f) Player.white
            (fun ex => heo ex.symm)]
          exact hspecQ.bottom hfa
      · by_cases heo : e = other5 f
        · rw [hXo (other5 f) heo.symm]
          simp only [List.length_append, List.length_singleton]
          omega
        · rw [Connect4.NarrowBoards.play_ne _ e (other5 f) Player.white
            (fun ex => heo ex.symm)]
          exact hspecQ.nonempty
      · by_cases heo : e = other5 f
        · rw [hXo (other5 f) heo.symm]
          exact topNB_append_white _
        · rw [Connect4.NarrowBoards.play_ne _ e (other5 f) Player.white
              (fun ex => heo ex.symm),
            Connect4.NarrowBoards.play_ne P e (other5 f) Player.black
              (fun ex => heo ex.symm)]
          exact hs.2.2.1
      · rw [Connect4.NarrowBoards.play_ne _ e f Player.white (fun ex => hnef ex.symm),
          Connect4.NarrowBoards.play_ne P e f Player.black (fun ex => hnef ex.symm)]
        exact hs.2.2.2.1
      · intro c
        by_cases hce : c = e
        · rw [hce, hXo e rfl, Connect4.NarrowBoards.play_eq]
          simp only [List.length_append, List.length_singleton]
          have := hs.2.2.2.2.1 e
          omega
        · rw [Connect4.NarrowBoards.play_ne _ e c Player.white hce,
            Connect4.NarrowBoards.play_ne P e c Player.black hce]
          exact hs.2.2.2.2.1 c
      · rw [Connect4.NarrowBoards.toMove_play, Connect4.NarrowBoards.toMove_play,
          hs.2.2.2.2.2]
        rfl

/-! ## W-MAIN: the master induction -/

/-- Every Black-to-move invariant state is safe for White through any horizon
`k`, by induction on `k`: each branch supplies the state geometry, quantifies
over Black's legal moves, and answers with one White move into a state safe
for `k` (via `safeFor_succ_mono`). -/
private theorem white_machine_aux (h : Nat) (hh : h % 2 = 0) (h2 : 2 ≤ h) :
    ∀ k : Nat,
      (∀ Q : Board 5, WD h Q → SafeFor h .white k Q) ∧
      (∀ (a : Fin 5) (Q : Board 5), W2 h a Q → SafeFor h .white k Q) ∧
      (∀ (a f : Fin 5) (Q : Board 5), W3 h a f Q → SafeFor h .white k Q) := by
  intro k
  induction k with
  | zero =>
      refine ⟨?_, ?_, ?_⟩
      · intro Q hq; exact no_four_wd hq.1 hq.2.2.1 hq.2.2.2.1
      · intro a Q hq; exact no_four_w2 hq.1 hq.2.1 hq.2.2.1 hq.2.2.2.1
      · intro a f Q hq; exact no_four_w3 hq.1
  | succ k ih =>
      obtain ⟨A, B, D⟩ := ih
      exact ⟨fun Q hq => wd_branch h hh h2 Q hq k A B,
        fun a Q hq => w2_branch h hh a Q hq k B D,
        fun a f Q hq => w3_branch h hh a f Q hq k D⟩

/-! ## W-MAIN: the final assembly -/

/-- White (the second player) never loses on the five-column board at every
positive even height: `WhiteGoal`, the White half of
`FiveEvenDrawGoal` (Allis 1988, §2.2 restricted to five columns). -/
theorem white_nonloss_five : WhiteGoal := by
  intro m hm
  have h2 : 2 ≤ 2 * m := by omega
  have hh : (2 * m) % 2 = 0 := by omega
  intro k
  match k with
  | 0 => exact no_four_empty5 Player.black
  | 1 =>
      refine ⟨no_four_empty5 Player.black, Or.inr (Or.inr ?_)⟩
      rw [FiveAllis.toMove_empty,
        if_neg (fun ex => Player.noConfusion ex)]
      intro q hq
      exact no_four_after_first q
  | (k + 2) =>
      refine ⟨no_four_empty5 Player.black, Or.inr (Or.inr ?_)⟩
      rw [FiveAllis.toMove_empty,
        if_neg (fun ex => Player.noConfusion ex)]
      intro q hq
      have hgeom := no_four_after_first (h := 2 * m) q
      have htw : Connect4.NarrowBoards.toMove
          (Connect4.NarrowBoards.play (Connect4.NarrowBoards.emptyBoard 5) q Player.black)
          = Player.white := by
        rw [Connect4.NarrowBoards.toMove_play, FiveAllis.toMove_empty]
        rfl
      refine ⟨hgeom, Or.inr (Or.inr ?_)⟩
      rw [if_pos htw, htw]
      have key := white_machine_aux (2 * m) hh h2 k
      by_cases hq23 : q = 2 ∨ q = 3
      · have hleg : Legal (2 * m)
            (Connect4.NarrowBoards.play (Connect4.NarrowBoards.emptyBoard 5) q Player.black)
            (other5 q) := by
          unfold Connect4.NarrowBoards.Legal
          rw [Connect4.NarrowBoards.play_ne _ q (other5 q) Player.black
            (other5_ne hq23)]
          show (0 : Nat) < 2 * m
          omega
        refine ⟨other5 q, hleg, ?_⟩
        exact key.2.1 q _ (w2_entry (2 * m) h2 q hq23)
      · have hq2 : q ≠ 2 := fun ex => hq23 (Or.inl ex)
        have hq3 : q ≠ 3 := fun ex => hq23 (Or.inr ex)
        have hleg : Legal (2 * m)
            (Connect4.NarrowBoards.play (Connect4.NarrowBoards.emptyBoard 5) q Player.black)
            q := by
          unfold Connect4.NarrowBoards.Legal
          rw [Connect4.NarrowBoards.play_eq]
          show (1 : Nat) < 2 * m
          omega
        refine ⟨q, hleg, ?_⟩
        exact key.1 _ (wd_entry (2 * m) h2 q hq2 hq3)

end FiveAllis
