import experiments.NarrowBoards
import Mathlib.Tactic.FinCases

namespace FiveAllis
open Connect4 (Player opponent)
open Connect4.NarrowBoards

abbrev WhiteGoal := ∀ m : Nat, 1 ≤ m → CanAvoidLoss (2*m) .white (emptyBoard 5)

theorem toMove_empty (w : Nat) : toMove (emptyBoard w) = .black := by
  simp [toMove, totalStones, emptyBoard]

theorem no_four_empty5 {h : Nat} (p : Player) : ¬ HasFour h (emptyBoard 5) p := by
  rintro (⟨x,y,hf⟩ | ⟨x,y,hf⟩ | ⟨x,y,hf⟩ | ⟨x,y,hf⟩) <;>
    obtain ⟨c, _, _, _, hs⟩ := cellAtInt_some (hf 0) <;>
    simp [emptyBoard, stone] at hs


/-- R columns: Black stones only at even 0-based index (odd paper row). -/
def SOdd (l : List Player) : Prop :=
  ∀ i, stone l i = some .black → i % 2 = 0

/-- p column: Black stones only at odd 0-based index. -/
def SEven (l : List Player) : Prop :=
  ∀ i, stone l i = some .black → i % 2 = 1

/-- q column: Black stones only at index ≤ 1 or odd index. -/
def SQ (l : List Player) : Prop :=
  ∀ i, stone l i = some .black → i ≤ 1 ∨ i % 2 = 1

/-- Opened P column (phase 3): the only possible adjacent Black pair is 0,1. -/
def SOpen (l : List Player) : Prop :=
  ∀ i, stone l i = some .black → stone l (i + 1) = some .black → i = 0

/-- Column top is not a Black stone. -/
def TopNB (l : List Player) : Prop :=
  ∀ i, stone l i = some .black → i + 1 ≠ l.length

theorem topNB_iff (l : List Player) : TopNB l ↔
    stone l (l.length - 1) ≠ some .black := by
  constructor
  · intro ht hs
    have hb := stone_bound l (l.length - 1) .black hs
    exact ht (l.length - 1) hs (by omega)
  · intro ht i hs he
    have h1 : l.length - 1 = i := by omega
    rw [h1] at ht
    exact ht hs

theorem topNB_append_white (l : List Player) : TopNB (l ++ [.white]) := by
  rw [topNB_iff]
  have hlen : (l ++ [Player.white]).length - 1 = l.length := by
    simp only [List.length_append, List.length_singleton]
    omega
  rw [hlen]
  have hr : ¬ (l.length < l.length) := by omega
  simp [stone_append, hr]

theorem sOdd_append_white (hn : SOdd l) : SOdd (l ++ [.white]) :=
  fun i hs => hn i (stone_append_other (by decide) hs)

theorem sEven_append_white (hn : SEven l) : SEven (l ++ [.white]) :=
  fun i hs => hn i (stone_append_other (by decide) hs)

theorem sQ_append_white (hn : SQ l) : SQ (l ++ [.white]) :=
  fun i hs => hn i (stone_append_other (by decide) hs)

theorem sOpen_append_white (hn : SOpen l) : SOpen (l ++ [.white]) := by
  intro i h0 h1
  exact hn i (stone_append_other (by decide) h0)
    (stone_append_other (by decide) h1)

theorem sOdd_append_black (hn : SOdd l) (hlen : l.length % 2 = 0) :
    SOdd (l ++ [.black]) := by
  intro i hs
  by_cases hr : i < l.length
  · exact hn i (by simpa [stone_append, hr] using hs)
  · have he : i = l.length := by
      have hb := stone_bound _ i .black hs
      simp only [List.length_append, List.length_singleton] at hb
      omega
    subst i
    simpa [stone_append, hr, hlen] using hs

theorem sEven_append_black (hn : SEven l) (hlen : l.length % 2 = 1) :
    SEven (l ++ [.black]) := by
  intro i hs
  by_cases hr : i < l.length
  · exact hn i (by simpa [stone_append, hr] using hs)
  · have he : i = l.length := by
      have hb := stone_bound _ i .black hs
      simp only [List.length_append, List.length_singleton] at hb
      omega
    subst i
    simpa [stone_append, hr, hlen] using hs

theorem sQ_append_black (hn : SQ l) (hlen : l.length % 2 = 1) :
    SQ (l ++ [.black]) := by
  intro i hs
  by_cases hr : i < l.length
  · exact hn i (by simpa [stone_append, hr] using hs)
  · have he : i = l.length := by
      have hb := stone_bound _ i .black hs
      simp only [List.length_append, List.length_singleton] at hb
      omega
    subst i
    exact Or.inr (by simpa [stone_append, hr, hlen] using hs)

theorem sOpen_append_black (hn : SOpen l) (ht : TopNB l) :
    SOpen (l ++ [.black]) := by
  intro i h0 h1
  have hb : i + 1 < (l ++ [Player.black]).length := stone_bound _ _ _ h1
  simp only [List.length_append, List.length_singleton] at hb
  by_cases hr : i < l.length
  · by_cases hr1 : i + 1 < l.length
    · exact hn i (by simpa [stone_append, hr] using h0)
        (by simpa [stone_append, hr1] using h1)
    · rw [topNB_iff] at ht
      have hei : l.length - 1 = i := by omega
      rw [hei] at ht
      have hsa := stone_append l Player.black i
      rw [if_pos hr] at hsa
      rw [hsa] at h0
      exact (ht h0).elim
  · have he : i = l.length := by omega
    subst i
    simp [stone_append] at h1

theorem sEven_sOpen (hn : SEven l) : SOpen l := by
  intro i h0 h1
  have e0 := hn i h0
  have e1 := hn (i + 1) h1
  omega

theorem sQ_sOpen (hn : SQ l) : SOpen l := by
  intro i h0 h1
  rcases hn i h0 with hi | hi
  · rcases hn (i + 1) h1 with hj | hj <;> omega
  · rcases hn (i + 1) h1 with hj | hj <;> omega


end FiveAllis
