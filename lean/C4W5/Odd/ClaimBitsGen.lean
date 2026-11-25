import C4W5.Theory.ClaimLeafBridge
import C4W5.Cert.Fast

/-!
# Unified Color-Polymorphic Bitboard Claim Checker (`ClaimBitsGen`)

Checks all six horizontal and diagonal 4-windows on a 5-column board in six GMP bitwise operations
for an arbitrary defender `me : Player` (`opp := opponent me`), proving:
1. `fastOdd_sound`  : `fastOdd me h p = true → ∃ q : Fin 5, ClaimOddHyp me h p.toBoard q`
2. `fastEven_sound` : `fastEven me h p = true → ClaimEvenHyp me h p.toBoard`

Zero `sorry`, zero custom axioms.
-/

namespace C4W5Gen
open Connect4 (Player opponent)
open Connect4.NarrowBoards
open C4W5

set_option linter.deprecated false
set_option maxHeartbeats 1500000

def alt64 : Nat := 0x5555555555555555

private theorem alt64_bit : ∀ n : Fin 64, alt64.testBit n.val = decide (n.val % 2 = 0) := by
  decide +kernel

def claimedOdd (q h0 c : Nat) : Nat :=
  if c = q then alt64 <<< (h0 + 1) else 0

def claimedEven (h : Nat) (p : Pos) (c : Nat) : Nat :=
  if p.ht c < h ∧ (h - p.ht c) % 2 = 0 then alt64 <<< (p.ht c + 1) else 0

def openMG (h : Nat) (me : Player) (p : Pos) (cm : Nat → Nat) (c : Nat) : Nat :=
  (2 ^ h - 1) ^^^ (((p.mask me c) ||| cm c) % 2 ^ h)

def potBG (h : Nat) (opp : Player) (p : Pos) (c : Nat) : Bool :=
  Nat.blt (p.ht c) h && (p.ht c == 0 || (p.mask opp c).testBit (p.ht c - 1))

def exceptionMG (h : Nat) (opp : Player) (p : Pos) (c : Nat) : Nat :=
  let o := p.mask opp c
  (o &&& (1 ||| (o <<< 1))) ||| (if potBG h opp p c then 2 ^ (p.ht c) else 0)

def offG : Nat → Nat → Nat
  | 0, _ => 0
  | 1, j => j
  | _, j => 3 - j

-- Keep the three scan directions explicit when the cell index is symbolic.
-- Rewriting these equations avoids leaving a multi-discriminant match for omega.
private theorem offG_0 (j : Nat) : offG 0 j = 0 := rfl
private theorem offG_1 (j : Nat) : offG 1 j = j := rfl
private theorem offG_2 (j : Nat) : offG 2 j = 3 - j := rfl

def liveG (d a b c e : Nat) : Nat :=
  (a >>> offG d 0) &&& (b >>> offG d 1) &&& (c >>> offG d 2) &&& (e >>> offG d 3)

def hitG (d a b c e : Nat) : Nat :=
  (a >>> offG d 0) ||| (b >>> offG d 1) ||| (c >>> offG d 2) ||| (e >>> offG d 3)

def checkWindowG (d a b c e u v w z : Nat) : Bool :=
  (liveG d a b c e &&& hitG d u v w z) == 0

def threeG (a b c e u v w z : Nat) : Bool :=
  checkWindowG 0 a b c e u v w z &&
  checkWindowG 1 a b c e u v w z &&
  checkWindowG 2 a b c e u v w z

def checkLinesG (h : Nat) (me : Player) (p : Pos) (cm : Nat → Nat) : Bool :=
  force (openMG h me p cm 0) fun a => force (openMG h me p cm 1) fun b =>
  force (openMG h me p cm 2) fun c => force (openMG h me p cm 3) fun e =>
  force (openMG h me p cm 4) fun f =>
  force (exceptionMG h (opponent me) p 0) fun u => force (exceptionMG h (opponent me) p 1) fun v =>
  force (exceptionMG h (opponent me) p 2) fun w => force (exceptionMG h (opponent me) p 3) fun z =>
  force (exceptionMG h (opponent me) p 4) fun t =>
  threeG a b c e u v w z && threeG b c e f v w z t

def ntrBG (h : Nat) (opp : Player) (p : Pos) (c : Nat) : Bool :=
  !(Nat.blt (p.ht c) h) ||
    !(Nat.ble 3 (p.ht c) &&
      (p.mask opp c).testBit (p.ht c - 1) &&
      (p.mask opp c).testBit (p.ht c - 2) &&
      (p.mask opp c).testBit (p.ht c - 3))

def fastOddQ (me : Player) (h : Nat) (p : Pos) (q : Nat) : Bool :=
  (h - p.ht q) % 2 == 1 && checkLinesG h me p (claimedOdd q (p.ht q))

def fastOdd (me : Player) (h : Nat) (p : Pos) : Bool :=
  Nat.ble h 64 && emptyParity h (opponent me) == 1 && p.wfB h &&
    ntrBG h (opponent me) p 0 && ntrBG h (opponent me) p 1 && ntrBG h (opponent me) p 2 &&
    ntrBG h (opponent me) p 3 && ntrBG h (opponent me) p 4 &&
    (fastOddQ me h p 0 || fastOddQ me h p 1 || fastOddQ me h p 2 ||
     fastOddQ me h p 3 || fastOddQ me h p 4)

def fastEven (me : Player) (h : Nat) (p : Pos) : Bool :=
  Nat.ble h 64 && emptyParity h (opponent me) == 0 && p.wfB h &&
    ntrBG h (opponent me) p 0 && ntrBG h (opponent me) p 1 && ntrBG h (opponent me) p 2 &&
    ntrBG h (opponent me) p 3 && ntrBG h (opponent me) p 4 &&
    checkLinesG h me p (claimedEven h p)

/-! ## Bitwise Soundness Lemmas -/

private theorem op_bitG {h : Nat} {me : Player} {p : Pos} {cm : Nat → Nat} {c y : Nat}
    (hy : y < h) (hb : (p.mask me c).testBit y = false) (hcm : (cm c).testBit y = false) :
    (openMG h me p cm c).testBit y = true := by
  simp [openMG, Nat.testBit_xor, Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow,
    Nat.testBit_or, hy, hb, hcm]

private theorem exc_bitG {h : Nat} {opp : Player} {p : Pos} (hw : p.WF h) {c : Fin 5} {r : Nat}
    (he : ExceptionalP opp p.toBoard c r ∨ PotExcP opp h p.toBoard c r) :
    (exceptionMG h opp p c.val).testBit r = true := by
  unfold exceptionMG
  dsimp only
  rw [Nat.testBit_or, Bool.or_eq_true]
  rcases he with ⟨hs, hprev⟩ | ⟨hr, hlt, htop⟩
  · left
    have ho : (p.mask opp c.val).testBit r = true :=
      (testBit_maskOf (hw c.val).1 opp r).mpr hs
    rw [Nat.testBit_and, Bool.and_eq_true, Nat.testBit_or, Bool.or_eq_true]
    refine ⟨ho, ?_⟩
    rcases hprev with rfl | hp
    · left; decide
    · by_cases hz : r = 0
      · subst hz; left; decide
      · right
        have hp' : (p.mask opp c.val).testBit (r - 1) = true :=
          (testBit_maskOf (hw c.val).1 opp (r - 1)).mpr hp
        simp [Nat.testBit_shiftLeft, show 1 ≤ r by omega, hp']
  · right
    rw [Pos.height] at hr hlt htop
    subst hr
    have hpot : potBG h opp p c.val = true := by
      unfold potBG
      simp only [Bool.and_eq_true, Nat.blt_eq, Bool.or_eq_true, beq_iff_eq]
      refine ⟨hlt, ?_⟩
      rcases htop with hz | hp
      · exact Or.inl hz
      · exact Or.inr ((testBit_maskOf (hw c.val).1 opp (p.ht c.val - 1)).mpr hp)
    rw [if_pos hpot, Nat.testBit_two_pow_self]

private theorem window_contraG {f g : Nat → Nat} {d x k i : Nat} (hi : i < 4)
    (hf : ∀ j : Fin 4, (f (x + j.val)).testBit (k + offG d j.val) = true)
    (hg : (g (x + i)).testBit (k + offG d i) = true)
    (hw : checkWindowG d (f x) (f (x + 1)) (f (x + 2)) (f (x + 3))
      (g x) (g (x + 1)) (g (x + 2)) (g (x + 3)) = true) : False := by
  unfold checkWindowG at hw
  have eq := beq_iff_eq.mp hw
  have no := congrArg (fun n : Nat => n.testBit k) eq
  have h0 := hf 0; have h1 := hf 1; have h2 := hf 2; have h3 := hf 3
  change (f x).testBit (k + offG d 0) = true at h0
  change (f (x + 1)).testBit (k + offG d 1) = true at h1
  change (f (x + 2)).testBit (k + offG d 2) = true at h2
  change (f (x + 3)).testBit (k + offG d 3) = true at h3
  rw [Nat.add_comm k] at h0 h1 h2 h3 hg
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;>
    simp [liveG, hitG, Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftRight,
      h0, h1, h2, h3, hg] at no <;> simp_all

private theorem window_atG {h : Nat} {me : Player} {p : Pos} {cm : Nat → Nat} {x d : Nat}
    (hx : x ≤ 1) (hd : d ≤ 2) (hscan : checkLinesG h me p cm = true) :
    let f := openMG h me p cm
    let g := exceptionMG h (opponent me) p
    checkWindowG d (f x) (f (x + 1)) (f (x + 2)) (f (x + 3))
      (g x) (g (x + 1)) (g (x + 2)) (g (x + 3)) = true := by
  simp only [checkLinesG, force_eq, threeG, Bool.and_eq_true] at hscan
  rcases (by omega : x = 0 ∨ x = 1) with rfl | rfl <;>
    rcases (by omega : d = 0 ∨ d = 1 ∨ d = 2) with rfl | rfl | rfl
  exacts [hscan.1.1.1, hscan.1.1.2, hscan.1.2, hscan.2.1.1, hscan.2.1.2, hscan.2.2]

private theorem checkLinesG_sound {h : Nat} {me : Player} {p : Pos} (hw : p.WF h)
    {cm : Nat → Nat} {Q : Fin 5 → Bool} {h0 : Fin 5 → Nat}
    (hcm : ∀ (d : Fin 5) (y : Nat), y < h → ¬ ClaimedSet Q h0 (d.val : Int) (y : Int) →
      (cm d.val).testBit y = false)
    (hscan : checkLinesG h me p cm = true)
    {c : Fin 5} {r : Nat}
    (he : ExceptionalP (opponent me) p.toBoard c r ∨ PotExcP (opponent me) h p.toBoard c r) :
    LinesDeadSet me h p.toBoard Q h0 c r := by
  intro dy hdy i
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hdy
  by_contra hnot
  have hall : ∀ j : Fin 4,
      cellAtInt h p.toBoard
        ((c.val : Int) - (i.val : Int) * 1 + (j.val : Int) * 1)
        ((r : Int) - (i.val : Int) * dy + (j.val : Int) * dy) ≠ some me ∧
      ¬ ClaimedSet Q h0
        ((c.val : Int) - (i.val : Int) * 1 + (j.val : Int) * 1)
        ((r : Int) - (i.val : Int) * dy + (j.val : Int) * dy) ∧
      (0 ≤ (c.val : Int) - (i.val : Int) * 1 + (j.val : Int) * 1 ∧
       (c.val : Int) - (i.val : Int) * 1 + (j.val : Int) * 1 < 5 ∧
       0 ≤ (r : Int) - (i.val : Int) * dy + (j.val : Int) * dy ∧
       (r : Int) - (i.val : Int) * dy + (j.val : Int) * dy < (h : Int)) := by
    intro j
    exact ⟨fun hm => hnot ⟨j, Or.inl hm⟩,
           fun hc => hnot ⟨j, Or.inr (Or.inl hc)⟩,
           Classical.not_not.mp (fun hb => hnot ⟨j, Or.inr (Or.inr hb)⟩)⟩
  have b0 := (hall 0).2.2
  have b3 := (hall 3).2.2
  have e0 : ((0 : Fin 4).val : Int) = 0 := rfl
  have e3 : ((3 : Fin 4).val : Int) = 3 := rfl
  rw [e0] at b0
  rw [e3] at b3
  have hc_lt := c.isLt
  have hi_lt := i.isLt
  have hic : i.val ≤ c.val := by omega
  have hci : c.val - i.val ≤ 1 := by omega
  obtain ⟨d, hd, hro, hyeq⟩ : ∃ d : Nat, d ≤ 2 ∧ offG d i.val ≤ r ∧
      ∀ j : Fin 4,
        (r : Int) - (i.val : Int) * dy + (j.val : Int) * dy =
          (((r - offG d i.val) + offG d j.val : Nat) : Int) := by
    rcases hdy with rfl | rfl | rfl
    · refine ⟨0, by omega, by simp only [offG_0]; omega, fun j => ?_⟩
      simp only [offG_0]
      omega
    · refine ⟨1, by omega, by simp only [offG_1]; omega, fun j => ?_⟩
      have hj := j.isLt
      simp only [offG_1]
      omega
    · refine ⟨2, by omega, by simp only [offG_2]; omega, fun j => ?_⟩
      have hj := j.isLt
      simp only [offG_2]
      omega
  refine window_contraG (f := openMG h me p cm) (g := exceptionMG h (opponent me) p)
    (d := d) (x := c.val - i.val) (k := r - offG d i.val) (i := i.val) hi_lt
    ?_ ?_ (window_atG hci hd hscan)
  · intro j
    have hj_lt := j.isLt
    obtain ⟨hcell, hcl, hbounds⟩ := hall j
    have hxj : (c.val : Int) - (i.val : Int) * 1 + (j.val : Int) * 1 =
        ((⟨c.val - i.val + j.val, by omega⟩ : Fin 5).val : Int) := by
      simp only; omega
    have hyj := hyeq j
    rw [hxj, hyj] at hcell hcl hbounds
    have hyj_lt : (r - offG d i.val) + offG d j.val < h := by omega
    have hmask_false :
        (p.mask me (c.val - i.val + j.val)).testBit ((r - offG d i.val) + offG d j.val) = false := by
      cases hb : (p.mask me (c.val - i.val + j.val)).testBit ((r - offG d i.val) + offG d j.val) with
      | false => rfl
      | true =>
        exfalso; apply hcell
        rw [cell_iff hw me ⟨c.val - i.val + j.val, by omega⟩]
        refine ⟨by omega, ?_⟩
        have htn : (((r - offG d i.val) + offG d j.val : Nat) : Int).toNat =
            (r - offG d i.val) + offG d j.val := by omega
        rw [htn]; exact hb
    have hcm_false : (cm (c.val - i.val + j.val)).testBit ((r - offG d i.val) + offG d j.val) = false :=
      hcm ⟨c.val - i.val + j.val, by omega⟩ _ hyj_lt hcl
    exact op_bitG hyj_lt hmask_false hcm_false
  · have ex1 : c.val - i.val + i.val = c.val := by omega
    have ex2 : (r - offG d i.val) + offG d i.val = r := by omega
    rw [ex1, ex2]
    exact exc_bitG hw he

private theorem ntrBG_sound {h : Nat} {opp : Player} {p : Pos} (hw : p.WF h) {c : Fin 5}
    (hnt : ntrBG h opp p c.val = true) :
    (p.toBoard c).length < h → ¬ TopThreeP opp p.toBoard c := by
  intro hlt ht
  rw [Pos.height] at hlt
  obtain ⟨t0, t1, t2, t3⟩ := ht
  rw [Pos.height] at t0 t1 t2 t3
  have b1 := (testBit_maskOf (hw c.val).1 opp (p.ht c.val - 1)).mpr t1
  have b2 := (testBit_maskOf (hw c.val).1 opp (p.ht c.val - 2)).mpr t2
  have b3 := (testBit_maskOf (hw c.val).1 opp (p.ht c.val - 3)).mpr t3
  have hblt : Nat.blt (p.ht c.val) h = true := by rw [Nat.blt_eq]; exact hlt
  have hble : Nat.ble 3 (p.ht c.val) = true := by rw [Nat.ble_eq]; exact t0
  unfold ntrBG Pos.mask at hnt
  rw [hblt, hble, b1, b2, b3] at hnt
  exact Bool.noConfusion hnt

private theorem fin5_casesG (c : Fin 5) : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 := by
  revert c; decide

private theorem fastOddQ_sound {me : Player} {h : Nat} {p : Pos} {q : Fin 5}
    (hh : h ≤ 64) (hreg : emptyParity h (opponent me) = 1) (hwf : p.wfB h = true)
    (hnt : ∀ c : Fin 5, ntrBG h (opponent me) p c.val = true)
    (hq : fastOddQ me h p q.val = true) :
    ClaimOddHyp me h p.toBoard q := by
  simp only [fastOddQ, Bool.and_eq_true, beq_iff_eq] at hq
  have hw := Pos.wfB_sound hwf
  refine ⟨hreg, fun c => by rw [Pos.height]; exact (hw c.val).2,
          by rw [Pos.height]; exact hq.1,
          fun c => ntrBG_sound hw (hnt c), ?_⟩
  intro c r he
  refine checkLinesG_sound hw (cm := claimedOdd q.val (p.ht q.val)) ?_ hq.2 he
  intro d y hy hnc
  unfold claimedOdd
  by_cases eq : d.val = q.val
  · rw [if_pos eq, Nat.testBit_shiftLeft]
    by_cases hl : p.ht q.val + 1 ≤ y
    · have hv : y - (p.ht q.val + 1) < 64 := by omega
      have ha := alt64_bit ⟨_, hv⟩
      have hn : (y - (p.ht q.val + 1)) % 2 ≠ 0 := by
        intro hm
        apply hnc
        have hdq : d = q := Fin.ext eq
        subst hdq
        refine ⟨d, by simp, rfl, ?_, ?_⟩
        · dsimp only; rw [Pos.height]; omega
        · dsimp only; rw [Pos.height]; omega
      simp [hl, ha, hn]
    · simp [hl]
  · simp [eq]

/-- **Soundness 1: `fastOdd` proves `∃ q, ClaimOddHyp me h p.toBoard q` (Odd-H White, Even-H Black).** -/
theorem fastOdd_sound {me : Player} {h : Nat} {p : Pos} (hf : fastOdd me h p = true) :
    ∃ q : Fin 5, ClaimOddHyp me h p.toBoard q := by
  simp only [fastOdd, Bool.and_eq_true, Nat.ble_eq, beq_iff_eq, Bool.or_eq_true] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hh, hreg⟩, hwf⟩, n0⟩, n1⟩, n2⟩, n3⟩, n4⟩, hq⟩ := hf
  have hnt : ∀ c : Fin 5, ntrBG h (opponent me) p c.val = true := by
    intro c; rcases fin5_casesG c with rfl | rfl | rfl | rfl | rfl
    exacts [n0, n1, n2, n3, n4]
  rcases hq with (((hq | hq) | hq) | hq) | hq
  · exact ⟨0, fastOddQ_sound hh hreg hwf hnt hq⟩
  · exact ⟨1, fastOddQ_sound hh hreg hwf hnt hq⟩
  · exact ⟨2, fastOddQ_sound hh hreg hwf hnt hq⟩
  · exact ⟨3, fastOddQ_sound hh hreg hwf hnt hq⟩
  · exact ⟨4, fastOddQ_sound hh hreg hwf hnt hq⟩

/-- **Soundness 2: `fastEven` proves `ClaimEvenHyp me h p.toBoard` (Odd-H Black, Even-H White).** -/
theorem fastEven_sound {me : Player} {h : Nat} {p : Pos} (hf : fastEven me h p = true) :
    ClaimEvenHyp me h p.toBoard := by
  simp only [fastEven, Bool.and_eq_true, Nat.ble_eq, beq_iff_eq] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hh, hreg⟩, hwf⟩, n0⟩, n1⟩, n2⟩, n3⟩, n4⟩, hscan⟩ := hf
  have hw := Pos.wfB_sound hwf
  have hnt : ∀ c : Fin 5, ntrBG h (opponent me) p c.val = true := by
    intro c; rcases fin5_casesG c with rfl | rfl | rfl | rfl | rfl
    exacts [n0, n1, n2, n3, n4]
  refine ⟨hreg, fun c => by rw [Pos.height]; exact (hw c.val).2,
          fun c => ntrBG_sound hw (hnt c), ?_⟩
  intro c r he
  refine checkLinesG_sound hw (cm := claimedEven h p) ?_ hscan he
  intro d y hy hnc
  unfold claimedEven
  by_cases hc : p.ht d.val < h ∧ (h - p.ht d.val) % 2 = 0
  · rw [if_pos hc, Nat.testBit_shiftLeft]
    by_cases hl : p.ht d.val + 1 ≤ y
    · have hv : y - (p.ht d.val + 1) < 64 := by omega
      have ha := alt64_bit ⟨_, hv⟩
      have hn : (y - (p.ht d.val + 1)) % 2 ≠ 0 := by
        intro hm
        apply hnc
        refine ⟨d, ?_, rfl, ?_, ?_⟩
        · simp only [evenCols, decide_eq_true_eq, Pos.height]; exact hc
        · dsimp only; rw [Pos.height]; omega
        · dsimp only; rw [Pos.height]; omega
      simp [hl, ha, hn]
    · simp [hl]
  · simp [hc]

#print axioms fastOdd_sound
#print axioms fastEven_sound

end C4W5Gen
