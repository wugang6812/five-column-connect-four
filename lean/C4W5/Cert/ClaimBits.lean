import C4W5.Cert.StretchZoneTree

/-! Check all horizontal and diagonal windows of a five-column board in six bit operations on windows.
The masks below include all exceptional white cells and all potential exceptional cells. -/
namespace C4W5.ClaimBits
open C4W5
set_option maxHeartbeats 1500000

def alt : Nat := 0x5555555555555555

private theorem alt_bit : ∀ n : Fin 64, alt.testBit n.val = decide (n.val % 2 = 0) := by
  decide +kernel

def claimed (q h₀ c : Nat) := if c = q then alt <<< (h₀ + 1) else 0

def openM (h : Nat) (p : Pos) (q h₀ c : Nat) :=
  (2^h - 1) ^^^ ((p.bm c ||| claimed q h₀ c) % 2^h)

def exceptionM (h : Nat) (p : Pos) (c : Nat) :=
  let w := p.mask .white c
  (w &&& (1 ||| (w <<< 1))) ||| (if potB h p c (p.ht c) then 2^(p.ht c) else 0)

def off (d j : Nat) := if d = 0 then 0 else if d = 1 then j else 3-j

def live (d a b c e : Nat) :=
  (a >>> off d 0) &&& (b >>> off d 1) &&& (c >>> off d 2) &&& (e >>> off d 3)

def hit (d a b c e : Nat) :=
  (a >>> off d 0) ||| (b >>> off d 1) ||| (c >>> off d 2) ||| (e >>> off d 3)

def checkWindow (d a b c e u v w z : Nat) : Bool := live d a b c e &&& hit d u v w z == 0

def three (a b c e u v w z : Nat) : Bool :=
  checkWindow 0 a b c e u v w z && checkWindow 1 a b c e u v w z && checkWindow 2 a b c e u v w z

def checkLines (h : Nat) (p : Pos) (q h₀ : Nat) : Bool :=
  force (openM h p q h₀ 0) fun a => force (openM h p q h₀ 1) fun b => force (openM h p q h₀ 2) fun c =>
  force (openM h p q h₀ 3) fun e => force (openM h p q h₀ 4) fun f =>
  force (exceptionM h p 0) fun u => force (exceptionM h p 1) fun v => force (exceptionM h p 2) fun w =>
  force (exceptionM h p 3) fun z => force (exceptionM h p 4) fun t =>
  three a b c e u v w z && three b c e f v w z t

theorem exc_bit {h : Nat} {p : Pos} {c r : Nat} (he : (excB p c r || potB h p c r) = true) :
    (exceptionM h p c).testBit r = true := by
  unfold exceptionM
  rw [Bool.or_eq_true] at he
  rw [Nat.testBit_or, Bool.or_eq_true]
  rcases he with he | he
  · left
    simp only [excB, Bool.and_eq_true, Nat.blt_eq, Bool.not_eq_true', Bool.or_eq_true, beq_iff_eq] at he
    obtain ⟨⟨hr,hb⟩,hprev⟩ := he
    have wm (y : Nat) (hy : y < p.ht c) (hblack : (p.bm c).testBit y = false) :
        (p.mask .white c).testBit y = true := by simp [Pos.mask, maskOf, Nat.testBit_xor, Nat.testBit_two_pow_sub_one, hy, hblack]
    rw [Nat.testBit_and, Bool.and_eq_true, Nat.testBit_or, Bool.or_eq_true]
    refine ⟨wm r hr hb, ?_⟩
    rcases hprev with rfl | hp
    · left; decide
    · by_cases hz : r=0
      · subst r; left; decide
      · right; simp [Nat.testBit_shiftLeft, show 1 ≤ r by omega, wm _ (by omega) hp]
  · right
    have er : r = p.ht c := by
      simp only [potB, Bool.and_eq_true, beq_iff_eq] at he
      exact he.1.1
    subst r; simp [he, Nat.testBit_two_pow]

private theorem op_bit {h : Nat} {p : Pos} {q h₀ c y : Nat} (hy : y < h) (hh : h ≤ 64)
    (hb : (p.bm c).testBit y = false) (hc : ¬ (c = q ∧ h₀ < y ∧ (y - h₀) % 2 = 1)) :
    (openM h p q h₀ c).testBit y = true := by
  have hm : (claimed q h₀ c).testBit y = false := by
    unfold claimed
    by_cases eq : c=q
    · rw [if_pos eq, Nat.testBit_shiftLeft]
      by_cases hl : h₀+1 ≤ y
      · have hv : y-(h₀+1) < 64 := by omega
        have ha := alt_bit ⟨_,hv⟩
        have hn : (y-(h₀+1)) % 2 ≠ 0 := by omega
        simp [hl, ha, hn]
      · simp [hl]
    · simp [eq]
  simp [openM,Nat.testBit_xor,Nat.testBit_two_pow_sub_one,Nat.testBit_mod_two_pow,Nat.testBit_or,hy,hb,hm]

private theorem window_contra {f g : Nat → Nat} {d x k i : Nat} (hi : i < 4)
    (hf : ∀ j : Fin 4, (f (x+j.val)).testBit (k+off d j.val) = true)
    (hg : (g (x+i)).testBit (k+off d i) = true)
    (hw : checkWindow d (f x) (f (x+1)) (f (x+2)) (f (x+3))
      (g x) (g (x+1)) (g (x+2)) (g (x+3)) = true) : False := by
  unfold checkWindow at hw
  have eq := beq_iff_eq.mp hw
  have no := congrArg (fun n : Nat => n.testBit k) eq
  have h0 := hf 0; have h1 := hf 1; have h2 := hf 2; have h3 := hf 3
  change (f x).testBit (k+off d 0) = true at h0
  change (f (x+1)).testBit (k+off d 1) = true at h1
  change (f (x+2)).testBit (k+off d 2) = true at h2
  change (f (x+3)).testBit (k+off d 3) = true at h3
  rw [Nat.add_comm k] at h0 h1 h2 h3 hg
  rcases (by omega : i=0 ∨ i=1 ∨ i=2 ∨ i=3) with rfl | rfl | rfl | rfl <;>
    simp [live,hit,Nat.testBit_and,Nat.testBit_or,Nat.testBit_shiftRight,h0,h1,h2,h3,hg, Nat.add_zero] at no <;> simp_all

private theorem window_at {h : Nat} {p : Pos} {q h₀ x d : Nat} (hx : x ≤ 1) (hd : d ≤ 2)
    (hscan : checkLines h p q h₀ = true) :
    let f := openM h p q h₀; let g := exceptionM h p
    checkWindow d (f x) (f (x+1)) (f (x+2)) (f (x+3)) (g x) (g (x+1)) (g (x+2)) (g (x+3)) = true := by
  simp only [checkLines, force_eq, three, Bool.and_eq_true] at hscan
  rcases (by omega : x=0 ∨ x=1) with rfl | rfl <;>
    rcases (by omega : d=0 ∨ d=1 ∨ d=2) with rfl | rfl | rfl
  exacts [hscan.1.1.1,hscan.1.1.2,hscan.1.2,hscan.2.1.1,hscan.2.1.2,hscan.2.2]

private theorem allUpTo_of {n : Nat} {f : Nat → Bool} (hf : ∀ r, r ≤ n → f r = true) : allUpTo n f = true := by
  induction n with
  | zero => exact hf 0 (by omega)
  | succ n ih => rw [allUpTo, Bool.and_eq_true]; exact ⟨hf _ (by omega), ih (fun r hr => hf r (by omega))⟩

private theorem one_line {h : Nat} {p : Pos} {q : Fin 5} {h₀ c r : Nat} (hh : h ≤ 64)
    (hs : checkLines h p q h₀ = true) (he : (excB p c r || potB h p c r) = true) :
    linesDeadB h p q h₀ c r = true := by
  unfold linesDeadB
  simp only [List.all_eq_true]
  intro d hd i hi
  have hd' : d ≤ 2 := by simp at hd; omega
  have hi' : i < 4 := by simp at hi; omega
  rw [List.any_eq_true]
  by_contra hn
  have hhj (j : Nat) (hj : j < 4) : lineJN h p q h₀ (c+3-i+j) (yN d r i j) = false := by
    cases hjn : lineJN h p q h₀ (c+3-i+j) (yN d r i j) with
    | false => rfl
    | true =>
      exfalso; apply hn; refine ⟨j, ?_, hjn⟩
      simp; omega
  have coord (j : Nat) (hj : j < 4) :
      3 ≤ c+3-i+j ∧ c+3-i+j < 8 ∧ 3 ≤ yN d r i j ∧ yN d r i j < h+3 := by
    have hhj' := hhj j hj
    by_contra hno
    simp [lineJN,hno] at hhj'
  have x₀ := coord 0 (by omega)
  have x₃ := coord 3 (by omega)
  have hc : i ≤ c := by omega
  have hx : c-i ≤ 1 := by omega
  have hr : off d i ≤ r := by
    rcases (by omega : d=0 ∨ d=1 ∨ d=2) with rfl | rfl | rfl <;>
      simp [off,yN] at * <;> omega
  have ycoord (j : Nat) (hj : j < 4) : yN d r i j = (r-off d i) + off d j + 3 := by
    rcases (by omega : d=0 ∨ d=1 ∨ d=2) with rfl | rfl | rfl <;>
      simp [off,yN] at * <;> omega
  apply window_contra (f := openM h p q h₀) (g := exceptionM h p) (k := r-off d i)
    (i := i) hi' _ _ (window_at hx hd' hs)
  · intro j
    have jm := j.isLt
    have z := hhj j.val jm
    have t := coord j.val jm
    have yc := ycoord j.val jm
    have xb : (c+3-i+j.val)-3 = c-i+j.val := by omega
    have yb : yN d r i j.val - 3 = r-off d i + off d j.val := by omega
    simp only [lineJN, decide_eq_true t, Bool.true_and, Bool.not_true, Bool.or_false,
      Bool.or_eq_false_iff, decide_eq_false_iff_not, xb, yb] at z
    apply op_bit (by omega) hh z.1
    intro ⟨heq, hlt, hmod⟩
    exact z.2 ⟨by omega,by omega,by omega⟩
  · have e1 : c-i+i = c := by omega
    have e2 : r-off d i + off d i = r := by omega
    simpa only [e1,e2] using exc_bit (h := h) he

def fastQ (h : Nat) (p : Pos) (q : Fin 5) : Bool :=
  (h - p.ht q.val) % 2 == 1 && checkLines h p q.val (p.ht q.val)

def fast (h : Nat) (p : Pos) : Bool :=
  h ≤ 64 && h % 2 == 0 && p.wfB h &&
    ntrB h p 0 && ntrB h p 1 && ntrB h p 2 && ntrB h p 3 && ntrB h p 4 &&
    (fastQ h p 0 || fastQ h p 1 || fastQ h p 2 || fastQ h p 3 || fastQ h p 4)

private theorem q_sound {h : Nat} {p : Pos} {q : Fin 5} (hh : h ≤ 64) (he : h % 2 = 0)
    (hw : p.wfB h = true) (nt : ∀ c : Fin 5, ntrB h p c.val = true)
    (hq : fastQ h p q = true) : claimQ h p q = true := by
  simp only [fastQ, Bool.and_eq_true, beq_iff_eq] at hq
  have hc (c : Fin 5) : colB h p q c.val = true := by
    unfold colB cellsOK
    rw [nt c, Bool.true_and]
    apply allUpTo_of
    intro r _
    cases ex : (excB p c.val r || potB h p c.val r) with
    | false => rfl
    | true => exact one_line (q := q) (h₀ := p.ht q.val) hh hq.2 ex
  simp only [claimQ, Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨he,hw⟩, hq.1⟩,hc 0⟩,hc 1⟩,hc 2⟩,hc 3⟩,hc 4⟩

theorem fast_sound {h : Nat} {p : Pos} (hf : fast h p = true) : claimB h p = true := by
  simp only [fast, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.or_eq_true] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hh, he⟩, hw⟩, n0⟩, n1⟩, n2⟩, n3⟩, n4⟩, hq⟩ := hf
  have nt : ∀ c : Fin 5, ntrB h p c.val = true := by
    intro c; rcases fin5c c with rfl | rfl | rfl | rfl | rfl
    exacts [n0,n1,n2,n3,n4]
  simp only [claimB, Bool.or_eq_true]
  rcases hq with ((((a | a) | a) | a) | a)
  · exact Or.inl (Or.inl (Or.inl (Or.inl (q_sound hh he hw nt a))))
  · exact Or.inl (Or.inl (Or.inl (Or.inr (q_sound hh he hw nt a))))
  · exact Or.inl (Or.inl (Or.inr (q_sound hh he hw nt a)))
  · exact Or.inl (Or.inr (q_sound hh he hw nt a))
  · exact Or.inr (q_sound hh he hw nt a)

end C4W5.ClaimBits
