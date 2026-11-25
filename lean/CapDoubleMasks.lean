import CapTransferCheck
import LongThreatBits

/-! Two distinct mask obligations for the CapTransfer checker. -/
namespace C4W5.CapFast
open Connect4.NarrowBoards C4W5.ClaimBits
open C4W5.CapTransfer (GateGuard)
open C4W5.LongThreat (selected)
set_option maxHeartbeats 2000000
set_option linter.deprecated false

private theorem alt_bit' : ∀ n : Fin 64, alt.testBit n.val = decide (n.val % 2 = 0) := by
  decide +kernel

private theorem shift_alt {k y : Nat} (hy : y < 64) (h : (alt <<< k).testBit y = true) :
    k ≤ y ∧ (y-k) % 2 = 0 := by
  rw [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hle,hbit⟩ := h
  have hh : y-k < 64 := by omega
  have ha := alt_bit' ⟨_,hh⟩
  change alt.testBit (y-k) = _ at ha
  rw [ha, decide_eq_true_eq] at hbit
  exact ⟨hle,hbit⟩

private theorem shift_bar {k y : Nat} (h : (((2^64 : Nat) - 1) <<< k).testBit y = true) : k ≤ y := by
  rw [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

private theorem cover {p : Pos} {c : Fin 5} {y : Nat} (hy : y < 64)
    (h : (alt <<< (p.ht c.val + 1)).testBit y = true) :
    Claimed c (p.ht c.val) c.val y := by
  obtain ⟨h1,h2⟩ := shift_alt hy h
  exact ⟨rfl,by omega,by omega⟩

/-- In the second phase the new s stripe starts at a+1, not at its old top. -/
def protection (phaseB : Bool) (p : Pos) (t s a b mask c : Nat) : Nat :=
  (if c = t ∨ mask.testBit c = true then alt <<< (p.ht c + 1) else 0) |||
  (if c = s then
    if phaseB then (((2^64 : Nat) - 1) <<< b) ||| (alt <<< (a + 1))
    else (((2^64 : Nat) - 1) <<< a) ||| (alt <<< (p.ht c + 1))
   else 0)

theorem protection_sound {p : Pos} {t s c : Fin 5} {a b mask y : Nat} {phaseB : Bool}
    (hy : y < 64) (ha : p.ht s.val < a) (hao : (a - p.ht s.val) % 2 = 1)
    (hb : (protection phaseB p t.val s.val a b mask c.val).testBit y = true) :
    GateGuard phaseB p t s a b mask c.val y := by
  rw [protection, Nat.testBit_or, Bool.or_eq_true] at hb
  rcases hb with h | h
  · by_cases hc : c.val = t.val ∨ mask.testBit c.val = true
    · rw [if_pos hc] at h
      have hstripe := cover (p:=p) (c:=c) hy h
      have hother : CapTransfer.protect t (selected mask) c := hc.imp Fin.ext id
      cases phaseB
      · change LongThreat.Guard s a (CapTransfer.protect t (selected mask)) (fun q => p.ht q.val) c.val y
        exact Or.inl ⟨c,Or.inr hother,hstripe⟩
      · change CapTransfer.PostGuard t s a b (selected mask) (fun q => p.ht q.val) c.val y
        exact Or.inl ⟨c,hother,hstripe⟩
    · simp [hc] at h
  · by_cases hc : c.val = s.val
    · rw [if_pos hc] at h
      have hh : c = s := Fin.ext hc
      subst c
      cases phaseB
      · change ((((2^64 : Nat)-1) <<< a) ||| (alt <<< (p.ht s.val + 1))).testBit y = true at h
        rw [Nat.testBit_or, Bool.or_eq_true] at h
        change LongThreat.Guard s a (CapTransfer.protect t (selected mask)) (fun q => p.ht q.val) s.val y
        rcases h with h | h
        · exact Or.inr ⟨rfl,by exact_mod_cast shift_bar h⟩
        · exact Or.inl ⟨s,Or.inl rfl,cover (p:=p) (c:=s) hy h⟩
      · change ((((2^64 : Nat)-1) <<< b) ||| (alt <<< (a + 1))).testBit y = true at h
        rw [Nat.testBit_or, Bool.or_eq_true] at h
        change CapTransfer.PostGuard t s a b (selected mask) (fun q => p.ht q.val) s.val y
        right; refine ⟨rfl,?_⟩
        rcases h with h | h
        · exact Or.inl (by exact_mod_cast shift_bar h)
        · obtain ⟨h1,h2⟩ := shift_alt hy h
          exact Or.inr ⟨by omega, by change (y : Int)%2 = (p.ht s.val : Int)%2; omega⟩
    · simp [hc] at h

def openMask (h : Nat) (p : Pos) (m : Nat → Nat) (c : Nat) : Nat :=
  (2^h - 1) ^^^ ((p.bm c ||| m c) % 2^h)

def scan (h : Nat) (p : Pos) (m : Nat → Nat) : Bool :=
  force (openMask h p m 0) fun a => force (openMask h p m 1) fun b => force (openMask h p m 2) fun c =>
  force (openMask h p m 3) fun e => force (openMask h p m 4) fun f =>
  force (exceptionM h p 0) fun u => force (exceptionM h p 1) fun v => force (exceptionM h p 2) fun w =>
  force (exceptionM h p 3) fun z => force (exceptionM h p 4) fun z4 =>
  three a b c e u v w z && three b c e f v w z z4

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
    simp [live,hit,Nat.testBit_and,Nat.testBit_or,Nat.testBit_shiftRight,h0,h1,h2,h3,hg] at no
  all_goals simp_all

private theorem window_at {h : Nat} {p : Pos} {m : Nat → Nat} {x d : Nat} (hx : x ≤ 1) (hd : d ≤ 2)
    (hscan : scan h p m = true) :
    let f := openMask h p m; let g := exceptionM h p
    checkWindow d (f x) (f (x+1)) (f (x+2)) (f (x+3)) (g x) (g (x+1)) (g (x+2)) (g (x+3)) = true := by
  simp only [scan, force_eq, three, Bool.and_eq_true] at hscan
  rcases (by omega : x=0 ∨ x=1) with rfl | rfl <;>
    rcases (by omega : d=0 ∨ d=1 ∨ d=2) with rfl | rfl | rfl
  exacts [hscan.1.1.1,hscan.1.1.2,hscan.1.2,hscan.2.1.1,hscan.2.1.2,hscan.2.2]


private theorem open_of_clear {h : Nat} {p : Pos} (hw : p.WF h) {t s c : Fin 5} {a b mask y : Nat} {phaseB : Bool}
    (hy : y < h) (hh : h ≤ 64)
    (ha : p.ht s.val < a) (hao : (a - p.ht s.val) % 2 = 1)
    (hn : ¬ (cellAtInt h p.toBoard c.val y = some .black ∨
      GateGuard phaseB p t s a b mask c.val y)) :
    (openMask h p (protection phaseB p t.val s.val a b mask) c.val).testBit y = true := by
  have hbb : (p.bm c.val).testBit y = false := by
    cases hb : (p.bm c.val).testBit y with
    | false => rfl
    | true =>
      exfalso; apply hn; left; apply cellBlack_sound hw
      simp [cellBlack, hb, c.isLt, hy]
  have hgg : (protection phaseB p t.val s.val a b mask c.val).testBit y = false := by
    cases hg : (protection phaseB p t.val s.val a b mask c.val).testBit y with
    | false => rfl
    | true => exact (hn (Or.inr (protection_sound (by omega) ha hao hg))).elim
  simp [openMask, Nat.testBit_xor,Nat.testBit_two_pow_sub_one,Nat.testBit_mod_two_pow,
    Nat.testBit_or,hy,hbb,hgg]

theorem scan_sound {h : Nat} {p : Pos} (hw : p.WF h) (hh : h ≤ 64)
    {t s c : Fin 5} {a b mask r : Nat} {phaseB : Bool}
    (ha : p.ht s.val < a) (hao : (a - p.ht s.val) % 2 = 1)
    (hs : scan h p (protection phaseB p t.val s.val a b mask) = true)
    (he : (excB p c.val r || potB h p c.val r) = true) :
    CapTransfer.WindowCheck phaseB h p t s a b mask c r := by
  intro d i
  by_contra hn
  have bad (j : Fin 4) :
      let x := (c.val : Int) - (i : Int) * 1 + (j : Int) * 1
      let y := (r : Int) - (i : Int) * dyOf d.val + (j : Int) * dyOf d.val
      ¬ (cellAtInt h p.toBoard x y = some .black ∨
        GateGuard phaseB p t s a b mask x y ∨
        ¬ (0 ≤ x ∧ x < 5 ∧ 0 ≤ y ∧ y < (h : Int))) := by dsimp only; intro hj; exact hn ⟨j,hj⟩
  have coord (j : Fin 4) :
      let x := (c.val : Int) - (i : Int) * 1 + (j : Int) * 1
      let y := (r : Int) - (i : Int) * dyOf d.val + (j : Int) * dyOf d.val
      0 ≤ x ∧ x < 5 ∧ 0 ≤ y ∧ y < (h : Int) := by
    by_contra hb; exact bad j (Or.inr (Or.inr hb))
  have h0 := coord 0
  have h3 := coord 3
  dsimp only at h0 h3
  simp only [Fin.val_zero, Nat.cast_zero, zero_mul, add_zero] at h0 h3
  have hi := i.isLt
  have hd := d.isLt
  have hic : i.val ≤ c.val := by omega
  have hx : c.val - i.val ≤ 1 := by omega
  have ds : d.val = 0 ∨ d.val = 1 ∨ d.val = 2 := by omega
  have hr : off d.val i.val ≤ r := by
    rcases ds with h | h | h <;> simp [off,dyOf,h] at * <;> omega
  apply window_contra (f := openMask h p (protection phaseB p t.val s.val a b mask)) (g := exceptionM h p) (k := r-off d.val i.val)
    (i := i.val) hi _ _ (window_at (d := d.val) hx (by omega) hs)
  · intro j
    have hj := j.isLt
    have cj : c.val - i.val + j.val < 5 := by omega
    let z : Fin 5 := ⟨c.val - i.val + j.val,cj⟩
    let y := r-off d.val i.val + off d.val j.val
    have ex : (z.val : Int) = (c.val : Int) - (i : Int) * 1 + (j : Int) * 1 := by dsimp [z]; omega
    have ey : (y : Int) = (r : Int) - (i : Int) * dyOf d.val + (j : Int) * dyOf d.val := by
      dsimp [y]; rcases ds with h | h | h <;> simp [off,dyOf,h] at * <;> omega
    have b := bad j
    have v := coord j
    dsimp only at b v
    have hy : y < h := by omega
    apply open_of_clear (t := t) (s := s) (c := z) hw hy hh ha hao
    intro hh'
    rw [ex,ey] at hh'
    exact b (hh'.imp id Or.inl)
  · have e1 : c.val-i.val+i.val = c.val := by omega
    have e2 : r-off d.val i.val + off d.val i.val = r := by omega
    simpa only [e1,e2] using exc_bit (h := h) he


def BitBase (H : Nat) (p : Pos) (t s : Fin 5) (a b mask : Nat) : Prop :=
  H ≤ 64 ∧ H % 2 = 0 ∧ p.wfB H = true ∧ s ≠ t ∧
  ¬ selected mask t ∧ ¬ selected mask s ∧
  p.ht t.val % 2 = 1 ∧ p.ht s.val % 2 = 0 ∧
  (∀ q : Fin 5, selected mask q → p.ht q.val % 2 = 0) ∧
  p.ht s.val < a ∧ a < b ∧ b < H ∧
  (a - p.ht s.val) % 2 = 1 ∧ b % 2 = p.ht s.val % 2 ∧
  ∀ c : Fin 5, ntrB H p c.val = true

instance (H : Nat) (p : Pos) (t s : Fin 5) (a b mask : Nat) :
    Decidable (BitBase H p t s a b mask) := by unfold BitBase; infer_instance

def check (H : Nat) (p : Pos) (t s : Fin 5) (a b mask : Nat) (dA dB : Fin 3) (iA iB : Fin 4) : Bool :=
  decide (BitBase H p t s a b mask) &&
  LongThreat.tripleBits H p s a dA iA && LongThreat.tripleBits H p s b dB iB &&
  scan H p (protection false p t.val s.val a b mask) &&
  scan H p (protection true p t.val s.val a b mask)

theorem check_reference {H : Nat} {p : Pos} {t s : Fin 5} {a b mask : Nat}
    {dA dB : Fin 3} {iA iB : Fin 4} (hc : check H p t s a b mask dA dB iA iB = true) :
    CapTransfer.check H p t s a b mask dA dB iA iB = true := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨h0,hda⟩,hdb⟩,hsA⟩,hsB⟩ := hc
  obtain ⟨hh,he,hwp,hd,nt,ns,ho,hse,hq,ha,hab,hhb,hap,hbp,hntr⟩ := h0
  have hw := Pos.wfB_sound hwp
  have triple {r : Nat} {d : Fin 3} {i : Fin 4} (hb0 : LongThreat.tripleBits H p s r d i = true) :
      LongThreat.tripleCheck H p s r d i := by
    have hb1 := of_decide_eq_true hb0
    intro j hj
    exact cellBlack_sound hw (hb1 j hj)
  apply decide_eq_true
  refine ⟨he,hwp,hd,nt,ns,ho,hse,hq,ha,hab,hhb,hap,hbp,fun c hc => LongThreat.ntrB_sound' (hntr c) hc,
    triple hda,triple hdb,?_⟩
  intro c r hr
  have hex : (excB p c.val r.val || potB H p c.val r.val) = true := by
    rw [Bool.or_eq_true]; exact hr
  exact ⟨scan_sound hw hh ha hap hsA hex, scan_sound hw hh ha hap hsB hex⟩

/-- The post-transfer guard set is contained in the pre-transfer set, not
    their union. This implication preserves the same guarding cell. -/
theorem post_guard_to_pre {p : Pos} {t s : Fin 5} {a b mask : Nat} {x y : Int}
    (hab : a < b) (h : GateGuard true p t s a b mask x y) :
    GateGuard false p t s a b mask x y := by
  change CapTransfer.PostGuard t s a b (selected mask) (fun q => p.ht q.val) x y at h
  change LongThreat.Guard s a (CapTransfer.protect t (selected mask)) (fun q => p.ht q.val) x y
  rcases h with ⟨q,hq,hc⟩ | ⟨hs,hb | ⟨ha,_⟩⟩
  · exact Or.inl ⟨q,Or.inr hq,hc⟩
  · exact Or.inr ⟨hs,by omega⟩
  · exact Or.inr ⟨hs,ha⟩

theorem post_window_to_pre {H : Nat} {p : Pos} {t s c : Fin 5} {a b mask r : Nat}
    (hab : a < b) (h : CapTransfer.WindowCheck true H p t s a b mask c r) :
    CapTransfer.WindowCheck false H p t s a b mask c r := by
  intro d i
  obtain ⟨j,hj⟩ := h d i
  exact ⟨j,hj.imp id (fun hr => hr.imp (post_guard_to_pre hab) id)⟩

/-- Runtime gate: the stronger post mask alone certifies both phases. -/
def checkPost (H : Nat) (p : Pos) (t s : Fin 5) (a b mask : Nat)
    (dA dB : Fin 3) (iA iB : Fin 4) : Bool :=
  decide (BitBase H p t s a b mask) &&
  LongThreat.tripleBits H p s a dA iA && LongThreat.tripleBits H p s b dB iB &&
  scan H p (protection true p t.val s.val a b mask)

theorem checkPost_reference {H : Nat} {p : Pos} {t s : Fin 5} {a b mask : Nat}
    {dA dB : Fin 3} {iA iB : Fin 4} (hc : checkPost H p t s a b mask dA dB iA iB = true) :
    CapTransfer.check H p t s a b mask dA dB iA iB = true := by
  simp only [checkPost, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨h0,hda⟩,hdb⟩,hsB⟩ := hc
  obtain ⟨hh,he,hwp,hd,nt,ns,ho,hse,hq,ha,hab,hhb,hap,hbp,hntr⟩ := h0
  have hw := Pos.wfB_sound hwp
  have triple {r : Nat} {d : Fin 3} {i : Fin 4} (hb0 : LongThreat.tripleBits H p s r d i = true) :
      LongThreat.tripleCheck H p s r d i := by
    have hb1 := of_decide_eq_true hb0
    intro j hj
    exact cellBlack_sound hw (hb1 j hj)
  apply decide_eq_true
  refine ⟨he,hwp,hd,nt,ns,ho,hse,hq,ha,hab,hhb,hap,hbp,fun c hc => LongThreat.ntrB_sound' (hntr c) hc,
    triple hda,triple hdb,?_⟩
  intro c r hr
  have hex : (excB p c.val r.val || potB H p c.val r.val) = true := by
    rw [Bool.or_eq_true]; exact hr
  have hpost := scan_sound hw hh ha hap hsB hex
  exact ⟨post_window_to_pre hab hpost, hpost⟩

theorem checkPost_leaf {H : Nat} {p : Pos} {t s : Fin 5} {a b mask : Nat}
    {dA dB : Fin 3} {iA iB : Fin 4} (hc : checkPost H p t s a b mask dA dB iA iB = true) :
    CapTransfer.L H p.toBoard :=
  CapTransfer.check_leaf (checkPost_reference hc)

theorem check_leaf {H : Nat} {p : Pos} {t s : Fin 5} {a b mask : Nat}
    {dA dB : Fin 3} {iA iB : Fin 4} (hc : check H p t s a b mask dA dB iA iB = true) :
    CapTransfer.L H p.toBoard :=
  CapTransfer.check_leaf (check_reference hc)

#print axioms check_reference
#print axioms checkPost_reference
#print axioms checkPost_leaf
#print axioms check_leaf
end C4W5.CapFast
