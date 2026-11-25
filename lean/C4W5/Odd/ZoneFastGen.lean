import C4W5.Odd.RealGen

/-!
# Color-Polymorphic Parity-Unified Fast Zone Certificate Checker (`ZoneFastGen`)

Connects `ZoneGen.zone_safeL_gen` (`C4W5.Theory.ZoneGen`) and `ClaimLeafBridge` to compact
64-bit-scale `CTree` certificates (`FastKey`) and bitboard leaf pruning (`ClaimBitsGen`), providing:
1. `zone_safeP_of_tree` — labeled pruned zone-game certificates (`zmemG`, O(log N) range lookup)
2. `zone_safeP_of_explicit_tree` — unlabeled explicit-controller zone sets (`zumemG`, **0 reply bytes**)

Zero `sorry`, zero custom axioms.
-/

namespace C4W5Gen
open Connect4 (Player opponent)
open Connect4.NarrowBoards
open C4W5

set_option linter.deprecated false

/-! ## Bridging `Lab5` to `LabG` -/

def natLabG (n : Nat) : LabG :=
  if n = 0 then .low else if n = 1 then .odd else .dead

def Lab5.fnG (l : Lab5) : Fin 5 → LabG :=
  fun c => natLabG (l.get c.val)

theorem Lab5.fnG_set (l : Lab5) (c : Fin 5) (v : Nat) :
    (l.set c.val v).fnG = Function.update l.fnG c (natLabG v) := by
  funext d
  fin_cases c <;> fin_cases d <;> simp [Lab5.fnG, Lab5.set, Lab5.get, Function.update]

theorem natLabG_dead {n : Nat} (h : 2 ≤ n) : natLabG n = .dead := by
  unfold natLabG; rw [if_neg (by omega), if_neg (by omega)]

theorem Lab5.allDeadG_sound {l : Lab5} (h : l.allDead = true) (d : Fin 5) :
    l.fnG d = .dead := by
  unfold Lab5.allDead at h
  simp only [Bool.and_eq_true, Nat.ble_eq] at h
  obtain ⟨⟨⟨⟨a0, a1⟩, a2⟩, a3⟩, a4⟩ := h
  fin_cases d <;> exact natLabG_dead (by assumption)

/-! ## Color-Polymorphic Zone Step Checker -/

def zOutG (K : Nat) (me : Player) (dest : Pos → Lab5 → Bool)
    (p : Pos) (l : Lab5) (e : Nat) : Bool :=
  force (l.get e) fun le =>
  if le = 0 then
    if p.ht e < K then forceP (p.push e me) fun p2 => dest p2 l else dest p (l.set e 1)
  else if le = 1 then dest p (l.set e 2) else false

def zWinG (K : Nat) (me : Player) (p : Pos) (l : Lab5) (e : Nat) : Bool :=
  if l.get e = 0 then
    if p.ht e < K then forceP (p.push e me) fun p2 => p2.hasFourQ me else false
  else false

def zColG (K : Nat) (me : Player) (dest : Pos → Lab5 → Bool)
    (lowReply capReply : Pos → Lab5 → Nat → Nat) (p : Pos) (l : Lab5) (c : Nat) : Bool :=
  force (l.get c) fun lc =>
  if lc = 0 then
    if p.ht c < K then
      forceP (p.push c (opponent me)) fun p1 =>
        !p1.hasFourQ (opponent me) &&
        (force (lowReply p1 l c % 5) fun e =>
          zWinG K me p1 l e || ((e == c || Nat.ble (p.ht c + 5) K) && zOutG K me dest p1 l e))
    else dest p (l.set c 2)
  else if lc = 1 then
    let l1 := l.set c 2
    l1.allDead ||
      (force (capReply p l1 c % 5) fun e => zWinG K me p l1 e || zOutG K me dest p l1 e)
  else true

def stepOKZG (K : Nat) (me : Player) (dest : Pos → Lab5 → Bool)
    (lowReply capReply : Pos → Lab5 → Nat → Nat) (p : Pos) (l : Lab5) : Bool :=
  p.wfB K &&
  zColG K me dest lowReply capReply p l 0 &&
  zColG K me dest lowReply capReply p l 1 &&
  zColG K me dest lowReply capReply p l 2 &&
  zColG K me dest lowReply capReply p l 3 &&
  zColG K me dest lowReply capReply p l 4

/-! ## Step Soundness (`stepOKZG` → `ZoneCert2P`) -/

section
variable {K : Nat} {me : Player} {J : Board 5 → (Fin 5 → LabG) → Prop}
  {dest : Pos → Lab5 → Bool}

private theorem zOutG_sound (hd : ∀ q l', dest q l' = true → J q.toBoard l'.fnG)
    {p : Pos} (hw : p.WF K) {l : Lab5} {e : Fin 5}
    (h : zOutG K me dest p l e.val = true) :
    DefOut me K J p.toBoard l.fnG e := by
  unfold zOutG at h
  rw [force_eq] at h
  have hht := (hw e.val).2
  by_cases h0 : l.get e.val = 0
  · rw [if_pos h0] at h
    have hl : l.fnG e = .low := by simp [Lab5.fnG, natLabG, h0]
    by_cases hlt : p.ht e.val < K
    · rw [if_pos hlt, forceP_eq] at h
      have hj := hd _ _ h
      rw [Pos.toBoard_push hw] at hj
      exact Or.inl ⟨hl, by rw [Pos.height]; exact hlt, hj⟩
    · rw [if_neg hlt] at h
      have hj := hd _ _ h
      rw [Lab5.fnG_set] at hj
      exact Or.inr (Or.inl ⟨hl, by rw [Pos.height]; omega, hj⟩)
  · rw [if_neg h0] at h
    by_cases h1 : l.get e.val = 1
    · rw [if_pos h1] at h
      have hl : l.fnG e = .odd := by simp [Lab5.fnG, natLabG, h1]
      have hj := hd _ _ h
      rw [Lab5.fnG_set] at hj
      exact Or.inr (Or.inr ⟨hl, hj⟩)
    · rw [if_neg h1] at h; exact Bool.noConfusion h

private theorem zWinG_sound {p : Pos} (hw : p.WF K) {l : Lab5} {e : Fin 5}
    (h : zWinG K me p l e.val = true) :
    DefWin me K p.toBoard l.fnG := by
  unfold zWinG at h
  by_cases h0 : l.get e.val = 0
  · rw [if_pos h0] at h
    by_cases hlt : p.ht e.val < K
    · rw [if_pos hlt, forceP_eq, Pos.hasFourQ_eq] at h
      refine ⟨e, by simp [Lab5.fnG, natLabG, h0], by rw [Pos.height]; exact hlt, ?_⟩
      rw [← Pos.toBoard_push hw]
      exact (hasFourF_iff (Pos.WF_push hw e me hlt) _).mp h
    · rw [if_neg hlt] at h; exact Bool.noConfusion h
  · rw [if_neg h0] at h; exact Bool.noConfusion h

private theorem zColG_sound (hd : ∀ q l', dest q l' = true → J q.toBoard l'.fnG)
    {lowReply capReply : Pos → Lab5 → Nat → Nat}
    {p : Pos} (hw : p.WF K) {l : Lab5} (c : Fin 5)
    (h : zColG K me dest lowReply capReply p l c.val = true) :
    (l.fnG c = .low → (p.toBoard c).length < K →
      ¬ HasFour K (play p.toBoard c (opponent me)) (opponent me) ∧
      (DefWin me K (play p.toBoard c (opponent me)) l.fnG ∨
        ∃ e, (e = c ∨ (p.toBoard c).length + 5 ≤ K) ∧
          DefOut me K J (play p.toBoard c (opponent me)) l.fnG e)) ∧
    (l.fnG c = .low → (p.toBoard c).length = K →
      J p.toBoard (Function.update l.fnG c .dead)) ∧
    (l.fnG c = .odd → (∀ d, Function.update l.fnG c .dead d = .dead) ∨
      DefWin me K p.toBoard (Function.update l.fnG c .dead) ∨
      ∃ e, DefOut me K J p.toBoard (Function.update l.fnG c .dead) e) := by
  unfold zColG at h
  rw [force_eq] at h
  have hfn : l.fnG c = natLabG (l.get c.val) := rfl
  have hupd : (l.set c.val 2).fnG = Function.update l.fnG c .dead := by
    rw [Lab5.fnG_set]; rfl
  by_cases h0 : l.get c.val = 0
  · rw [if_pos h0] at h
    refine ⟨fun _ hlt => ?_, fun _ heq => ?_, fun hodd => ?_⟩
    · rw [Pos.height] at hlt
      rw [if_pos hlt, forceP_eq, Bool.and_eq_true, Bool.not_eq_true',
          Pos.hasFourQ_eq, force_eq, Bool.or_eq_true] at h
      obtain ⟨hnf, hrest⟩ := h
      have hw1 := Pos.WF_push hw c (opponent me) hlt
      have hb1 := Pos.toBoard_push hw c (opponent me)
      refine ⟨?_, ?_⟩
      · intro hf
        rw [← hb1, ← hasFourF_iff hw1, hnf] at hf
        exact Bool.noConfusion hf
      · rw [← hb1]
        let ef : Fin 5 := ⟨lowReply (p.push c.val (opponent me)) l c.val % 5, Nat.mod_lt _ (by decide)⟩
        rcases hrest with hwin | h_and
        · exact Or.inl (zWinG_sound hw1 (e := ef) hwin)
        · rw [Bool.and_eq_true] at h_and
          obtain ⟨hmust, hout⟩ := h_and
          refine Or.inr ⟨ef, ?_, zOutG_sound hd hw1 hout⟩
          rw [Pos.height]
          rw [Bool.or_eq_true] at hmust
          rcases hmust with he | hle
          · left; apply Fin.ext
            show lowReply (p.push c.val (opponent me)) l c.val % 5 = c.val
            exact beq_iff_eq.mp he
          · right; rw [Nat.ble_eq] at hle; exact hle
    · rw [Pos.height] at heq
      rw [if_neg (by omega)] at h
      have hj := hd _ _ h
      rwa [hupd] at hj
    · rw [hfn, h0] at hodd; simp [natLabG] at hodd
  · rw [if_neg h0] at h
    refine ⟨fun hlow => ?_, fun hlow => ?_, fun hodd => ?_⟩
    · rw [hfn] at hlow; unfold natLabG at hlow; rw [if_neg h0] at hlow; split at hlow <;> cases hlow
    · rw [hfn] at hlow; unfold natLabG at hlow; rw [if_neg h0] at hlow; split at hlow <;> cases hlow
    · by_cases h1 : l.get c.val = 1
      · rw [if_pos h1] at h
        dsimp only at h
        simp only [Bool.or_eq_true, force_eq] at h
        rw [← hupd]
        let ef : Fin 5 := ⟨capReply p (l.set c.val 2) c.val % 5, Nat.mod_lt _ (by decide)⟩
        rcases h with hall | hwin | hout
        · exact Or.inl (Lab5.allDeadG_sound hall)
        · exact Or.inr (Or.inl (zWinG_sound hw (e := ef) hwin))
        · exact Or.inr (Or.inr ⟨ef, zOutG_sound hd hw hout⟩)
      · rw [hfn] at hodd; unfold natLabG at hodd; rw [if_neg h0, if_neg h1] at hodd; cases hodd

theorem stepOKZG_sound (hd : ∀ q l', dest q l' = true → J q.toBoard l'.fnG)
    {lowReply capReply : Pos → Lab5 → Nat → Nat}
    {p : Pos} {l : Lab5}
    (h : stepOKZG K me dest lowReply capReply p l = true) (c : Fin 5) :
    (l.fnG c = .low → (p.toBoard c).length < K →
      ¬ HasFour K (play p.toBoard c (opponent me)) (opponent me) ∧
      (DefWin me K (play p.toBoard c (opponent me)) l.fnG ∨
        ∃ e, (e = c ∨ (p.toBoard c).length + 5 ≤ K) ∧
          DefOut me K J (play p.toBoard c (opponent me)) l.fnG e)) ∧
    (l.fnG c = .low → (p.toBoard c).length = K →
      J p.toBoard (Function.update l.fnG c .dead)) ∧
    (l.fnG c = .odd → (∀ d, Function.update l.fnG c .dead d = .dead) ∨
      DefWin me K p.toBoard (Function.update l.fnG c .dead) ∨
      ∃ e, DefOut me K J p.toBoard (Function.update l.fnG c .dead) e) := by
  unfold stepOKZG at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hwf, h0⟩, h1⟩, h2⟩, h3⟩, h4⟩ := h
  have hw := Pos.wfB_sound hwf
  fin_cases c
  · exact zColG_sound hd hw 0 h0
  · exact zColG_sound hd hw 1 h1
  · exact zColG_sound hd hw 2 h2
  · exact zColG_sound hd hw 3 h3
  · exact zColG_sound hd hw 4 h4

end

/-! ## Root Discipline Checker (`discBG` → `DiscEP ∧ ∀ c, TColP`) -/

def colDiscG (opp : Player) (K b h : Nat) : Bool :=
  let o := maskOf opp b h
  Nat.blt (o &&& (o <<< 1 ||| 1)) (2 ^ (K - 3)) &&
  ((!(h == 0) && (maskOf (opponent opp) b h).testBit (h - 1)) || Nat.ble (h + 4) K)

def discBG (opp : Player) (K : Nat) (p : Pos) : Bool :=
  Nat.ble 4 K &&
  colDiscG opp K p.b0 p.h0 && colDiscG opp K p.b1 p.h1 &&
  colDiscG opp K p.b2 p.h2 && colDiscG opp K p.b3 p.h3 &&
  colDiscG opp K p.b4 p.h4

private theorem colDiscG_sound {opp : Player} {K b h : Nat} (hK : 4 ≤ K) (hb : b < 2 ^ h)
    (hd : colDiscG opp K b h = true) :
    (∀ r, stone (decC h b) r = some opp → (r = 0 ∨ stone (decC h b) (r - 1) = some opp) →
      r + 4 ≤ K) ∧
    ((h = 0 ∨ stone (decC h b) (h - 1) = some opp) → h + 4 ≤ K) := by
  unfold colDiscG at hd
  dsimp only at hd
  simp only [Bool.and_eq_true, Nat.blt_eq, Bool.or_eq_true, Nat.ble_eq,
    Bool.not_eq_true', beq_eq_false_iff_ne] at hd
  obtain ⟨hexc, htop⟩ := hd
  constructor
  · intro r h1 h2
    by_contra hcon
    have h10 : (1 : Nat).testBit 0 = true := by decide
    have hbit : (maskOf opp b h &&& (maskOf opp b h <<< 1 ||| 1)).testBit r = true := by
      rw [Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftLeft,
        (testBit_maskOf hb opp r).mpr h1]
      rcases h2 with rfl | h2
      · simp [h10]
      · by_cases hr0 : r = 0
        · subst hr0; simp [h10]
        · simp [(testBit_maskOf hb opp (r - 1)).mpr h2, show 1 ≤ r by omega]
    have hf := testBit_false_of_lt hexc (show K - 3 ≤ r by omega)
    rw [hf] at hbit
    exact Bool.noConfusion hbit
  · intro h1
    rcases htop with ⟨hne, hbit⟩ | hle
    · exfalso
      rcases h1 with h0 | hopp
      · exact hne h0
      · have hdef := (testBit_maskOf hb (opponent opp) (h - 1)).mp hbit
        rw [hopp] at hdef
        exact ne_opponent opp (Option.some.inj hdef)
    · exact hle

theorem discBG_sound {opp : Player} {K H : Nat} {p : Pos} (hw : p.WF K)
    (hd : discBG opp K p = true) :
    DiscEP opp K p.toBoard ∧ ∀ c, TColP opp K H p.toBoard c := by
  unfold discBG at hd
  simp only [Bool.and_eq_true, Nat.ble_eq] at hd
  obtain ⟨⟨⟨⟨⟨hK, d0⟩, d1⟩, d2⟩, d3⟩, d4⟩ := hd
  have hcol : ∀ c : Fin 5, colDiscG opp K (p.bm c.val) (p.ht c.val) = true := by
    intro c; fin_cases c <;> assumption
  constructor
  · intro c r hexc
    exact (colDiscG_sound hK (hw c.val).1 (hcol c)).1 r hexc.1 hexc.2
  · intro c _ htop
    have hc := (colDiscG_sound hK (hw c.val).1 (hcol c)).2
    simp only [Pos.toBoard, decC_length] at htop
    rw [Pos.height]; exact hc htop

private theorem wf_monoG {K H : Nat} {p : Pos} (hw : p.WF K) (hKH : K ≤ H) : p.WF H :=
  fun c => ⟨(hw c).1, le_trans (hw c).2 hKH⟩

/-! ## Shared Concrete-Root Lifting -/

private theorem allLowOfWF {K H : Nat} {p : Pos} (hw : p.WF K) :
    labsG H K p.toBoard = fun _ => .low := by
  funext c
  have hc : (p.toBoard c).length ≤ K := by
    rw [Pos.height]
    exact (hw c.val).2
  simp only [labsG, labOfG, if_pos hc]

/-- A root decoded entirely below the cut has the concrete low labels; the proof
    opening and this geometric fact are common to both certificate formats. -/
private theorem checkedZoneRoot {K H : Nat} {me : Player}
    (hpar : K % 2 = H % 2) (hKH : K + 2 ≤ H)
    {Leaf : Nat → Board 5 → Prop} (hLeaf : ZoneLeafSound me Leaf)
    {I : Board 5 → (Fin 5 → LabG) → Prop}
    (hcert : ZoneCert2P me K I (fun L ℓ => I L ℓ ∨ Leaf K L))
    {ms : List (Fin 5)} {q : Pos}
    (hr : Pos.run K Pos.empty .black ms = some q)
    (ht : q.total % 2 = turnParity (opponent me))
    (hd : discBG (opponent me) K q = true)
    (hroot : I q.toBoard (fun _ => .low)) :
    SafeP H me (playList (emptyBoard 5) .black ms) := by
  obtain ⟨hboard, hnw, hnb, hwK⟩ := root_of_run' hr
  rw [← hboard]
  have hwH : q.WF H := wf_monoG hwK (by omega)
  have hnoneK (pl : Player) : ¬ HasFour K q.toBoard pl := by
    cases pl with
    | black => exact hnb
    | white => exact hnw
  have hnoneH (pl : Player) : ¬ HasFour H q.toBoard pl := by
    intro hf
    have hbits := (hasFourF_iff hwH pl).mpr hf
    exact hnoneK pl ((hasFourF_iff hwK pl).mp hbits)
  obtain ⟨hE, hT⟩ := discBG_sound (H := H) hwK hd
  have htrunc : truncG K q.toBoard = q.toBoard := by
    funext c
    simp only [truncG]
    exact List.take_of_length_le (by rw [Pos.height]; exact (hwK c.val).2)
  apply zone_safeL_gen hpar hKH hLeaf hcert
  refine ⟨toMove_of_totalParity ht, hnoneH _, hnoneH _, hE, hT, ?_, Or.inl ?_⟩
  · intro c
    rw [Pos.height]
    exact (hwH c.val).2
  · simpa only [htrunc, allLowOfWF (H := H) hwK] using hroot

private theorem zeroLab5 : (⟨0, 0, 0, 0, 0⟩ : Lab5).fnG = fun _ => .low := by
  funext c
  fin_cases c <;> rfl

/-! ## Concrete Zone Tree Wrappers: Labeled (`zmemG`) and Unlabeled Explicit (`zumemG`) -/

def zoneDest (t : CTree) (leafB : Pos → Bool) (q : Pos) (lq : Lab5) : Bool :=
  zmemG t q lq || leafB q

def zoneCheckW (K : Nat) (me : Player) (t : CTree) (leafB : Pos → Bool) (w : Nat) : Bool :=
  withUnpack9 (w / 3125 / 243) fun pos =>
    let lb := unpackL (w / 3125 % 243)
    let rep := w % 3125
    stepOKZG K me (zoneDest t leafB) (fun _ _ c => replyOf rep c) (fun _ _ c => replyOf rep c) pos lb

def ZIG (t : CTree) (L : Board 5) (ℓ : Fin 5 → LabG) : Prop :=
  ∃ w, TIn t w ∧ L = (unpack9 (w / 3125 / 243)).toBoard ∧ ℓ = (unpackL (w / 3125 % 243)).fnG

theorem zone_safeP_of_tree {K H : Nat} {me : Player}
    (hpar : K % 2 = H % 2) (hKH : K + 2 ≤ H)
    {Leaf : Nat → Board 5 → Prop} (hLeaf : ZoneLeafSound me Leaf)
    {leafB : Pos → Bool} (hleafB : ∀ q, leafB q = true → Leaf K q.toBoard)
    (t : CTree) (ms : List (Fin 5)) (q : Pos)
    (hr : Pos.run K Pos.empty .black ms = some q)
    (hall : treeAllOK (zoneCheckW K me t leafB) t = true)
    (ht : q.total % 2 = turnParity (opponent me))
    (hd : discBG (opponent me) K q = true)
    (hmem : zmemG t q ⟨0, 0, 0, 0, 0⟩ = true) :
    SafeP H me (playList (emptyBoard 5) .black ms) := by
  refine checkedZoneRoot hpar hKH hLeaf (I := ZIG t) ?_ hr ht hd ?_
  · intro L ℓ hstate c
    obtain ⟨w, hnode, rfl, rfl⟩ := hstate
    have hcheck := treeAllOK_sound hall hnode
    simp only [zoneCheckW, withUnpack9_eq] at hcheck
    refine stepOKZG_sound (J := fun L ℓ => ZIG t L ℓ ∨ Leaf K L) ?_ hcheck c
    intro q' l' hdest
    change (zmemG t q' l' || leafB q') = true at hdest
    rw [Bool.or_eq_true] at hdest
    rcases hdest with hmember | hleaf
    · obtain ⟨w', hin', hp', hl'⟩ := zmemG_sound hmember
      exact Or.inl ⟨w', hin', by rw [hp'], by rw [hl']⟩
    · exact Or.inr (hleafB q' hleaf)
  · obtain ⟨w, hin, hp, hl⟩ := zmemG_sound hmem
    refine ⟨w, hin, ?_, ?_⟩
    · rw [hp]
    · rw [hl, zeroLab5]

def zoneUDest (t : CTree) (leafB : Pos → Bool) (q : Pos) (lq : Lab5) : Bool :=
  zumemG t q lq || leafB q

def zoneUCheckW (K : Nat) (me : Player) (t : CTree) (leafB : Pos → Bool)
    (lowReply capReply : Pos → Lab5 → Nat → Nat) (w : Nat) : Bool :=
  withUnpack9 (w / 243) fun pos =>
    let lb := unpackL (w % 243)
    stepOKZG K me (zoneUDest t leafB) lowReply capReply pos lb

def ZUIG (t : CTree) (L : Board 5) (ℓ : Fin 5 → LabG) : Prop :=
  ∃ w, TIn t w ∧ L = (unpack9 (w / 243)).toBoard ∧ ℓ = (unpackL (w % 243)).fnG

theorem zone_safeP_of_explicit_tree {K H : Nat} {me : Player}
    (hpar : K % 2 = H % 2) (hKH : K + 2 ≤ H)
    {Leaf : Nat → Board 5 → Prop} (hLeaf : ZoneLeafSound me Leaf)
    {leafB : Pos → Bool} (hleafB : ∀ q, leafB q = true → Leaf K q.toBoard)
    (lowReply capReply : Pos → Lab5 → Nat → Nat)
    (t : CTree) (ms : List (Fin 5)) (q : Pos)
    (hr : Pos.run K Pos.empty .black ms = some q)
    (hall : treeAllOK (zoneUCheckW K me t leafB lowReply capReply) t = true)
    (ht : q.total % 2 = turnParity (opponent me))
    (hd : discBG (opponent me) K q = true)
    (hmem : zumemG t q ⟨0, 0, 0, 0, 0⟩ = true) :
    SafeP H me (playList (emptyBoard 5) .black ms) := by
  refine checkedZoneRoot hpar hKH hLeaf (I := ZUIG t) ?_ hr ht hd ?_
  · intro L ℓ hstate c
    obtain ⟨w, hnode, rfl, rfl⟩ := hstate
    have hcheck := treeAllOK_sound hall hnode
    simp only [zoneUCheckW, withUnpack9_eq] at hcheck
    refine stepOKZG_sound (J := fun L ℓ => ZUIG t L ℓ ∨ Leaf K L) ?_ hcheck c
    intro q' l' hdest
    change (zumemG t q' l' || leafB q') = true at hdest
    rw [Bool.or_eq_true] at hdest
    rcases hdest with hmember | hleaf
    · obtain ⟨w', hin', hp', hl'⟩ := zumemG_sound hmember
      exact Or.inl ⟨w', hin', by rw [hp'], by rw [hl']⟩
    · exact Or.inr (hleafB q' hleaf)
  · obtain ⟨w, hin, hp, hl⟩ := zumemG_sound hmem
    refine ⟨w, hin, ?_, ?_⟩
    · rw [hp]
    · rw [hl, zeroLab5]

#print axioms zone_safeP_of_tree
#print axioms zone_safeP_of_explicit_tree

end C4W5Gen
