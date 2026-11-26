import MPC.Invariants.ForwardPotential
import Mathlib.Tactic.IntervalCases
/-!
# MPC.Pieces.GoldTypeMove

Gold-type pieces (gold, promoted silver, promoted knight, promoted lance, tokin)
never make a discovered check in a periodic trace.

A board move of a non-glaring piece goes between two half-lines from the enemy
king that are neither equal nor opposite. Both ends are non-glaring
(Lemma 2.8), and a gold-type piece keeps its kind. A step attack ignores
the board, so a non-glaring gold-type piece does not attack the enemy king by a
step from either end.

**Case analysis.** With `v` and `w` the two ends relative to the enemy king, both
on lines through it and not collinear with it, a gold step from `v` to `w` whose
ends do not attack the king goes forward (`gold_step_forward`). The paper lists
the move `(±1, 1) → (0, 2)`; the case analysis also finds `(±2, 0) → (±1, 1)`,
which goes forward too.

**Potential.** So every non-glaring move of a gold-type piece raises its owner's
forward rank (`forwardRank_lt_of_nonGlaring_goldType_move_of_periodic`), and Part
4's potential lemma rules such moves out
(`not_nonGlaring_goldType_move_of_periodic`). In particular no gold-type piece is
moved by a discovered check (`not_openableMove_goldType_of_periodic`). No GameSeq
is used.
-/

namespace MPC

/-- The sign of the forward direction of `o` on the board's second coordinate. -/
def forwardSign (o : Player) : ℤ :=
  match o with
  | .sente => 1
  | .gote => -1

private theorem forwardRank_sub (o : Player) (src dst : Pos) :
    (forwardRank o dst : ℤ) - forwardRank o src = forwardSign o * (Pos.dirTo src dst).2 := by
  have h1 := src.2.isLt
  have h2 := dst.2.isLt
  cases o <;> simp only [forwardRank, forwardSign, Pos.dirTo] <;>
    push_cast [Nat.cast_sub (by omega : src.2.val ≤ 8), Nat.cast_sub (by omega : dst.2.val ≤ 8)] <;>
    ring

/-- Gold-type pieces step like a gold and do not slide. -/
theorem PieceType.goldType_dirs {pt : PieceType} (h : pt.movesLikeGold = true) :
    pt.stepDirs = PieceType.gold.stepDirs ∧ pt.slideDirs = [] := by
  cases pt <;> simp_all [PieceType.movesLikeGold, PieceType.stepDirs, PieceType.slideDirs]

/-- The case analysis: between two lines through the enemy king, not collinear
    with it, a gold step whose ends do not attack the king goes forward. Here `v`
    and `w` are the two ends relative to the king. -/
theorem gold_step_forward (o : Player) (v w : ℤ × ℤ)
    (hv : v.1 = 0 ∨ v.2 = 0 ∨ v.1 = v.2 ∨ v.1 = -v.2)
    (hw : w.1 = 0 ∨ w.2 = 0 ∨ w.1 = w.2 ∨ w.1 = -w.2)
    (hcross : v.1 * w.2 - v.2 * w.1 ≠ 0)
    (hs : ((w.1 - v.1, w.2 - v.2) : Dir) ∈ PieceType.gold.stepDirs.map (Dir.forPlayer · o))
    (hv' : ((-v.1, -v.2) : Dir) ∉ PieceType.gold.stepDirs.map (Dir.forPlayer · o))
    (hw' : ((-w.1, -w.2) : Dir) ∉ PieceType.gold.stepDirs.map (Dir.forPlayer · o)) :
    0 < forwardSign o * (w.2 - v.2) := by
  obtain ⟨v1, v2⟩ := v
  obtain ⟨w1, w2⟩ := w
  dsimp only at hv hw hcross hs hv' hw' ⊢
  obtain ⟨s1, hs1⟩ : ∃ s1, s1 = w1 - v1 := ⟨_, rfl⟩
  obtain ⟨s2, hs2⟩ : ∃ s2, s2 = w2 - v2 := ⟨_, rfl⟩
  have hcross' : v1 * s2 - v2 * s1 ≠ 0 := by
    intro h
    apply hcross
    rw [hs1, hs2] at h
    have e : v1 * w2 - v2 * w1 = v1 * (w2 - v2) - v2 * (w1 - v1) := by ring
    rw [e]
    exact h
  have hw1 : w1 = v1 + s1 := by omega
  have hw2 : w2 = v2 + s2 := by omega
  rw [← hs1, ← hs2] at hs
  subst hw1
  subst hw2
  -- A forward step is done. Otherwise both ends are next to the king, and one of
  -- them attacks it.
  cases o <;>
    simp only [PieceType.stepDirs, List.map_cons, List.map_nil, Dir.forPlayer, Dir.flip,
      List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at hs <;>
    rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp only [forwardSign] <;>
    first
    | omega
    | (have hb : -1 ≤ v1 ∧ v1 ≤ 1 ∧ -1 ≤ v2 ∧ v2 ≤ 1 := by omega
       obtain ⟨hb1, hb2, hb3, hb4⟩ := hb
       interval_cases v1 <;> interval_cases v2 <;>
         first | omega | exact absurd (by decide) hv' | exact absurd (by decide) hw')

/-- The two ends of a half-line point, relative to the start, lie on a line
    through it. -/
theorem OnRay.on_line {K P : Pos} {d : Dir} {a : ℤ} (h : OnRay K d a P) :
    P.toInt.1 - K.toInt.1 = 0 ∨ P.toInt.2 - K.toInt.2 = 0 ∨
      P.toInt.1 - K.toInt.1 = P.toInt.2 - K.toInt.2 ∨
      P.toInt.1 - K.toInt.1 = -(P.toInt.2 - K.toInt.2) := by
  obtain ⟨hd, _, hP⟩ := h
  rw [hP]
  dsimp only
  simp only [PieceType.stepDirs, List.mem_cons, List.not_mem_nil,
    or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega

/-- Points on two half-lines from `K` that are neither equal nor opposite are not
    collinear with `K`. -/
theorem OnRay.cross_ne_zero {K P Q : Pos} {d e : Dir} {a b : ℤ} (hP : OnRay K d a P)
    (hQ : OnRay K e b Q) (h1 : e ≠ d) (h2 : e ≠ (-d.1, -d.2)) :
    (P.toInt.1 - K.toInt.1) * (Q.toInt.2 - K.toInt.2) -
      (P.toInt.2 - K.toInt.2) * (Q.toInt.1 - K.toInt.1) ≠ 0 := by
  obtain ⟨hd, ha, hPe⟩ := hP
  obtain ⟨he, hb, hQe⟩ := hQ
  have key : ∀ d ∈ PieceType.king.stepDirs, ∀ e ∈ PieceType.king.stepDirs, e ≠ d →
      e ≠ (-d.1, -d.2) → d.1 * e.2 - d.2 * e.1 ≠ 0 := by decide
  have hde := key d hd e he h1 h2
  rw [hPe, hQe]
  dsimp only
  have e : (K.toInt.1 + a * d.1 - K.toInt.1) * (K.toInt.2 + b * e.2 - K.toInt.2) -
      (K.toInt.2 + a * d.2 - K.toInt.2) * (K.toInt.1 + b * e.1 - K.toInt.1) =
      (a * b) * (d.1 * e.2 - d.2 * e.1) := by ring
  rw [e]
  exact mul_ne_zero (mul_ne_zero (by omega) (by omega)) hde

/-- In board coordinates: a gold step between two half-lines from the enemy king
    `K` that are neither equal nor opposite, whose ends do not attack `K` by a gold
    step, raises the mover's forward rank. -/
theorem forwardRank_lt_of_gold_step_between_rays (o : Player) (K src dst : Pos) (d e : Dir)
    (a b : ℤ) (hsrc : OnRay K d a src) (hdst : OnRay K e b dst) (h1 : e ≠ d)
    (h2 : e ≠ (-d.1, -d.2))
    (hmove : Pos.dirTo src dst ∈ PieceType.gold.stepDirs.map (Dir.forPlayer · o))
    (hsK : Pos.dirTo src K ∉ PieceType.gold.stepDirs.map (Dir.forPlayer · o))
    (hdK : Pos.dirTo dst K ∉ PieceType.gold.stepDirs.map (Dir.forPlayer · o)) :
    forwardRank o src < forwardRank o dst := by
  have hsub := forwardRank_sub o src dst
  have key := gold_step_forward o (src.toInt.1 - K.toInt.1, src.toInt.2 - K.toInt.2)
    (dst.toInt.1 - K.toInt.1, dst.toInt.2 - K.toInt.2) hsrc.on_line hdst.on_line
    (hsrc.cross_ne_zero hdst h1 h2)
    (by
      convert hmove using 1
      simp only [Pos.dirTo, Pos.toInt]
      ext <;> dsimp only <;> ring)
    (by
      convert hsK using 2
      simp only [Pos.dirTo, Pos.toInt]
      ext <;> dsimp only <;> ring)
    (by
      convert hdK using 2
      simp only [Pos.dirTo, Pos.toInt]
      ext <;> dsimp only <;> ring)
  have e : (Pos.dirTo src dst).2 = (dst.toInt.2 - K.toInt.2) - (src.toInt.2 - K.toInt.2) := by
    simp only [Pos.dirTo, Pos.toInt]
    ring
  rw [e] at hsub
  dsimp only at key
  omega

namespace MoveTrace

/-- In a periodic trace satisfying the periodic-check premises, a board move of a non-glaring
    gold-type piece raises its owner's forward rank. -/
theorem forwardRank_lt_of_nonGlaring_goldType_move_of_periodic (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hr : tr.BoardMovesFollowCanMoveToOriented)
    (hp : tr.IsPeriodic) (i : Fin tr.len) (src dst : Pos) (promote : Bool) (p : Piece)
    (hm : tr.moves i = .boardMove src dst promote)
    (hpc : (tr.before i).board.grid src = some p)
    (hng : ¬ tr.GlaresAtEnemyKing kp i.castSucc src) (hpt : p.pieceType.movesLikeGold = true) :
    forwardRank p.owner src < forwardRank p.owner dst := by
  have hkp := tr.kingPos_eq_of_periodic kp ht hs hk hsafe h0 hc hr hp
  have hown : p.owner = (tr.before i).turn := by
    obtain ⟨piece, hpiece, ho⟩ := hs i src dst promote hm
    rw [hpc] at hpiece
    cases hpiece
    exact ho
  obtain ⟨hstep, hslide⟩ := PieceType.goldType_dirs hpt
  obtain ⟨d, e, a, b, hsrc, hdst, h1, h2⟩ :=
    tr.openable_move_rays_of_periodic kp ht hs hk hsafe h0 hc hr hp i src dst promote hm hng
  rw [← hown] at hsrc hdst
  -- The move is a gold step.
  have hmove : Pos.dirTo src dst ∈ PieceType.gold.stepDirs.map (Dir.forPlayer · p.owner) := by
    rcases hr i src dst promote p hm hpc with hst | ⟨sd, hsd, _⟩
    · rw [hstep] at hst
      exact hst
    · rw [hslide] at hsd
      exact absurd hsd (List.not_mem_nil)
  -- Neither end attacks the enemy king by a step.
  have hsK : Pos.dirTo src (kp 0 p.owner.opponent) ∉
      PieceType.gold.stepDirs.map (Dir.forPlayer · p.owner) := by
    intro h
    apply hng
    refine ⟨p, hpc, Or.inl ?_⟩
    rw [hkp i.castSucc, hstep]
    exact h
  have hdK : Pos.dirTo dst (kp 0 p.owner.opponent) ∉
      PieceType.gold.stepDirs.map (Dir.forPlayer · p.owner) := by
    intro h
    have hngd : ¬ tr.GlaresAtEnemyKing kp i.succ dst := fun hg =>
      hng (tr.glares_source_of_glares_destination_of_periodic kp ht hs hk hsafe h0 hc hr hp i
        src dst promote hm hg)
    apply hngd
    have hgrid := tr.boardMove_grid_dst_eq_of_not_glares_of_periodic kp ht hs hk hsafe h0 hc hr
      hp i src dst promote hm hng
    refine ⟨p, ?_, Or.inl ?_⟩
    · change (tr.after i).board.grid dst = some p
      rw [hgrid, hpc]
    · rw [hkp i.succ, hstep]
      exact h
  exact forwardRank_lt_of_gold_step_between_rays p.owner _ src dst d e a b hsrc hdst h1 h2
    hmove hsK hdK

/-- Under the same premises, no gold-type piece moves from a non-glaring square: it
    would raise the potential of its owner's forward ranks. -/
theorem not_nonGlaring_goldType_move_of_periodic (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hr : tr.BoardMovesFollowCanMoveToOriented)
    (hp : tr.IsPeriodic) (i : Fin tr.len) (src dst : Pos) (promote : Bool) (p : Piece)
    (hm : tr.moves i = .boardMove src dst promote)
    (hpc : (tr.before i).board.grid src = some p)
    (hng : ¬ tr.GlaresAtEnemyKing kp i.castSucc src) (hpt : p.pieceType.movesLikeGold = true) :
    False := by
  let P : Piece → Prop := fun x => x.owner = p.owner ∧ x.pieceType.movesLikeGold = true
  have hlt : ∀ j s d, tr.NonGlaringMoveOf kp P j s d →
      forwardRank p.owner s < forwardRank p.owner d := by
    rintro j s d ⟨pr, x, hmj, hxc, hxg, hxo, hxt⟩
    rw [← hxo]
    exact tr.forwardRank_lt_of_nonGlaring_goldType_move_of_periodic kp ht hs hk hsafe h0 hc hr
      hp j s d pr x hmj hxc hxg hxt
  have hmv : tr.NonGlaringMoveOf kp P i src dst := ⟨promote, p, hm, hpc, hng, rfl, hpt⟩
  have heq := tr.potential_move_eq_of_periodic kp ht hs hk hsafe h0 hc hr hp P
    (forwardRank p.owner) (fun j s d h => (hlt j s d h).le) i src dst hmv
  have := hlt i src dst hmv
  omega

/-- In a periodic mutual-check trace, no gold-type piece is moved by a discovered
    check. -/
theorem not_openableMove_goldType_of_periodic (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos) (hm : tr.MutualPerpetualCheck kp) (o : Player)
    (pt : PieceType) (hpt : pt.movesLikeGold = true) : ¬ tr.OpenableMoveBy kp o pt := by
  rintro ⟨i, src, dst, promote, _, hmv, hsrc, hng, _⟩
  exact tr.not_nonGlaring_goldType_move_of_periodic kp hm.transitions hm.sourcesOwned
    hm.kingsWellPlaced hm.ownKingSafe hm.initialOpponentSafe hm.checks hm.movementRules
    hm.periodic i src dst promote ⟨o, pt⟩ hmv hsrc hng hpt

end MoveTrace
end MPC
