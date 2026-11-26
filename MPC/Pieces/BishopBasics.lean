import MPC.Basic.Lemmas
import MPC.Pieces.RookDragonLemma
/-!
# MPC.Pieces.BishopBasics

What the earlier Parts leave for bishops and horses. Throughout,
the trace is a periodic mutual-check trace with Proposition 4.1 and the piece
counts.

- Only bishops and horses make discovered checks (`bishopHorse_of_openableMove`):
   and 4–7 exclude every other kind. A non-glaring board move is a
  discovered check (Lemma 2.4), so every non-glaring board move moves a bishop or a
  horse, and so does every openable piece, which leaves its square later
  (`bishopHorse_of_openable_of_periodic`).
- In every state each side has an openable bishop or horse: its discovered check
  (Proposition 4.1) moves one, and the number of openable ones is the same in every
  state. With the piece counts these two are all the bishops and horses on
  the board (`openable_of_bishopHorse_of_periodic`). In particular no bishop or horse
  glares.
- An openable bishop or horse stands on a rank or file half-line from its enemy
  king (`orth_ray_of_openable_of_periodic`). The piece glaring behind it
  (Proposition 3.3) is not a bishop or horse, so it does not slide diagonally.
- A non-glaring move of a bishop or horse goes between two points at the same
  distance `t` from the enemy king on perpendicular rank and file half-lines
  (`bishopEdge_of_nonGlaring_move_of_periodic`, `BishopEdge`). The move is
  diagonal: a horse's orthogonal step cannot join two such points.
-/

namespace MPC

/-- Two points at distance `t` from the enemy king on perpendicular rank and file
    half-lines, relative to the king: one on the rank, the other on the file. -/
def BishopEdge (t : ℤ) (v w : ℤ × ℤ) : Prop :=
  0 < t ∧ ((v.2 = 0 ∧ (v.1 = t ∨ v.1 = -t) ∧ w.1 = 0 ∧ (w.2 = t ∨ w.2 = -t)) ∨
    (v.1 = 0 ∧ (v.2 = t ∨ v.2 = -t) ∧ w.2 = 0 ∧ (w.1 = t ∨ w.1 = -t)))

/-- Bishops and horses slide diagonally. -/
theorem diag_of_bishopHorse_slideDir (pt : PieceType) (o : Player) (sd : Dir)
    (hpt : pt = .bishop ∨ pt = .horse) (h : sd ∈ pt.slideDirs.map (Dir.forPlayer · o)) :
    (sd.1 = 1 ∨ sd.1 = -1) ∧ (sd.2 = 1 ∨ sd.2 = -1) := by
  have key : ∀ x ∈ pt.slideDirs.map (Dir.forPlayer · o),
      (x.1 = 1 ∨ x.1 = -1) ∧ (x.2 = 1 ∨ x.2 = -1) := by
    rcases hpt with rfl | rfl <;> cases o <;> decide
  exact key sd h

/-- Bishops and horses step only along ranks and files, by one square. -/
theorem orth_of_bishopHorse_stepDir (pt : PieceType) (o : Player) (d : Dir)
    (hpt : pt = .bishop ∨ pt = .horse) (h : d ∈ pt.stepDirs.map (Dir.forPlayer · o)) :
    (d.1 = 0 ∧ (d.2 = 1 ∨ d.2 = -1)) ∨ (d.2 = 0 ∧ (d.1 = 1 ∨ d.1 = -1)) := by
  have key : ∀ x ∈ pt.stepDirs.map (Dir.forPlayer · o),
      (x.1 = 0 ∧ (x.2 = 1 ∨ x.2 = -1)) ∨ (x.2 = 0 ∧ (x.1 = 1 ∨ x.1 = -1)) := by
    rcases hpt with rfl | rfl <;> cases o <;> decide
  exact key d h

/-- A rank or file unit direction is one of the four. -/
theorem orth_unit_cases {e : Dir} (hu : e ∈ PieceType.king.stepDirs) (horth : e.1 = 0 ∨ e.2 = 0) :
    e = (1, 0) ∨ e = (-1, 0) ∨ e = (0, 1) ∨ e = (0, -1) := by
  have key : ∀ x ∈ PieceType.king.stepDirs, (x.1 = 0 ∨ x.2 = 0) →
      x = (1, 0) ∨ x = (-1, 0) ∨ x = (0, 1) ∨ x = (0, -1) := by decide
  exact key e hu horth

/-- A diagonal slide between points on two perpendicular rank and file half-lines
    keeps the distance from the king. -/
theorem bishopEdge_of_diag_move (e1 e2 : Dir) (a b : ℤ) (ha : 0 < a) (hb : 0 < b)
    (h1 : e1 = (1, 0) ∨ e1 = (-1, 0) ∨ e1 = (0, 1) ∨ e1 = (0, -1))
    (h2 : e2 = (1, 0) ∨ e2 = (-1, 0) ∨ e2 = (0, 1) ∨ e2 = (0, -1))
    (hne : e2 ≠ e1) (hne' : e2 ≠ (-e1.1, -e1.2)) (s1 s2 k : ℤ) (hs1 : s1 = 1 ∨ s1 = -1)
    (hs2 : s2 = 1 ∨ s2 = -1) (hk : 1 ≤ k) (hx : b * e2.1 - a * e1.1 = k * s1)
    (hy : b * e2.2 - a * e1.2 = k * s2) :
    BishopEdge a (a * e1.1, a * e1.2) (b * e2.1, b * e2.2) := by
  unfold BishopEdge
  dsimp only
  rcases h1 with rfl | rfl | rfl | rfl <;> rcases h2 with rfl | rfl | rfl | rfl <;>
    simp only [ne_eq, Prod.mk.injEq, not_and, neg_zero, neg_neg, not_true_eq_false] at hne hne' <;>
    rcases hs1 with rfl | rfl <;> rcases hs2 with rfl | rfl <;>
    simp only [mul_one, mul_zero, mul_neg, neg_neg, sub_zero, zero_sub, true_and,
      true_or, or_true] at hx hy ⊢ <;>
    omega

/-- No single rank or file step joins two points on perpendicular rank and file
    half-lines. -/
theorem not_orth_step_between_rays (e1 e2 : Dir) (a b : ℤ) (ha : 0 < a) (hb : 0 < b)
    (h1 : e1 = (1, 0) ∨ e1 = (-1, 0) ∨ e1 = (0, 1) ∨ e1 = (0, -1))
    (h2 : e2 = (1, 0) ∨ e2 = (-1, 0) ∨ e2 = (0, 1) ∨ e2 = (0, -1))
    (hne : e2 ≠ e1) (hne' : e2 ≠ (-e1.1, -e1.2))
    (h : (b * e2.1 - a * e1.1 = 0 ∧ (b * e2.2 - a * e1.2 = 1 ∨ b * e2.2 - a * e1.2 = -1)) ∨
      (b * e2.2 - a * e1.2 = 0 ∧ (b * e2.1 - a * e1.1 = 1 ∨ b * e2.1 - a * e1.1 = -1))) :
    False := by
  rcases h1 with rfl | rfl | rfl | rfl <;> rcases h2 with rfl | rfl | rfl | rfl <;>
    simp only [ne_eq, Prod.mk.injEq, not_and, neg_zero, neg_neg, not_true_eq_false] at hne hne' <;>
    simp only [mul_one, mul_zero, mul_neg, neg_neg, sub_zero, zero_sub] at h <;>
    omega

namespace MoveTrace

/-- A non-glaring board move in a periodic trace satisfying the periodic-check premises is a
    discovered check by the moved piece. -/
theorem openableMove_of_nonGlaring_move (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hr : tr.BoardMovesFollowCanMoveToOriented)
    (hp : tr.IsPeriodic) (i : Fin tr.len) (src dst : Pos) (promote : Bool) (p : Piece)
    (hm : tr.moves i = .boardMove src dst promote)
    (hpc : (tr.before i).board.grid src = some p)
    (hng : ¬ tr.GlaresAtEnemyKing kp i.castSucc src) :
    tr.OpenableMoveBy kp p.owner p.pieceType := by
  have hown : p.owner = (tr.before i).turn := by
    obtain ⟨piece, hpiece, ho⟩ := hs i src dst promote hm
    rw [hpc] at hpiece
    cases hpiece
    exact ho
  have hu := tr.unblockedChecker_of_not_glares_source_of_periodic kp ht hs hk hsafe h0 hc hr hp
    i src dst promote hm hng
  rw [← hown] at hu
  exact ⟨i, src, dst, promote, hown.symm, hm, hpc, hng, hu⟩

/-- Only bishops and horses make discovered checks:  and 4–7 exclude every
    other kind. -/
theorem bishopHorse_of_openableMove (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (hm : tr.MutualPerpetualCheck kp) (h41 : tr.DiscoveredCheckByEachSide kp)
    (hcount : tr.PieceCountsAtMostTwo) (o : Player) (pt : PieceType)
    (h : tr.OpenableMoveBy kp o pt) : pt = .bishop ∨ pt = .horse := by
  cases pt <;> first
    | exact Or.inl rfl
    | exact Or.inr rfl
    | exact absurd h (tr.not_openableMove_king kp hm _)
    | exact absurd h (tr.not_openableMove_forward_of_periodic kp hm _ _ (by decide))
    | exact absurd h (tr.not_openableMove_goldType_of_periodic kp hm _ _ rfl)
    | exact absurd h (tr.not_openableMove_silver_of_periodic kp hm hcount _)
    | exact absurd h (tr.not_openableMove_rookDragon_of_periodic kp hm h41 hcount _ _
        (by decide))

/-- Every non-glaring board move moves a bishop or a horse. -/
theorem bishopHorse_of_nonGlaring_move (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (hm : tr.MutualPerpetualCheck kp) (h41 : tr.DiscoveredCheckByEachSide kp)
    (hcount : tr.PieceCountsAtMostTwo) (i : Fin tr.len) (src dst : Pos) (promote : Bool)
    (p : Piece) (hmv : tr.moves i = .boardMove src dst promote)
    (hpc : (tr.before i).board.grid src = some p)
    (hng : ¬ tr.GlaresAtEnemyKing kp i.castSucc src) :
    p.pieceType = .bishop ∨ p.pieceType = .horse :=
  tr.bishopHorse_of_openableMove kp hm h41 hcount _ _
    (tr.openableMove_of_nonGlaring_move kp hm.transitions hm.sourcesOwned hm.kingsWellPlaced
      hm.ownKingSafe hm.initialOpponentSafe hm.checks hm.movementRules hm.periodic i src dst
      promote p hmv hpc hng)

/-- Every openable piece is a bishop or a horse: it leaves its square later by a
    non-glaring board move. -/
theorem bishopHorse_of_openable_of_periodic (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos) (hm : tr.MutualPerpetualCheck kp)
    (h41 : tr.DiscoveredCheckByEachSide kp) (hcount : tr.PieceCountsAtMostTwo)
    (k : Fin (tr.len + 1)) (q : Pos) (hq : tr.IsOpenableAt kp k q) (P : Piece)
    (hP : (tr.states k).board.grid q = some P) :
    P.pieceType = .bishop ∨ P.pieceType = .horse := by
  obtain ⟨ht, hs, hk, hsafe, h0, hc, hr, hp, _, _⟩ := hm
  have hkp := tr.kingPos_eq_of_periodic kp ht hs hk hsafe h0 hc hr hp
  obtain ⟨_, j, dst, pr, _, _, _, _, _, _, hngi, hmj, hcyc, _, _, _, _, hall⟩ :=
    tr.openable_covered_of_periodic kp ht hs hk hsafe h0 hc hr hp k q hq
  obtain ⟨hqk, _, _⟩ := hall k hcyc
  obtain ⟨hqj, _, _⟩ := hall j.castSucc (cyclicBetween_self_right _ _)
  have hPj : (tr.before j).board.grid q = some P := by
    change (tr.states j.castSucc).board.grid q = some P
    rw [hqj, ← hqk, hP]
  have hngj : ¬ tr.GlaresAtEnemyKing kp j.castSucc q := fun hg =>
    hngi ((tr.glaresAtEnemyKing_congr kp ht hqj ((hkp _).trans (hkp _).symm)).mp hg)
  exact tr.bishopHorse_of_nonGlaring_move kp ⟨ht, hs, hk, hsafe, h0, hc, hr, hp, ‹_›, ‹_›⟩ h41
    hcount j q dst pr P hmj hPj hngj

/-- In every state each side has an openable bishop or horse. -/
theorem exists_openable_bishopHorse_of_periodic (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos) (hm : tr.MutualPerpetualCheck kp)
    (h41 : tr.DiscoveredCheckByEachSide kp) (hcount : tr.PieceCountsAtMostTwo)
    (k : Fin (tr.len + 1)) (o : Player) :
    ∃ (q : Pos) (P : Piece), (tr.states k).board.grid q = some P ∧ P.owner = o ∧
      (P.pieceType = .bishop ∨ P.pieceType = .horse) ∧ tr.IsOpenableAt kp k q := by
  have hm' := hm
  obtain ⟨ht, hs, hk, hsafe, h0, hc, hr, hp, _, _⟩ := hm
  obtain ⟨pt, hopen⟩ := tr.exists_openableMove kp hm' h41 o
  have hpt := tr.bishopHorse_of_openableMove kp hm' h41 hcount o pt hopen
  obtain ⟨j, s, _, _, _, hmj, hsj, hngj, _⟩ := hopen
  let P : Piece → Prop := fun x => x.owner = o ∧ (x.pieceType = .bishop ∨ x.pieceType = .horse)
  have hmem : s ∈ tr.openableSquaresOf kp P j.castSucc := by
    refine (tr.mem_openableSquaresOf kp P _ _).mpr ⟨⟨_, hsj, rfl, hpt⟩, ?_, hngj,
      fun himm => himm.2 j (by rw [hmj]; exact Or.inl rfl)⟩
    change (tr.before j).board.grid s ≠ none
    rw [hsj]
    exact Option.some_ne_none _
  have hpos : 0 < (tr.openableSquaresOf kp P k).card := by
    rw [tr.openableSquaresOf_card_eq_of_periodic kp ht hs hk hsafe h0 hc hr hp P k,
      ← tr.openableSquaresOf_card_eq_of_periodic kp ht hs hk hsafe h0 hc hr hp P j.castSucc]
    exact Finset.card_pos.mpr ⟨s, hmem⟩
  obtain ⟨q, hq⟩ := Finset.card_pos.mp hpos
  obtain ⟨⟨x, hx, hxo, hxt⟩, hqo⟩ := (tr.mem_openableSquaresOf kp P _ _).mp hq
  exact ⟨q, x, hx, hxo, hxt, hqo⟩

/-- In every state the openable bishops or horses of the two sides are all the
    bishops and horses on the board: every bishop or horse is openable. -/
theorem openable_of_bishopHorse_of_periodic (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos) (hm : tr.MutualPerpetualCheck kp)
    (h41 : tr.DiscoveredCheckByEachSide kp) (hcount : tr.PieceCountsAtMostTwo)
    (k : Fin (tr.len + 1)) (q : Pos) (P : Piece) (hP : (tr.states k).board.grid q = some P)
    (hPt : P.pieceType = .bishop ∨ P.pieceType = .horse) : tr.IsOpenableAt kp k q := by
  obtain ⟨a, A, hA, hAo, hAt, haop⟩ :=
    tr.exists_openable_bishopHorse_of_periodic kp hm h41 hcount k .sente
  obtain ⟨b, B, hB, hBo, hBt, hbop⟩ :=
    tr.exists_openable_bishopHorse_of_periodic kp hm h41 hcount k .gote
  have hab : a ≠ b := by
    rintro rfl
    rw [hA] at hB
    cases hB
    cases hBo.symm.trans hAo
  have hsub : ({a, b} : Finset Pos) ⊆ tr.bishopHorseSquares k := by
    intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact tr.mem_bishopHorseSquares_of _ _ A hA hAt
    · exact tr.mem_bishopHorseSquares_of _ _ B hB hBt
  have hall : tr.bishopHorseSquares k = {a, b} := by
    refine (Finset.eq_of_subset_of_card_le hsub ?_).symm
    rw [Finset.card_pair hab]
    exact (hcount k).1
  have hmem := tr.mem_bishopHorseSquares_of _ _ P hP hPt
  rw [hall] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl
  · exact haop
  · exact hbop

/-- Under the same premises, no bishop or horse glares. -/
theorem not_glares_bishopHorse_of_periodic (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos) (hm : tr.MutualPerpetualCheck kp)
    (h41 : tr.DiscoveredCheckByEachSide kp) (hcount : tr.PieceCountsAtMostTwo)
    (k : Fin (tr.len + 1)) (q : Pos) (P : Piece) (hP : (tr.states k).board.grid q = some P)
    (hPt : P.pieceType = .bishop ∨ P.pieceType = .horse) : ¬ tr.GlaresAtEnemyKing kp k q :=
  (tr.openable_of_bishopHorse_of_periodic kp hm h41 hcount k q P hP hPt).2.1

/-- In a periodic trace satisfying the periodic-check premises, Proposition 3.3's glaring piece
    behind an openable square, in any state, slides back along the square's
    half-line from the enemy king. -/
theorem slider_behind_openable_of_periodic (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hr : tr.BoardMovesFollowCanMoveToOriented)
    (hp : tr.IsPeriodic) (k : Fin (tr.len + 1)) (q : Pos) (hq : tr.IsOpenableAt kp k q)
    (P : Piece) (hP : (tr.states k).board.grid q = some P) :
    ∃ (B : Pos) (Q : Piece) (e : Dir) (b m : ℤ), (tr.states k).board.grid B = some Q ∧
      Q.owner = P.owner ∧ tr.GlaresAtEnemyKing kp k B ∧
      OnRay (kp 0 P.owner.opponent) e b q ∧ OnRay (kp 0 P.owner.opponent) e m B ∧ b < m ∧
      ((-e.1, -e.2) : Dir) ∈ Q.pieceType.slideDirs.map (Dir.forPlayer · Q.owner) := by
  have hkp := tr.kingPos_eq_of_periodic kp ht hs hk hsafe h0 hc hr hp
  obtain ⟨i, j, dst, pr, B, Q, e, b, m, hdi, _, hmj, hcyc, hown, hray, hB, hbm, hall⟩ :=
    tr.openable_covered_of_periodic kp ht hs hk hsafe h0 hc hr hp k q hq
  obtain ⟨hqk, hQk, hglk⟩ := hall k hcyc
  have hPown : P.owner = (tr.before i).turn := by
    obtain ⟨P', hP', hP'o⟩ := tr.destination_piece_owner ht hs i
    rw [hdi, ← hqk, hP] at hP'
    cases hP'
    exact hP'o
  have hQP : Q.owner = P.owner := hown.trans hPown.symm
  rw [hQP] at hray hB
  obtain ⟨hqj, hQj, _⟩ := hall j.castSucc (cyclicBetween_self_right _ _)
  have hturnj : (tr.before j).turn = P.owner := by
    obtain ⟨piece, hpiece, ho⟩ := hs j q dst pr hmj
    change (tr.states j.castSucc).board.grid q = some piece at hpiece
    rw [hqj, ← hqk, hP] at hpiece
    cases hpiece
    exact ho.symm
  have hstep : Pos.dirTo B (kp 0 P.owner.opponent) ∉
      Q.pieceType.stepDirs.map (Dir.forPlayer · Q.owner) := by
    have h := tr.not_stepAttack_of_before kp ht hsafe h0 j B Q hQj (hQP.trans hturnj.symm)
    rw [hkp j.castSucc, hturnj] at h
    exact h
  obtain ⟨Q', hQ', hatkQ⟩ := hglk
  rw [hQk] at hQ'
  cases hQ'
  have hatkQ' := hatkQ
  rw [hkp k, show kp 0 Q.owner.opponent = kp 0 P.owner.opponent by rw [hQP]] at hatkQ'
  have hslide := slideDir_of_attack_not_step _ _ _ B _ hatkQ' hstep hB
  exact ⟨B, Q, e, b, m, hQk, hQP, ⟨Q, hQk, hatkQ⟩, hray, hB, hbm, hslide⟩

/-- An openable bishop or horse stands on a rank or file half-line from its enemy
    king: the piece glaring behind it is not a bishop or horse, so it does not slide
    diagonally. -/
theorem orth_ray_of_openable_of_periodic (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos) (hm : tr.MutualPerpetualCheck kp)
    (h41 : tr.DiscoveredCheckByEachSide kp) (hcount : tr.PieceCountsAtMostTwo)
    (k : Fin (tr.len + 1)) (q : Pos) (hq : tr.IsOpenableAt kp k q) (P : Piece)
    (hP : (tr.states k).board.grid q = some P) :
    ∃ (e : Dir) (b : ℤ), OnRay (kp 0 P.owner.opponent) e b q ∧ (e.1 = 0 ∨ e.2 = 0) := by
  have hm' := hm
  obtain ⟨ht, hs, hk, hsafe, h0, hc, hr, hp, _, _⟩ := hm
  obtain ⟨B, Q, e, b, _, hQ, _, hgl, hray, hB, _, hslide⟩ :=
    tr.slider_behind_openable_of_periodic kp ht hs hk hsafe h0 hc hr hp k q hq P hP
  refine ⟨e, b, hray, ?_⟩
  by_contra horth
  push Not at horth
  have hu := (PieceType.mem_king_stepDirs_iff e).mp hB.1
  have hQt := bishopHorse_of_slideDir _ _ _ hslide (by dsimp only; omega) (by dsimp only; omega)
  exact tr.not_glares_bishopHorse_of_periodic kp hm' h41 hcount k B Q hQ hQt hgl

/-- A non-glaring move of a bishop or horse goes between two points at the same
    distance from the enemy king, one on its rank and the other on its file. -/
theorem bishopEdge_of_nonGlaring_move_of_periodic (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos) (hm : tr.MutualPerpetualCheck kp)
    (h41 : tr.DiscoveredCheckByEachSide kp) (hcount : tr.PieceCountsAtMostTwo)
    (i : Fin tr.len) (src dst : Pos) (promote : Bool) (p : Piece)
    (hmv : tr.moves i = .boardMove src dst promote)
    (hpc : (tr.before i).board.grid src = some p)
    (hng : ¬ tr.GlaresAtEnemyKing kp i.castSucc src) :
    ∃ t : ℤ, BishopEdge t (relTo (kp 0 p.owner.opponent) src)
      (relTo (kp 0 p.owner.opponent) dst) := by
  have hm' := hm
  obtain ⟨ht, hs, hk, hsafe, h0, hc, hr, hp, _, _⟩ := hm
  have hpt := tr.bishopHorse_of_nonGlaring_move kp hm' h41 hcount i src dst promote p hmv hpc hng
  have hown : p.owner = (tr.before i).turn := by
    obtain ⟨piece, hpiece, ho⟩ := hs i src dst promote hmv
    rw [hpc] at hpiece
    cases hpiece
    exact ho
  -- Both ends lie on rank or file half-lines.
  have hsrcOpen : tr.IsOpenableAt kp i.castSucc src := by
    refine ⟨?_, hng, fun himm => himm.2 i (by rw [hmv]; exact Or.inl rfl)⟩
    change (tr.before i).board.grid src ≠ none
    rw [hpc]
    exact Option.some_ne_none _
  have hdstgrid : (tr.states i.succ).board.grid dst = some p := by
    change (tr.after i).board.grid dst = some p
    rw [tr.boardMove_grid_dst_eq_of_not_glares_of_periodic kp ht hs hk hsafe h0 hc hr hp i src dst
      promote hmv hng]
    exact hpc
  have hngd : ¬ tr.GlaresAtEnemyKing kp i.succ dst := fun hg =>
    hng (tr.glares_source_of_glares_destination_of_periodic kp ht hs hk hsafe h0 hc hr hp i src
      dst promote hmv hg)
  have hdstOpen : tr.IsOpenableAt kp i.succ dst := by
    refine ⟨?_, hngd, fun himm => himm.2 i (by rw [hmv]; exact Or.inr rfl)⟩
    rw [hdstgrid]
    exact Option.some_ne_none _
  obtain ⟨e1, b1, hray1, horth1⟩ :=
    tr.orth_ray_of_openable_of_periodic kp hm' h41 hcount i.castSucc src hsrcOpen p hpc
  obtain ⟨e2, b2, hray2, horth2⟩ :=
    tr.orth_ray_of_openable_of_periodic kp hm' h41 hcount i.succ dst hdstOpen p hdstgrid
  -- The half-lines are neither equal nor opposite.
  obtain ⟨d, e, a, b, hsr, hdr, hed, hed'⟩ :=
    tr.openable_move_rays_of_periodic kp ht hs hk hsafe h0 hc hr hp i src dst promote hmv hng
  rw [← hown] at hsr hdr
  obtain ⟨he1, _⟩ := OnRay.unique hray1 hsr
  obtain ⟨he2, _⟩ := OnRay.unique hray2 hdr
  rw [← he1, ← he2] at hed hed'
  have rs := hray1.relTo_eq
  have rd := hray2.relTo_eq
  have hc1 := orth_unit_cases hray1.1 horth1
  have hc2 := orth_unit_cases hray2.1 horth2
  have hb1 := hray1.2.1
  have hb2 := hray2.2.1
  -- The move: a diagonal slide, or a horse's step along a rank or file.
  have hdiff : Pos.dirTo src dst = (b2 * e2.1 - b1 * e1.1, b2 * e2.2 - b1 * e1.2) := by
    have h1 := congrArg Prod.fst rs
    have h2 := congrArg Prod.snd rs
    have g1 := congrArg Prod.fst rd
    have g2 := congrArg Prod.snd rd
    simp only [relTo, Pos.toInt] at h1 h2 g1 g2
    simp only [Pos.dirTo]
    ext <;> dsimp only <;> linarith
  refine ⟨b1, ?_⟩
  rw [rs, rd]
  rcases hr i src dst promote p hmv hpc with hst | ⟨sd, hsd, _, k, hk, hx, hy, _⟩
  · exfalso
    have h := orth_of_bishopHorse_stepDir _ _ _ hpt hst
    rw [hdiff] at h
    exact not_orth_step_between_rays e1 e2 b1 b2 hb1 hb2 hc1 hc2 hed hed' h
  · have hdg := diag_of_bishopHorse_slideDir _ _ _ hpt hsd
    rw [hdiff] at hx hy
    have hk' : (1 : ℤ) ≤ k := by exact_mod_cast hk
    exact bishopEdge_of_diag_move e1 e2 b1 b2 hb1 hb2 hc1 hc2 hed hed' sd.1 sd.2 k hdg.1 hdg.2
      hk' hx hy

end MoveTrace
end MPC
