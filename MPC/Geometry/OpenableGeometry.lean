import MPC.Basic.Lemmas
import MPC.Glare.NonGlaringKind
import Mathlib.Data.Finset.Max
/-!
# MPC.Geometry.OpenableGeometry

The geometry of discovered checks in periodic traces.

The paper's Section 5 starts from Proposition 3.3: a move of a non-glaring piece
is a discovered check, so it goes from one of the eight lines through the enemy
king to a different one. Here a line through `K` is a half-line: a point lies
`c ≥ 1` king steps from `K` along a king direction `d` (`OnRay K d c q`).

- A sliding attack that is not a step puts the attacker on a half-line from its
  target, and the squares strictly between are exactly the nearer points of that
  half-line (`ray_of_attack_not_step`).
- A move of two or more unit steps along a line that passes an occupied square is
  neither a step nor a clear slide (`not_canMoveToOriented_of_blocked`).
- Proposition 3.3 in half-line form: when a move puts a non-glaring piece on `A`,
  `A` and the glaring piece `Q` behind it lie on one half-line from the enemy king,
  `A` nearer (`openable_glaring_ray_cyclic_of_periodic`). `Q` does not attack by a
  step, since step attacks ignore the board and the opponent is never in check on
  the mover's turn.
- A board move of a non-glaring piece goes between two half-lines from the enemy
  king that are neither equal nor opposite (`openable_move_rays_of_periodic`).
  - The source lies between the unblocked checker and the king.
  - On the same half-line, the destination would block the checker, sit on it, or
    lie beyond it, so the move would jump over it.
  - On the opposite half-line, the move would jump over the enemy king.
- Coverage: in every state, an openable piece lies inside the cyclic interval from
  the move that brought it to the move that takes it away, so Proposition 3.3's
  glaring piece stands behind it in that state (`openable_covered_of_periodic`).

-/

namespace MPC

private theorem pos_eq_of_toInt {a b : Pos} (h : a.toInt = b.toInt) : a = b := by
  have h1 : (a.1.val : ℤ) = b.1.val := congrArg Prod.fst h
  have h2 : (a.2.val : ℤ) = b.2.val := congrArg Prod.snd h
  exact Prod.ext (Fin.ext (by exact_mod_cast h1)) (Fin.ext (by exact_mod_cast h2))

/-- Every oriented slide direction is a unit step. -/
private theorem slide_mem_king (pt : PieceType) (o : Player) (d : Dir)
    (h : d ∈ pt.slideDirs.map (Dir.forPlayer · o)) : d ∈ PieceType.king.stepDirs := by
  have key : ∀ x ∈ pt.slideDirs.map (Dir.forPlayer · o), x ∈ PieceType.king.stepDirs := by
    cases o <;> cases pt <;> decide
  exact key d h

/-- The reverse of a king direction is a king direction. -/
theorem neg_mem_king_stepDirs {d : Dir} (h : d ∈ PieceType.king.stepDirs) :
    ((-d.1, -d.2) : Dir) ∈ PieceType.king.stepDirs := by
  rw [PieceType.mem_king_stepDirs_iff] at h ⊢
  dsimp only
  omega

/-- `q` lies `c ≥ 1` unit steps from `K` along the king direction `d`: on one of the
    eight half-lines from `K`. -/
def OnRay (K : Pos) (d : Dir) (c : ℤ) (q : Pos) : Prop :=
  d ∈ PieceType.king.stepDirs ∧ 0 < c ∧
    q.toInt = (K.toInt.1 + c * d.1, K.toInt.2 + c * d.2)

/-- A point of a half-line determines the direction and the distance. -/
theorem OnRay.unique {K q : Pos} {d e : Dir} {c c' : ℤ} (h : OnRay K d c q)
    (h' : OnRay K e c' q) : d = e ∧ c = c' := by
  obtain ⟨hd, hc, hq⟩ := h
  obtain ⟨he, hc', hq'⟩ := h'
  rw [hq] at hq'
  have h1 : c * d.1 = c' * e.1 := by
    have := congrArg Prod.fst hq'
    dsimp only at this
    linarith
  have h2 : c * d.2 = c' * e.2 := by
    have := congrArg Prod.snd hq'
    dsimp only at this
    linarith
  obtain ⟨d1, d2⟩ := d
  obtain ⟨e1, e2⟩ := e
  rw [PieceType.mem_king_stepDirs_iff] at hd he
  dsimp only at hd he h1 h2
  have key : d1 = e1 ∧ d2 = e2 ∧ c = c' := by
    rcases (show d1 = -1 ∨ d1 = 0 ∨ d1 = 1 by omega) with rfl | rfl | rfl <;>
      rcases (show d2 = -1 ∨ d2 = 0 ∨ d2 = 1 by omega) with rfl | rfl | rfl <;>
      rcases (show e1 = -1 ∨ e1 = 0 ∨ e1 = 1 by omega) with rfl | rfl | rfl <;>
      rcases (show e2 = -1 ∨ e2 = 0 ∨ e2 = 1 by omega) with rfl | rfl | rfl <;>
      omega
  exact ⟨Prod.ext key.1 key.2.1, key.2.2⟩

/-- A sliding attack on `K` from `B` that is not a step: `B` lies on a half-line
    from `K`, the path is clear, and the squares strictly between `B` and `K` are
    exactly the nearer points of that half-line. -/
theorem ray_of_attack_not_step (board : Board) (o : Player) (pt : PieceType) (B K : Pos)
    (hatk : attacksOriented board o pt B K)
    (hstep : Pos.dirTo B K ∉ pt.stepDirs.map (Dir.forPlayer · o)) :
    ∃ (d : Dir) (n : ℤ), OnRay K d n B ∧ pathClear board B K ∧
      ∀ q : ℤ × ℤ, q ∈ slidePath B K ↔
        ∃ c : ℤ, 1 ≤ c ∧ c < n ∧ q = (K.toInt.1 + c * d.1, K.toInt.2 + c * d.2) := by
  rcases hatk with hst | ⟨sd, hsd, hnorm, n, hn, hx, hy, hpc⟩
  · exact absurd hst hstep
  have hsdK := slide_mem_king _ _ sd hsd
  have hu := (PieceType.mem_king_stepDirs_iff sd).mp hsdK
  have hd0 : sd ≠ (0, 0) := fun h => hu.2.2.2.2 ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  have hKx : K.toInt.1 = B.toInt.1 + ↑n * sd.1 := by
    dsimp [Pos.dirTo, Pos.toInt] at hx ⊢
    omega
  have hKy : K.toInt.2 = B.toInt.2 + ↑n * sd.2 := by
    dsimp [Pos.dirTo, Pos.toInt] at hy ⊢
    omega
  have hiff := mem_slidePath_iff_of_exact_steps B K sd n hd0 hn hnorm hKx hKy
  refine ⟨(-sd.1, -sd.2), n, ⟨neg_mem_king_stepDirs hsdK, by omega, ?_⟩, hpc, fun q => ?_⟩
  · ext
    · show B.toInt.1 = K.toInt.1 + ↑n * -sd.1
      rw [hKx]; ring
    · show B.toInt.2 = K.toInt.2 + ↑n * -sd.2
      rw [hKy]; ring
  rw [hiff q]
  constructor
  · rintro ⟨j, hj1, hjn, rfl⟩
    refine ⟨(n : ℤ) - j, by omega, by omega, ?_⟩
    ext
    · show B.toInt.1 + ↑j * sd.1 = K.toInt.1 + (↑n - ↑j) * -sd.1
      rw [hKx]; ring
    · show B.toInt.2 + ↑j * sd.2 = K.toInt.2 + (↑n - ↑j) * -sd.2
      rw [hKy]; ring
  · rintro ⟨c, hc1, hcn, rfl⟩
    obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ n - c by omega)
    refine ⟨j, by omega, by omega, ?_⟩
    ext
    · show K.toInt.1 + c * -sd.1 = B.toInt.1 + ↑j * sd.1
      rw [hKx, ← hj]; ring
    · show K.toInt.2 + c * -sd.2 = B.toInt.2 + ↑j * sd.2
      rw [hKy, ← hj]; ring

/-- A move of two or more unit steps along a line, past an occupied square, is
    neither a step nor a clear slide. -/
theorem not_canMoveToOriented_of_blocked (board : Board) (o : Player) (pt : PieceType)
    (src dst P : Pos) (u : Dir) (s t : ℤ) (hu : u ∈ PieceType.king.stepDirs)
    (hdst : dst.toInt = (src.toInt.1 + s * u.1, src.toInt.2 + s * u.2))
    (ht1 : 1 ≤ t) (hts : t < s)
    (hP : P.toInt = (src.toInt.1 + t * u.1, src.toInt.2 + t * u.2))
    (hocc : board.grid P ≠ none) :
    ¬ canMoveToOriented board o pt src dst := by
  have hd1 : (Pos.dirTo src dst).1 = s * u.1 := by
    have := congrArg Prod.fst hdst
    dsimp [Pos.dirTo, Pos.toInt] at this ⊢
    omega
  have hd2 : (Pos.dirTo src dst).2 = s * u.2 := by
    have := congrArg Prod.snd hdst
    dsimp [Pos.dirTo, Pos.toInt] at this ⊢
    omega
  obtain ⟨u1, u2⟩ := u
  have huu := (PieceType.mem_king_stepDirs_iff (u1, u2)).mp hu
  dsimp only at huu hd1 hd2 hdst hP
  rintro (hst | ⟨sd, hsd, hnorm, k, hk, hx, hy, hpc⟩)
  · -- A step is a unit step or a knight's jump; neither spans two unit steps.
    rcases stepDir_unit_or_knight pt o _ hst with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2⟩
    · rw [hd1] at h1 h2
      rw [hd2] at h3 h4
      rcases (show u1 = -1 ∨ u1 = 0 ∨ u1 = 1 by omega) with rfl | rfl | rfl <;>
        rcases (show u2 = -1 ∨ u2 = 0 ∨ u2 = 1 by omega) with rfl | rfl | rfl <;>
        omega
    · rw [hd1] at h1
      rw [hd2] at h2
      rcases (show u1 = -1 ∨ u1 = 0 ∨ u1 = 1 by omega) with rfl | rfl | rfl <;>
        rcases (show u2 = -1 ∨ u2 = 0 ∨ u2 = 1 by omega) with rfl | rfl | rfl <;>
        omega
  · -- A slide along `u` must pass `P`, which is occupied.
    have hsdK := slide_mem_king _ _ sd hsd
    obtain ⟨sd1, sd2⟩ := sd
    have hsu := (PieceType.mem_king_stepDirs_iff (sd1, sd2)).mp hsdK
    dsimp only at hsu hx hy
    rw [hd1] at hx
    rw [hd2] at hy
    have hsame : sd1 = u1 ∧ sd2 = u2 ∧ (k : ℤ) = s := by
      rcases (show u1 = -1 ∨ u1 = 0 ∨ u1 = 1 by omega) with rfl | rfl | rfl <;>
        rcases (show u2 = -1 ∨ u2 = 0 ∨ u2 = 1 by omega) with rfl | rfl | rfl <;>
        rcases (show sd1 = -1 ∨ sd1 = 0 ∨ sd1 = 1 by omega) with rfl | rfl | rfl <;>
        rcases (show sd2 = -1 ∨ sd2 = 0 ∨ sd2 = 1 by omega) with rfl | rfl | rfl <;>
        omega
    obtain ⟨rfl, rfl, hks⟩ := hsame
    have hd0 : ((sd1, sd2) : Dir) ≠ (0, 0) := fun h =>
      hsu.2.2.2.2 ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    have hiff := mem_slidePath_iff_of_exact_steps src dst (sd1, sd2) k hd0 hk hnorm
      (by rw [hdst]; dsimp only; rw [hks]) (by rw [hdst]; dsimp only; rw [hks])
    obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ t by omega)
    have hmem : P.toInt ∈ slidePath src dst := by
      rw [hiff]
      refine ⟨j, by omega, by omega, ?_⟩
      rw [hP, hj]
    have h := hpc P.toInt hmem (Pos.onBoard_toInt P) (Pos.onBoard_toInt P)
    rw [Pos.toPos_toInt] at h
    exact hocc h

namespace MoveTrace

/-- Proposition 3.3 in half-line form: in a periodic trace satisfying 's
    premises, let move `i` put a non-glaring piece on `A`. Besides Proposition
    3.3's conclusion, `A` and the glaring piece's square `B` lie on one half-line
    from the enemy king, `A` nearer. -/
theorem openable_glaring_ray_cyclic_of_periodic (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hr : tr.BoardMovesFollowCanMoveToOriented)
    (hp : tr.IsPeriodic) (i : Fin tr.len)
    (hng : ¬ tr.GlaresAtEnemyKing kp i.succ (tr.moves i).destination) :
    ∃ (j : Fin tr.len) (dst : Pos) (promote : Bool) (B : Pos) (Q : Piece) (e : Dir) (b m : ℤ),
      tr.moves j = .boardMove (tr.moves i).destination dst promote ∧
      Q.owner = (tr.before i).turn ∧
      OnRay (kp 0 Q.owner.opponent) e b (tr.moves i).destination ∧
      OnRay (kp 0 Q.owner.opponent) e m B ∧ b < m ∧
      ∀ k : Fin (tr.len + 1), cyclicBetween i.succ j.castSucc k →
        (tr.states k).board.grid (tr.moves i).destination =
          (tr.states i.succ).board.grid (tr.moves i).destination ∧
        (tr.states k).board.grid B = some Q ∧ tr.GlaresAtEnemyKing kp k B := by
  have hkp := tr.kingPos_eq_of_periodic kp ht hs hk hsafe h0 hc hr hp
  obtain ⟨j, dstj, prj, B, Q, hmj, hown, hmem, hall⟩ :=
    tr.openable_glaring_line_cyclic_of_periodic kp ht hs hk hsafe h0 hc hr hp i hng
  obtain ⟨P, hP, hPo⟩ := tr.destination_piece_owner ht hs i
  obtain ⟨hQ1, hgl1⟩ := (hall i.succ (cyclicBetween_self_left _ _)).2
  obtain ⟨hAj, hQj, _⟩ := hall j.castSucc (cyclicBetween_self_right _ _)
  -- The departing side is the mover of `i`, so `Q` does not attack by a step.
  have hturn : (tr.before j).turn = (tr.before i).turn := by
    obtain ⟨piece, hpiece, ho⟩ := hs j _ dstj prj hmj
    change (tr.states j.castSucc).board.grid _ = some piece at hpiece
    rw [hAj, hP] at hpiece
    cases hpiece
    exact ho.symm.trans hPo
  have hstepQ : Pos.dirTo B (kp 0 Q.owner.opponent) ∉
      Q.pieceType.stepDirs.map (Dir.forPlayer · Q.owner) := by
    have h := tr.not_stepAttack_of_before kp ht hsafe h0 j B Q hQj (hown.trans hturn.symm)
    rw [hkp j.castSucc, hturn, ← hown] at h
    exact h
  obtain ⟨Q', hQ', hatkQ⟩ := hgl1
  rw [hQ1] at hQ'
  cases hQ'
  rw [hkp i.succ] at hatkQ
  obtain ⟨e, n, hB, _, hiff⟩ := ray_of_attack_not_step _ _ _ B _ hatkQ hstepQ
  obtain ⟨c, hc1, hcn, hA⟩ := (hiff _).mp hmem
  exact ⟨j, dstj, prj, B, Q, e, c, n, hmj, hown, ⟨hB.1, by omega, hA⟩, hB, hcn, hall⟩

/-- The geometry of a discovered check: in a periodic trace satisfying 's
    premises, a board move from a non-glaring square goes between two half-lines
    from the enemy king that are neither equal nor opposite. -/
theorem openable_move_rays_of_periodic (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hr : tr.BoardMovesFollowCanMoveToOriented)
    (hp : tr.IsPeriodic) (i : Fin tr.len) (src dst : Pos) (promote : Bool)
    (hm : tr.moves i = .boardMove src dst promote)
    (hns : ¬ tr.GlaresAtEnemyKing kp i.castSucc src) :
    ∃ (d e : Dir) (a b : ℤ),
      OnRay (kp 0 (tr.before i).turn.opponent) d a src ∧
      OnRay (kp 0 (tr.before i).turn.opponent) e b dst ∧
      e ≠ d ∧ e ≠ (-d.1, -d.2) := by
  have hkp := tr.kingPos_eq_of_periodic kp ht hs hk hsafe h0 hc hr hp
  obtain ⟨K, hKdef⟩ : ∃ K, K = kp 0 (tr.before i).turn.opponent := ⟨_, rfl⟩
  rw [← hKdef]
  -- The unblocked checker `C`: the source lies between it and the enemy king.
  have hu := tr.unblockedChecker_of_not_glares_source_of_periodic kp ht hs hk hsafe h0 hc hr hp
    i src dst promote hm hns
  rw [hm] at hu
  obtain ⟨C, X, hCs, hCd, hXb, hXa, hXo, hatk, hsrcmem, hdstmem, _, _⟩ := hu
  have hXo' : X.owner = (tr.before i).turn := by rw [hXo, Player.opponent_opponent]
  rw [hkp i.succ, ← hKdef] at hatk hsrcmem hdstmem
  have hstep : Pos.dirTo C K ∉ X.pieceType.stepDirs.map (Dir.forPlayer · X.owner) := by
    have h := tr.not_stepAttack_of_before kp ht hsafe h0 i C X hXb hXo'
    rw [hkp i.castSucc, ← hKdef] at h
    exact h
  obtain ⟨d, n, hC, _, hiff⟩ := ray_of_attack_not_step _ _ _ C K hatk hstep
  obtain ⟨a, ha1, han, hsrc⟩ := (hiff _).mp hsrcmem
  -- The destination lies on Proposition 3.3's half-line.
  have hng : ¬ tr.GlaresAtEnemyKing kp i.succ (tr.moves i).destination := by
    rw [hm]
    exact fun hg => hns (tr.glares_source_of_glares_destination_of_periodic kp ht hs hk hsafe h0
      hc hr hp i src dst promote hm hg)
  obtain ⟨_, _, _, _, Q, e, b, _, _, hown, hdst, _, _, _⟩ :=
    tr.openable_glaring_ray_cyclic_of_periodic kp ht hs hk hsafe h0 hc hr hp i hng
  rw [hown, ← hKdef, hm] at hdst
  change OnRay K e b dst at hdst
  refine ⟨d, e, a, b, ⟨hC.1, by omega, hsrc⟩, hdst, ?_, ?_⟩
  · -- Same half-line: the destination blocks `C`, sits on it, or lies beyond it.
    rintro rfl
    obtain ⟨_, hb0, hdstEq⟩ := hdst
    rcases lt_trichotomy b n with hbn | hbn | hbn
    · exact hdstmem ((hiff _).mpr ⟨b, by omega, hbn, hdstEq⟩)
    · apply hCd
      apply pos_eq_of_toInt
      rw [hC.2.2, hdstEq, hbn]
    · -- The move jumps over `C`, which stood there before.
      obtain ⟨piece, hpiece, _⟩ := hs i src dst promote hm
      apply not_canMoveToOriented_of_blocked (tr.before i).board piece.owner piece.pieceType
        src dst C e (b - a) (n - a) hC.1 ?_ (by omega) (by omega) ?_ (by rw [hXb]; simp)
        (hr i src dst promote piece hm hpiece)
      · rw [hdstEq, hsrc]
        ext <;> dsimp only <;> ring
      · rw [hC.2.2, hsrc]
        ext <;> dsimp only <;> ring
  · -- Opposite half-line: the move jumps over the enemy king.
    rintro rfl
    obtain ⟨_, hb0, hdstEq⟩ := hdst
    obtain ⟨piece, hpiece, _⟩ := hs i src dst promote hm
    have hKocc : (tr.before i).board.grid K ≠ none := by
      rw [hKdef, ← hkp i.castSucc]
      change (tr.states i.castSucc).board.grid _ ≠ none
      rw [(hk i.castSucc).king_present]
      simp
    apply not_canMoveToOriented_of_blocked (tr.before i).board piece.owner piece.pieceType
      src dst K (-d.1, -d.2) (a + b) a (neg_mem_king_stepDirs hC.1) ?_ (by omega) (by omega) ?_
      hKocc (hr i src dst promote piece hm hpiece)
    · rw [hdstEq, hsrc]
      ext <;> dsimp only <;> ring
    · rw [hsrc]
      ext <;> dsimp only <;> ring

/-- Coverage: in a periodic trace satisfying the periodic-check premises, every openable piece
    at state `k` was put on its square by some move `i` and leaves it by a later
    move `j` (cyclically), with `k` between them. So Proposition 3.3's glaring
    piece stands behind it on its half-line at state `k`. -/
theorem openable_covered_of_periodic (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hr : tr.BoardMovesFollowCanMoveToOriented)
    (hp : tr.IsPeriodic) (k : Fin (tr.len + 1)) (q : Pos) (hq : tr.IsOpenableAt kp k q) :
    ∃ (i j : Fin tr.len) (dst : Pos) (promote : Bool) (B : Pos) (Q : Piece) (e : Dir)
      (b m : ℤ),
      (tr.moves i).destination = q ∧ ¬ tr.GlaresAtEnemyKing kp i.succ q ∧
      tr.moves j = .boardMove q dst promote ∧ cyclicBetween i.succ j.castSucc k ∧
      Q.owner = (tr.before i).turn ∧
      OnRay (kp 0 Q.owner.opponent) e b q ∧ OnRay (kp 0 Q.owner.opponent) e m B ∧ b < m ∧
      ∀ k' : Fin (tr.len + 1), cyclicBetween i.succ j.castSucc k' →
        (tr.states k').board.grid q = (tr.states i.succ).board.grid q ∧
        (tr.states k').board.grid B = some Q ∧ tr.GlaresAtEnemyKing kp k' B := by
  classical
  have hkp := tr.kingPos_eq_of_periodic kp ht hs hk hsafe h0 hc hr hp
  have hd := tr.boardMoveEndpointsDistinct_of_oriented hs hr
  obtain ⟨hocc, hngk, himm⟩ := hq
  -- Some move touches `q`.
  have hex : ∃ m : Fin tr.len, (tr.moves m).Touches q := by
    by_contra hnone
    push Not at hnone
    apply hocc
    rw [tr.grid_eq_of_untouched ht q (Fin.zero_le k) fun m _ _ => hnone m]
    by_contra h0q
    exact himm ⟨h0q, hnone⟩
  -- The last move touching `q` before `k`, cyclically, and `q` is unchanged since.
  obtain ⟨i, hti, hgrid, hcase⟩ : ∃ i : Fin tr.len, (tr.moves i).Touches q ∧
      (tr.states k).board.grid q = (tr.states i.succ).board.grid q ∧
      ((i.succ ≤ k ∧ ∀ m : Fin tr.len, i.succ ≤ m.castSucc → m.castSucc < k →
          ¬ (tr.moves m).Touches q) ∨
        (∀ m : Fin tr.len, (tr.moves m).Touches q → k ≤ m.castSucc ∧ m ≤ i)) := by
    by_cases hb : ∃ m : Fin tr.len, m.succ ≤ k ∧ (tr.moves m).Touches q
    · set S := Finset.univ.filter fun m : Fin tr.len => m.succ ≤ k ∧ (tr.moves m).Touches q
      have hS : S.Nonempty := by
        obtain ⟨m, hm⟩ := hb
        exact ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩⟩
      obtain ⟨hik, hti⟩ := (Finset.mem_filter.mp (S.max'_mem hS)).2
      have hun : ∀ m : Fin tr.len, (S.max' hS).succ ≤ m.castSucc → m.castSucc < k →
          ¬ (tr.moves m).Touches q := by
        intro m h1 h2 htm
        have hmk : m.succ ≤ k := by
          rw [Fin.le_def, Fin.val_succ]
          rw [Fin.lt_def, Fin.val_castSucc] at h2
          omega
        have hmS : m ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmk, htm⟩
        have hle := S.le_max' m hmS
        rw [Fin.le_def, Fin.val_succ, Fin.val_castSucc] at h1
        rw [Fin.le_def] at hle
        omega
      exact ⟨S.max' hS, hti, tr.grid_eq_of_untouched ht q hik hun, Or.inl ⟨hik, hun⟩⟩
    · push Not at hb
      set S := Finset.univ.filter fun m : Fin tr.len => (tr.moves m).Touches q
      have hS : S.Nonempty := by
        obtain ⟨m, hm⟩ := hex
        exact ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩⟩
      have hti := (Finset.mem_filter.mp (S.max'_mem hS)).2
      have hafter : ∀ m : Fin tr.len, (tr.moves m).Touches q →
          k ≤ m.castSucc ∧ m ≤ S.max' hS := by
        intro m htm
        refine ⟨?_, S.le_max' m (Finset.mem_filter.mpr ⟨Finset.mem_univ _, htm⟩)⟩
        by_contra hlt
        push Not at hlt
        apply hb m _ htm
        rw [Fin.le_def, Fin.val_succ]
        rw [Fin.lt_def, Fin.val_castSucc] at hlt
        omega
      -- `q` is unchanged from the last touch to the end, and from the start to `k`.
      have h1 : (tr.states (Fin.last tr.len)).board.grid q =
          (tr.states (S.max' hS).succ).board.grid q := by
        apply tr.grid_eq_of_untouched ht q (Fin.le_last _)
        intro m hm1 _ htm
        have hle := (hafter m htm).2
        rw [Fin.le_def, Fin.val_succ, Fin.val_castSucc] at hm1
        rw [Fin.le_def] at hle
        omega
      have h2 : (tr.states k).board.grid q = (tr.states 0).board.grid q :=
        tr.grid_eq_of_untouched ht q (Fin.zero_le k) fun m _ hm2 htm => by
          have := (hafter m htm).1
          exact absurd hm2 (not_lt.mpr this)
      refine ⟨S.max' hS, hti, ?_, Or.inr hafter⟩
      rw [h2, ← h1, show tr.states (Fin.last tr.len) = tr.states 0 from hp]
  -- That move put the piece on `q`.
  have hocci : (tr.states i.succ).board.grid q ≠ none := by
    rw [← hgrid]
    exact hocc
  have hngi : ¬ tr.GlaresAtEnemyKing kp i.succ q := fun h =>
    hngk ((tr.glaresAtEnemyKing_congr kp ht hgrid ((hkp _).trans (hkp _).symm)).mpr h)
  have hdi : (tr.moves i).destination = q := by
    rcases hmi : tr.moves i with ⟨src, dst, promote⟩ | ⟨pt, dst⟩
    · rw [hmi] at hti
      rcases hti with rfl | rfl
      · exact absurd (tr.boardMove_grid_src ht i q dst promote hmi (hd i q dst promote hmi)) hocci
      · rfl
    · rw [hmi] at hti
      exact hti.symm
  have hng : ¬ tr.GlaresAtEnemyKing kp i.succ (tr.moves i).destination := by
    rw [hdi]
    exact hngi
  obtain ⟨j, dst, promote, B, Q, e, b, m, hmj, hown, hray, hB, hbm, hall⟩ :=
    tr.openable_glaring_ray_cyclic_of_periodic kp ht hs hk hsafe h0 hc hr hp i hng
  rw [hdi] at hmj hray hall
  have htj : (tr.moves j).Touches q := by
    rw [hmj]
    exact Or.inl rfl
  have hji : j ≠ i := by
    rintro rfl
    rw [hmj] at hdi
    exact hd j q dst promote hmj hdi.symm
  refine ⟨i, j, dst, promote, B, Q, e, b, m, hdi, hngi, hmj, ?_, hown, hray, hB, hbm, hall⟩
  -- `k` lies between the arrival and the departure.
  have hji' : j.val ≠ i.val := fun h => hji (Fin.ext h)
  unfold cyclicBetween
  simp only [Fin.le_def, Fin.lt_def, Fin.val_succ, Fin.val_castSucc]
  rcases hcase with ⟨hik, hun⟩ | hafter
  · rw [Fin.le_def, Fin.val_succ] at hik
    by_cases hij : i.val < j.val
    · have hkj : k.val ≤ j.val := by
        by_contra hlt
        exact hun j (by rw [Fin.le_def, Fin.val_succ, Fin.val_castSucc]; omega)
          (by rw [Fin.lt_def, Fin.val_castSucc]; omega) htj
      omega
    · omega
  · obtain ⟨hkj, hjle⟩ := hafter j htj
    rw [Fin.le_def, Fin.val_castSucc] at hkj
    rw [Fin.le_def] at hjle
    omega

end MoveTrace
end MPC
