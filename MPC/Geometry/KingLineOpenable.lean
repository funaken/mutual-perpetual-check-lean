import MPC.Basic.Lemmas
import MPC.Geometry.OpenableLineCyclic
import MPC.Geometry.Line
/-!
# MPC.Geometry.KingLineOpenable

The paper's Proposition 3.5 on periodic traces: an openable piece never moves
onto the line through both kings.

Suppose a move puts a non-glaring piece on `A` and `A` lies on the line through
the enemy king `K` and the mover's king `L`. By Proposition 3.3 a piece `Q` of
the mover glares at `K` from a square `B` by sliding through `A`. So `B`, `A`,
`K`, `L` lie on one line: `A` strictly between `B` and `K`, and the own king `L`
not strictly between them, because it is immovable and the stripped board keeps
it (Remark 3.2). The mover was in check before the move. By Corollary 3.4 the
move lands on the checker's square or on its sliding line, and the checker's
path to `L` misses its own king `K`. If `L` lies beyond `K`, the checker's path
through `A` crosses `K`. If `L` lies beyond `B`, the path crosses `B`, where `Q`
already stood before the move. Either way the check was blocked, which is a
contradiction. A checker attacking by a step would have to stand on `A` itself,
and no step reaches two or more squares along a line.

The geometry is integer arithmetic along a unit direction. -/

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

private theorem sign_of_unit (x : ℤ) (h1 : -1 ≤ x) (h2 : x ≤ 1) : Int.sign x = x := by
  rcases (show x = -1 ∨ x = 0 ∨ x = 1 by omega) with rfl | rfl | rfl <;> rfl

namespace Geometry

/-- Collinearity does not depend on the order of the first two points. -/
theorem collinear_swap (a b c : Point) : collinear a b c ↔ collinear b a c := by
  unfold collinear
  have key : (a.1 - b.1) * (c.2 - b.2) - (c.1 - b.1) * (a.2 - b.2) =
      -((b.1 - a.1) * (c.2 - a.2) - (c.1 - a.1) * (b.2 - a.2)) := by ring
  constructor <;> intro h <;> linarith

end Geometry

/-- Every oriented step direction is a unit step or a knight's jump. -/
theorem stepDir_unit_or_knight (pt : PieceType) (o : Player) (d : Dir)
    (h : d ∈ pt.stepDirs.map (Dir.forPlayer · o)) :
    (-1 ≤ d.1 ∧ d.1 ≤ 1 ∧ -1 ≤ d.2 ∧ d.2 ≤ 1) ∨
      ((d.1 = 1 ∨ d.1 = -1) ∧ (d.2 = 2 ∨ d.2 = -2)) := by
  have key : ∀ x ∈ pt.stepDirs.map (Dir.forPlayer · o),
      (-1 ≤ x.1 ∧ x.1 ≤ 1 ∧ -1 ≤ x.2 ∧ x.2 ≤ 1) ∨
        ((x.1 = 1 ∨ x.1 = -1) ∧ (x.2 = 2 ∨ x.2 = -2)) := by
    cases o <;> cases pt <;> decide
  exact key d h

/-- If `A` lies `c ≠ 0` unit steps from `K` along `d` and `L` is collinear with
    `K` and `A`, then `L` also lies on that line through `K`. -/
theorem exists_line_param_of_collinear (K L A : Pos) (d : Dir) (c : ℤ)
    (hd : d ∈ PieceType.king.stepDirs) (hc : c ≠ 0)
    (hA : A.toInt = (K.toInt.1 + c * d.1, K.toInt.2 + c * d.2))
    (hcol : Geometry.collinear K.toInt L.toInt A.toInt) :
    ∃ t : ℤ, L.toInt = (K.toInt.1 + t * d.1, K.toInt.2 + t * d.2) := by
  have hA1 : A.toInt.1 - K.toInt.1 = c * d.1 := by rw [hA]; ring
  have hA2 : A.toInt.2 - K.toInt.2 = c * d.2 := by rw [hA]; ring
  unfold Geometry.collinear at hcol
  rw [hA1, hA2] at hcol
  have hkey : (L.toInt.1 - K.toInt.1) * d.2 = d.1 * (L.toInt.2 - K.toInt.2) := by
    have e : c * ((L.toInt.1 - K.toInt.1) * d.2 - d.1 * (L.toInt.2 - K.toInt.2)) =
        (L.toInt.1 - K.toInt.1) * (c * d.2) - c * d.1 * (L.toInt.2 - K.toInt.2) := by ring
    rw [hcol, sub_self] at e
    rcases mul_eq_zero.mp e with h | h
    · exact absurd h hc
    · linarith
  obtain ⟨d1, d2⟩ := d
  rw [PieceType.mem_king_stepDirs_iff] at hd
  dsimp only at hd hkey ⊢
  refine ⟨(L.toInt.1 - K.toInt.1) * d1 + (L.toInt.2 - K.toInt.2) * d2 * (1 - d1 * d1), ?_⟩
  rcases (show d1 = -1 ∨ d1 = 0 ∨ d1 = 1 by omega) with rfl | rfl | rfl <;>
    rcases (show d2 = -1 ∨ d2 = 0 ∨ d2 = 1 by omega) with rfl | rfl | rfl <;>
    simp only [Prod.ext_iff] <;> constructor <;> omega

/-- Forward case of `mem_slidePath_of_between`. -/
private theorem mem_slidePath_of_between_fwd (B A L Z : Pos) (d : Dir) (j u z : ℤ)
    (hd : d ∈ PieceType.king.stepDirs)
    (hA : A.toInt = (B.toInt.1 + j * d.1, B.toInt.2 + j * d.2))
    (hL : L.toInt = (B.toInt.1 + u * d.1, B.toInt.2 + u * d.2))
    (hZ : Z.toInt = (B.toInt.1 + z * d.1, B.toInt.2 + z * d.2))
    (hjz : j < z) (hzu : z < u) : Z.toInt ∈ slidePath A L := by
  have hu := (PieceType.mem_king_stepDirs_iff d).mp hd
  have hd0 : d ≠ (0, 0) := fun h => hu.2.2.2.2 ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  have hn : 1 ≤ (u - j).toNat := by omega
  have hcast : (((u - j).toNat : ℕ) : ℤ) = u - j := Int.toNat_of_nonneg (by omega)
  have hx : L.toInt.1 = A.toInt.1 + ↑(u - j).toNat * d.1 := by
    rw [hcast, hL, hA]
    ring
  have hy : L.toInt.2 = A.toInt.2 + ↑(u - j).toNat * d.2 := by
    rw [hcast, hL, hA]
    ring
  have hdir : (Pos.dirTo A L).normalize = d := by
    have e1 : (Pos.dirTo A L).1 = (u - j) * d.1 := by
      change L.toInt.1 - A.toInt.1 = _
      rw [hL, hA]
      ring
    have e2 : (Pos.dirTo A L).2 = (u - j) * d.2 := by
      change L.toInt.2 - A.toInt.2 = _
      rw [hL, hA]
      ring
    change (Int.sign (Pos.dirTo A L).1, Int.sign (Pos.dirTo A L).2) = d
    rw [e1, e2, Int.sign_mul, Int.sign_mul, Int.sign_eq_one_of_pos (by omega), one_mul, one_mul,
      sign_of_unit _ hu.1 hu.2.1, sign_of_unit _ hu.2.2.1 hu.2.2.2.1]
  refine (mem_slidePath_iff_of_exact_steps A L d (u - j).toNat hd0 hn hdir hx hy _).mpr
    ⟨(z - j).toNat, by omega, by omega, ?_⟩
  have hc2 : (((z - j).toNat : ℕ) : ℤ) = z - j := Int.toNat_of_nonneg (by omega)
  rw [hc2, hZ, hA]
  ext <;> simp only <;> ring

/-- Three points `A`, `L`, `Z` on a line through `B` with unit direction `d`, at
    parameters `j`, `u`, `z`: if `z` lies strictly between `j` and `u`, then `Z`
    is on the slide path from `A` to `L`. -/
theorem mem_slidePath_of_between (B A L Z : Pos) (d : Dir) (j u z : ℤ)
    (hd : d ∈ PieceType.king.stepDirs)
    (hA : A.toInt = (B.toInt.1 + j * d.1, B.toInt.2 + j * d.2))
    (hL : L.toInt = (B.toInt.1 + u * d.1, B.toInt.2 + u * d.2))
    (hZ : Z.toInt = (B.toInt.1 + z * d.1, B.toInt.2 + z * d.2))
    (hz : (j < z ∧ z < u) ∨ (u < z ∧ z < j)) : Z.toInt ∈ slidePath A L := by
  rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact mem_slidePath_of_between_fwd B A L Z d j u z hd hA hL hZ h1 h2
  · have hd' : ((-d.1, -d.2) : Dir) ∈ PieceType.king.stepDirs := by
      rw [PieceType.mem_king_stepDirs_iff] at hd ⊢
      dsimp only
      omega
    refine mem_slidePath_of_between_fwd B A L Z (-d.1, -d.2) (-j) (-u) (-z) hd' ?_ ?_ ?_
      (by omega) (by omega)
    · rw [hA]; ext <;> simp only <;> ring
    · rw [hL]; ext <;> simp only <;> ring
    · rw [hZ]; ext <;> simp only <;> ring

/-- The end of a cyclic interval belongs to it. -/
theorem cyclicBetween_self_right {n : ℕ} (a b : Fin (n + 1)) : cyclicBetween a b b := by
  rcases le_or_gt a b with h | h
  · exact Or.inl ⟨h, h, le_refl b⟩
  · exact Or.inr ⟨h, Or.inr (le_refl b)⟩

private theorem collinear_kings (kp0 : Player → Pos) (p : Player) (A : Pos)
    (h : Geometry.collinear (kp0 .sente).toInt (kp0 .gote).toInt A.toInt) :
    Geometry.collinear (kp0 p.opponent).toInt (kp0 p).toInt A.toInt := by
  cases p
  · exact (Geometry.collinear_swap _ _ _).mp h
  · exact h

namespace MoveTrace

/-- In a periodic mutual-check trace, the mover is in check before every move:
    the previous move checked it, and before the first move the last one did. -/
theorem inCheck_before_of_periodic (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hk : tr.KingsWellPlaced kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hp : tr.IsPeriodic) (i : Fin tr.len) :
    inCheckOriented (tr.before i).board (tr.before i).turn
      (kp i.castSucc (tr.before i).turn) := by
  obtain ⟨n, hn⟩ := i
  cases n with
  | zero =>
    let l : Fin tr.len := ⟨tr.len - 1, by omega⟩
    have hls : l.succ = Fin.last tr.len := Fin.ext (by simp [l]; omega)
    have hperiod : tr.states (Fin.last tr.len) = tr.states 0 := hp
    have hturn : (tr.before l).turn.opponent = (tr.states 0).turn := by
      rw [← tr.turn_after_move ht l]
      change (tr.states l.succ).turn = _
      rw [hls, hperiod]
    have h := hc l
    change inCheckOriented (tr.states l.succ).board _ _ at h
    rw [hturn, hls, hperiod, hp.kingPos_last hk] at h
    exact h
  | succ n =>
    let i' : Fin tr.len := ⟨n, by omega⟩
    have hsucc : i'.succ = (⟨n + 1, hn⟩ : Fin tr.len).castSucc := Fin.ext rfl
    have hturn : (tr.before i').turn.opponent = (tr.before ⟨n + 1, hn⟩).turn := by
      rw [← tr.turn_after_move ht i']
      change (tr.states i'.succ).turn = (tr.states (⟨n + 1, hn⟩ : Fin tr.len).castSucc).turn
      rw [hsucc]
    have h := hc i'
    change inCheckOriented (tr.states i'.succ).board _ _ at h
    rw [hturn, hsucc] at h
    exact h

/-- Proposition 3.5: in a periodic trace satisfying 's premises, a move that
    puts a non-glaring piece on its destination never lands on the line through
    both kings. -/
theorem openable_destination_off_kingLine_of_periodic (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hr : tr.BoardMovesFollowCanMoveToOriented)
    (hp : tr.IsPeriodic) (i : Fin tr.len)
    (hng : ¬ tr.GlaresAtEnemyKing kp i.succ (tr.moves i).destination) :
    ¬ Geometry.collinear (kp 0 .sente).toInt (kp 0 .gote).toInt
      (tr.moves i).destination.toInt := by
  intro hcol
  have hkp := tr.kingPos_eq_of_periodic kp ht hs hk hsafe h0 hc hr hp
  have hd := tr.boardMoveEndpointsDistinct_of_oriented hs hr
  -- Proposition 3.3 and the arriving piece.
  obtain ⟨j, dstj, prj, B, Q, hmj, hown, hmem, hall⟩ :=
    tr.openable_glaring_line_cyclic_of_periodic kp ht hs hk hsafe h0 hc hr hp i hng
  obtain ⟨P, hP, hPo⟩ := tr.destination_piece_owner ht hs i
  -- The mover was in check before the move; Corollary 3.4 places the destination.
  obtain ⟨C, X, hX, hXo, hatkX⟩ := tr.inCheck_before_of_periodic kp ht hk hc hp i
  have hcor := tr.destination_on_checker_line kp ht hs hsafe i
    (by rw [hkp i.succ, hkp i.castSucc]) C X hX hXo hatkX
  -- The move itself, for later grid updates.
  have hmove : ∀ q : Pos, q ≠ (tr.moves i).destination →
      (tr.states i.succ).board.grid q ≠ none →
      (tr.states i.castSucc).board.grid q = (tr.states i.succ).board.grid q := by
    intro q hq hocc
    have key : ∀ mv : Move, tr.moves i = mv →
        (tr.states i.castSucc).board.grid q = (tr.states i.succ).board.grid q := by
      intro mv hm
      rw [hm] at hq
      cases mv with
      | boardMove src dst promote =>
        have hqs : q ≠ src := by
          rintro rfl
          exact hocc (tr.boardMove_grid_src ht i q dst promote hm (hd i q dst promote hm))
        exact (tr.boardMove_grid_other ht i src dst promote q hm hqs hq).symm
      | dropMove pt dst =>
        exact (tr.dropMove_grid_other ht i pt dst q hm hq).symm
    exact key _ rfl
  generalize (tr.moves i).destination = A at hng hcol hmj hmem hall hP hcor hmove
  obtain ⟨L, hLdef⟩ : ∃ L, L = kp 0 (tr.before i).turn := ⟨_, rfl⟩
  obtain ⟨K, hKdef⟩ : ∃ K, K = kp 0 (tr.before i).turn.opponent := ⟨_, rfl⟩
  obtain ⟨hQ1, hgl1⟩ := (hall i.succ (cyclicBetween_self_left _ _)).2
  obtain ⟨hAj, hQj, _⟩ := hall j.castSucc (cyclicBetween_self_right _ _)
  -- The departing side is the mover of `i`.
  have hturn : (tr.before j).turn = (tr.before i).turn := by
    obtain ⟨piece, hpiece, ho⟩ := hs j A dstj prj hmj
    change (tr.states j.castSucc).board.grid A = some piece at hpiece
    rw [hAj, hP] at hpiece
    cases hpiece
    exact ho.symm.trans hPo
  have hQo : Q.owner = (tr.before i).turn := hown
  have hKQ : kp 0 Q.owner.opponent = K := by rw [hQo, hKdef]
  -- `Q` does not attack `K` by a step.
  have hstepQ : Pos.dirTo B K ∉ Q.pieceType.stepDirs.map (Dir.forPlayer · Q.owner) := by
    have h := tr.not_stepAttack_of_before kp ht hsafe h0 j B Q hQj (hQo.trans hturn.symm)
    rw [hkp j.castSucc, hturn, ← hKdef] at h
    exact h
  -- `Q` glares at `K` by sliding: `A` lies strictly between `B` and `K`.
  obtain ⟨Q', hQ', hatkQ⟩ := hgl1
  rw [hQ1] at hQ'
  cases hQ'
  rw [hkp i.succ, hKQ] at hatkQ
  rcases hatkQ with hst | ⟨sd, hsd, hnorm, n, hn, hx, hy, hpc⟩
  · exact hstepQ hst
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
  rw [hKQ] at hmem
  obtain ⟨j0, hj1, hjn, hAeq⟩ := (hiff A.toInt).mp hmem
  -- Remark 3.2: the own king `L` is not strictly between `B` and `K`.
  have himmL : tr.ImmovableAt L := by
    rw [hLdef]
    exact tr.immovableAt_kingPos_of_periodic kp ht hs hk hsafe h0 hc hr hp _
  have hLking : (tr.states i.succ).board.grid L = some ⟨(tr.before i).turn, .king⟩ := by
    rw [hLdef, ← hkp i.succ]
    exact (hk i.succ).king_present _
  have hLnot : L.toInt ∉ slidePath B K := by
    intro hLmem
    have h := hpc L.toInt hLmem (Pos.onBoard_toInt L) (Pos.onBoard_toInt L)
    rw [Pos.toPos_toInt] at h
    simp only [strippedBoard] at h
    rw [ite_eq_left (Or.inr himmL), hLking] at h
    cases h
  -- `L` is on the line through `B` and `K`.
  have hcolKL : Geometry.collinear K.toInt L.toInt A.toInt := by
    rw [hKdef, hLdef]
    exact collinear_kings (kp 0) _ A hcol
  obtain ⟨t, hLt⟩ := exists_line_param_of_collinear K L A sd ((j0 : ℤ) - n) hsdK
    (by omega) (by
      rw [hAeq]
      ext
      · show B.toInt.1 + ↑j0 * sd.1 = K.toInt.1 + (↑j0 - ↑n) * sd.1
        rw [hKx]; ring
      · show B.toInt.2 + ↑j0 * sd.2 = K.toInt.2 + (↑j0 - ↑n) * sd.2
        rw [hKy]; ring) hcolKL
  have hLu : L.toInt = (B.toInt.1 + (↑n + t) * sd.1, B.toInt.2 + (↑n + t) * sd.2) := by
    rw [hLt]
    ext
    · show K.toInt.1 + t * sd.1 = B.toInt.1 + (↑n + t) * sd.1
      rw [hKx]; ring
    · show K.toInt.2 + t * sd.2 = B.toInt.2 + (↑n + t) * sd.2
      rw [hKy]; ring
  -- `L` is neither `K` nor `B`, and not strictly between them.
  have ht0 : t ≠ 0 := by
    intro h0'
    rw [h0', zero_mul, zero_mul, add_zero, add_zero] at hLt
    have hLK : L = K := pos_eq_of_toInt hLt
    rw [hLdef, hKdef] at hLK
    exact Player.opponent_ne_self _ ((hk 0).positions_injective hLK).symm
  have hu0 : (n : ℤ) + t ≠ 0 := by
    intro h0'
    rw [h0', zero_mul, zero_mul, add_zero, add_zero] at hLu
    have hLB : L = B := pos_eq_of_toInt hLu
    rw [hLB, hQ1] at hLking
    cases hLking
    simp [PieceType.slideDirs] at hsd
  have hside : (n : ℤ) < n + t ∨ (n : ℤ) + t < 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨hlt, hge⟩ := hcon
    apply hLnot
    refine (hiff L.toInt).mpr ⟨(↑n + t).toNat, by omega, by omega, ?_⟩
    rw [hLu, Int.toNat_of_nonneg (by omega)]
  -- `Q` was already on `B` before the move.
  have hQi : (tr.states i.castSucc).board.grid B = some Q := by
    have hBA : B ≠ A := by
      rintro rfl
      exact hng ⟨Q, hQ1, by
        rw [hkp i.succ, hKQ]
        exact Or.inr ⟨sd, hsd, hnorm, n, hn, hx, hy, hpc⟩⟩
    rw [hmove B hBA (by rw [hQ1]; exact Option.some_ne_none _)]
    exact hQ1
  -- The checker before the move attacked `L`.
  have hLi : kp i.castSucc (tr.before i).turn = L := by rw [hkp i.castSucc, hLdef]
  rw [hLi] at hatkX hcor
  -- A square strictly between `A` and `L` that was occupied before the move:
  -- `K` when `L` lies beyond `K`, and `B` when `L` lies beyond `B`.
  obtain ⟨Z, z, hZ, hZocc, hzb⟩ : ∃ (Z : Pos) (z : ℤ),
      Z.toInt = (B.toInt.1 + z * sd.1, B.toInt.2 + z * sd.2) ∧
      (tr.states i.castSucc).board.grid Z ≠ none ∧
      (((j0 : ℤ) < z ∧ z < n + t) ∨ ((n : ℤ) + t < z ∧ z < j0)) := by
    rcases hside with h | h
    · refine ⟨K, n, Prod.ext hKx hKy, ?_, Or.inl ⟨by omega, h⟩⟩
      rw [hKdef, ← hkp i.castSucc, (hk i.castSucc).king_present]
      exact Option.some_ne_none _
    · refine ⟨B, 0, by simp, by rw [hQi]; exact Option.some_ne_none _, Or.inr ⟨h, by omega⟩⟩
  have hZmem : Z.toInt ∈ slidePath A L :=
    mem_slidePath_of_between B A L Z sd j0 (↑n + t) z hsdK hAeq hLu hZ hzb
  rcases hatkX with hstX | ⟨sd', hsd', hnorm', m', hm', hx', hy', hpc'⟩
  · -- A step check comes from `A` itself, two or more steps from `L`.
    rcases hcor with hAC | ⟨_, hns⟩
    · rw [← hAC] at hstX
      have e1 : (Pos.dirTo A L).1 = (↑n + t - ↑j0) * sd.1 := by
        change L.toInt.1 - A.toInt.1 = _
        rw [hLu, hAeq]
        ring
      have e2 : (Pos.dirTo A L).2 = (↑n + t - ↑j0) * sd.2 := by
        change L.toInt.2 - A.toInt.2 = _
        rw [hLu, hAeq]
        ring
      have hshape := stepDir_unit_or_knight _ _ _ hstX
      rw [e1, e2] at hshape
      rcases (show sd.1 = -1 ∨ sd.1 = 0 ∨ sd.1 = 1 by omega) with h1 | h1 | h1 <;>
        rcases (show sd.2 = -1 ∨ sd.2 = 0 ∨ sd.2 = 1 by omega) with h2 | h2 | h2 <;>
        rw [h1, h2] at hshape <;> omega
    · exact hns hstX
  · -- A sliding check passes `Z`, which was occupied.
    have hd0' : sd' ≠ (0, 0) := by
      have hu' := (PieceType.mem_king_stepDirs_iff sd').mp (slide_mem_king _ _ sd' hsd')
      exact fun h => hu'.2.2.2.2 ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    have hxC : L.toInt.1 = C.toInt.1 + ↑m' * sd'.1 := by
      dsimp [Pos.dirTo, Pos.toInt] at hx' ⊢
      omega
    have hyC : L.toInt.2 = C.toInt.2 + ↑m' * sd'.2 := by
      dsimp [Pos.dirTo, Pos.toInt] at hy' ⊢
      omega
    have hZC : Z.toInt ∈ slidePath C L := by
      rcases hcor with hAC | ⟨hAmem, _⟩
      · rw [← hAC]
        exact hZmem
      · exact (mem_slidePath_of_mem_tail C A L sd' m' hd0' hm' hnorm' hxC hyC hAmem Z.toInt
          hZmem).1
    have h := hpc' Z.toInt hZC (Pos.onBoard_toInt Z) (Pos.onBoard_toInt Z)
    rw [Pos.toPos_toInt] at h
    exact hZocc h

end MoveTrace
end MPC
