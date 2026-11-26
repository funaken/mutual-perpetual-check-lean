import MPC.Basic.Lemmas
import MPC.Pieces.SilverLemma
/-!
# MPC.Pieces.RookDragonLemma

The paper's Lemma 5.2 on periodic traces: no rook or dragon is moved by a
discovered check. It uses Proposition 4.1
(`DiscoveredCheckByEachSide`) and the piece counts (`PieceCountsAtMostTwo`), and
treats both sides at once.

**Behind an openable rook or dragon stands a bishop or horse**
(`bishopHorse_behind_openable_rookDragon_of_periodic`). By coverage and
Proposition 3.3, a piece `Q` of the same side glares at the enemy king `K` through
the openable square `q`, from farther along `q`'s half-line, and slides back along
it. If that half-line ran along a rank or file, the squares between `q` and `K`
would be as empty on `q`'s stripped board as on `Q`'s, so the rook or dragon on `q`
would glare itself. So the half-line is diagonal and `Q` is a bishop or a horse.

**The contradiction** (`not_openableMove_rookDragon_of_periodic`).
- When a non-glaring rook or dragon of `o` moves, its source and destination lie
  on different half-lines. Right after the move a bishop or horse of `o`
  glares through each, on two different squares. By the piece counts these are
  all the bishops and horses on the board, so none of them is non-glaring. By
   there is then no non-glaring bishop or horse in any state.
- By Proposition 4.1 the opponent also makes a discovered check. That piece is not
  a king (Proposition 2.2), a knight, lance, or pawn, a gold-type piece, a silver, or a bishop or horse (just shown). So it is a rook
  or a dragon.
- The number of openable rooks and dragons of the opponent is the same in every
  state, so one stands right after `o`'s move. Behind it a bishop or horse
  of the opponent glares at `o`'s king. That makes three bishop/horse squares,
  against the piece counts.
-/

namespace MPC

private theorem toInt_toPos (q : ℤ × ℤ) (h : onBoard q) : (toPos q h).toInt = q := by
  obtain ⟨h1, _, h2, _⟩ := h
  ext
  · simp [toPos, Pos.toInt]; omega
  · simp [toPos, Pos.toInt]; omega

/-- Rooks and dragons slide along every rank and file direction. -/
theorem orth_mem_rookDragon_slideDirs (pt : PieceType) (o : Player) (sd : Dir)
    (hpt : pt = .rook ∨ pt = .dragon) (hsd : sd ∈ PieceType.king.stepDirs)
    (horth : sd.1 = 0 ∨ sd.2 = 0) : sd ∈ pt.slideDirs.map (Dir.forPlayer · o) := by
  have key : ∀ x ∈ PieceType.king.stepDirs, (x.1 = 0 ∨ x.2 = 0) →
      x ∈ pt.slideDirs.map (Dir.forPlayer · o) := by
    rcases hpt with rfl | rfl <;> cases o <;> decide
  exact key sd hsd horth

/-- A diagonal slider is a bishop or a horse. -/
theorem bishopHorse_of_slideDir (pt : PieceType) (o : Player) (sd : Dir)
    (h : sd ∈ pt.slideDirs.map (Dir.forPlayer · o)) (h1 : sd.1 ≠ 0) (h2 : sd.2 ≠ 0) :
    pt = .bishop ∨ pt = .horse := by
  have key : ∀ x ∈ pt.slideDirs.map (Dir.forPlayer · o), x.1 ≠ 0 → x.2 ≠ 0 →
      pt = .bishop ∨ pt = .horse := by
    cases o <;> cases pt <;> decide
  exact key sd h h1 h2

/-- Normalizing a positive multiple of a king direction gives the direction. -/
theorem normalize_mul_of_king_step {d : Dir} (hd : d ∈ PieceType.king.stepDirs) {b : ℤ}
    (hb : 0 < b) : Dir.normalize (b * d.1, b * d.2) = d := by
  obtain ⟨d1, d2⟩ := d
  rw [PieceType.mem_king_stepDirs_iff] at hd
  dsimp only at hd
  have hs : Int.sign b = 1 := Int.sign_eq_one_of_pos hb
  rcases (show d1 = -1 ∨ d1 = 0 ∨ d1 = 1 by omega) with rfl | rfl | rfl <;>
    rcases (show d2 = -1 ∨ d2 = 0 ∨ d2 = 1 by omega) with rfl | rfl | rfl <;>
    simp [Dir.normalize, hs, Int.sign_neg]

namespace MoveTrace

/-- A square holding a bishop or a horse belongs to `bishopHorseSquares`. -/
theorem mem_bishopHorseSquares_of (tr : MoveTrace) (k : Fin (tr.len + 1)) (q : Pos) (P : Piece)
    (hq : (tr.states k).board.grid q = some P)
    (hP : P.pieceType = .bishop ∨ P.pieceType = .horse) : q ∈ tr.bishopHorseSquares k := by
  simp only [bishopHorseSquares, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨P, hq, hP⟩

/-- In a periodic trace satisfying the periodic-check premises, behind an openable rook or dragon
    stands a glaring bishop or horse of the same side, farther along the rook's
    half-line from the enemy king. -/
theorem bishopHorse_behind_openable_rookDragon_of_periodic (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hr : tr.BoardMovesFollowCanMoveToOriented)
    (hp : tr.IsPeriodic) (k : Fin (tr.len + 1)) (q : Pos) (hq : tr.IsOpenableAt kp k q)
    (P : Piece) (hP : (tr.states k).board.grid q = some P)
    (hpt : P.pieceType = .rook ∨ P.pieceType = .dragon) :
    ∃ (B : Pos) (Q : Piece) (e : Dir) (b m : ℤ), (tr.states k).board.grid B = some Q ∧
      Q.owner = P.owner ∧ (Q.pieceType = .bishop ∨ Q.pieceType = .horse) ∧
      tr.GlaresAtEnemyKing kp k B ∧ OnRay (kp 0 P.owner.opponent) e b q ∧
      OnRay (kp 0 P.owner.opponent) e m B ∧ b < m := by
  have hkp := tr.kingPos_eq_of_periodic kp ht hs hk hsafe h0 hc hr hp
  obtain ⟨i, j, dst, pr, B, Q, e, b, m, hdi, _, hmj, hcyc, hown, hray, hB, hbm, hall⟩ :=
    tr.openable_covered_of_periodic kp ht hs hk hsafe h0 hc hr hp k q hq
  obtain ⟨hqk, hQk, hglk⟩ := hall k hcyc
  -- `P` is the arriving piece, so `Q` and `P` belong to the mover of `i`.
  have hPown : P.owner = (tr.before i).turn := by
    obtain ⟨P', hP', hP'o⟩ := tr.destination_piece_owner ht hs i
    rw [hdi, ← hqk, hP] at hP'
    cases hP'
    exact hP'o
  have hQP : Q.owner = P.owner := hown.trans hPown.symm
  rw [hQP] at hray hB
  -- `Q` does not attack by a step: it stands on `B` before the departure `j`.
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
  have hatkQ0 := hatkQ
  rw [hkp k, hQP] at hatkQ
  rw [hQP] at hstep
  have hslide := slideDir_of_attack_not_step _ _ _ B _ hatkQ hstep hB
  obtain ⟨d', n', hB', _, hiff⟩ := ray_of_attack_not_step _ _ _ B _ hatkQ hstep
  obtain ⟨hd', hn'⟩ := OnRay.unique hB' hB
  subst hd'
  subst hn'
  refine ⟨B, Q, d', b, n', hQk, hQP, ?_, ⟨Q, hQk, ?_⟩, hray, hB, hbm⟩
  · -- Along a rank or file, the rook or dragon on `q` would glare itself.
    have he := (PieceType.mem_king_stepDirs_iff d').mp hB.1
    by_cases horth : d'.1 = 0 ∨ d'.2 = 0
    · exfalso
      apply hq.2.1
      refine ⟨P, hP, ?_⟩
      rw [hkp k]
      obtain ⟨_, hb0, hqe⟩ := hray
      have hsd : ((-d'.1, -d'.2) : Dir) ∈ P.pieceType.slideDirs.map (Dir.forPlayer · P.owner) :=
        orth_mem_rookDragon_slideDirs _ _ _ hpt (neg_mem_king_stepDirs hB.1)
          (by dsimp only; omega)
      have hdir : Pos.dirTo q (kp 0 P.owner.opponent) = (b * -d'.1, b * -d'.2) := by
        simp only [Pos.dirTo]
        have h1 := congrArg Prod.fst hqe
        have h2 := congrArg Prod.snd hqe
        simp only [Pos.toInt] at h1 h2
        ext <;> dsimp only <;> linarith
      obtain ⟨bn, hbn⟩ := Int.eq_ofNat_of_zero_le hb0.le
      have hnorm : (Pos.dirTo q (kp 0 P.owner.opponent)).normalize = (-d'.1, -d'.2) := by
        rw [hdir]
        exact normalize_mul_of_king_step (neg_mem_king_stepDirs hB.1) hb0
      have hd0 : ((-d'.1, -d'.2) : Dir) ≠ (0, 0) := by
        intro h
        have h1 := congrArg Prod.fst h
        have h2 := congrArg Prod.snd h
        dsimp only at h1 h2
        omega
      have hKx : (kp 0 P.owner.opponent).toInt.1 = q.toInt.1 + ↑bn * -d'.1 := by
        have := congrArg Prod.fst hqe
        dsimp only at this
        rw [← hbn]
        linarith
      have hKy : (kp 0 P.owner.opponent).toInt.2 = q.toInt.2 + ↑bn * -d'.2 := by
        have := congrArg Prod.snd hqe
        dsimp only at this
        rw [← hbn]
        linarith
      refine Or.inr ⟨(-d'.1, -d'.2), hsd, hnorm, bn, by omega, ?_, ?_, ?_⟩
      · rw [hdir, ← hbn]
      · rw [hdir, ← hbn]
      · -- The squares between `q` and the king are empty on `Q`'s stripped board.
        rw [pathClear_iff_of_exact_steps _ q _ (-d'.1, -d'.2) bn hd0 (by omega) hnorm hKx hKy]
        intro jj hj1 hjn hob
        set R := toPos _ hob with hRdef
        have hRint : R.toInt = ((kp 0 P.owner.opponent).toInt.1 + (b - jj) * d'.1,
            (kp 0 P.owner.opponent).toInt.2 + (b - jj) * d'.2) := by
          rw [hRdef, toInt_toPos]
          have h1 := congrArg Prod.fst hqe
          have h2 := congrArg Prod.snd hqe
          ext <;> dsimp only at h1 h2 ⊢ <;> linarith
        have hRmem : R.toInt ∈ slidePath B (kp 0 P.owner.opponent) :=
          (hiff _).mpr ⟨b - jj, by omega, by omega, hRint⟩
        have hpcB : pathClear (tr.strippedBoard k B) B (kp 0 P.owner.opponent) := by
          rcases hatkQ with hst | ⟨_, _, _, _, _, _, _, hpc⟩
          · exact absurd hst hstep
          · exact hpc
        have hRe := hpcB R.toInt hRmem (Pos.onBoard_toInt R) (Pos.onBoard_toInt R)
        rw [Pos.toPos_toInt] at hRe
        -- A nonzero multiple of a king direction is nonzero.
        have hnz : ∀ t : ℤ, t ≠ 0 → t * d'.1 = 0 → t * d'.2 = 0 → False := by
          intro t ht h1 h2
          rcases mul_eq_zero.mp h1 with h | h
          · exact ht h
          rcases mul_eq_zero.mp h2 with h' | h'
          · exact ht h'
          exact he.2.2.2.2 ⟨h, h'⟩
        have hRq : R ≠ q := by
          intro h
          have := congrArg Pos.toInt h
          rw [hRint, hqe] at this
          have h1 := congrArg Prod.fst this
          have h2 := congrArg Prod.snd this
          dsimp only at h1 h2
          exact hnz (jj : ℤ) (by omega) (by linarith) (by linarith)
        have hRB' : R ≠ B := by
          intro h
          have := congrArg Pos.toInt h
          rw [hRint, hB.2.2] at this
          have h1 := congrArg Prod.fst this
          have h2 := congrArg Prod.snd this
          dsimp only at h1 h2
          exact hnz (n' - b + jj) (by omega) (by linarith) (by linarith)
        simp only [strippedBoard] at hRe ⊢
        by_cases himm : tr.ImmovableAt R
        · rw [ite_eq_left (Or.inr himm)] at hRe
          rw [ite_eq_left (Or.inr himm)]
          exact hRe
        · rw [ite_eq_right (by rintro (h | h); exact hRq h; exact himm h)]
    · -- Diagonally, `Q` slides diagonally.
      push Not at horth
      exact bishopHorse_of_slideDir _ _ _ hslide (by dsimp only; omega) (by dsimp only; omega)
  · exact hatkQ0

/-- Three distinct bishop-or-horse squares in one state contradict the piece counts. -/
theorem false_of_three_bishopHorse (tr : MoveTrace) (hcount : tr.PieceCountsAtMostTwo)
    (k : Fin (tr.len + 1)) (q1 q2 q3 : Pos) (h12 : q1 ≠ q2) (h13 : q1 ≠ q3) (h23 : q2 ≠ q3)
    (h1 : q1 ∈ tr.bishopHorseSquares k) (h2 : q2 ∈ tr.bishopHorseSquares k)
    (h3 : q3 ∈ tr.bishopHorseSquares k) : False := by
  have hsub : ({q1, q2, q3} : Finset Pos) ⊆ tr.bishopHorseSquares k := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
  have hcard : ({q1, q2, q3} : Finset Pos).card = 3 :=
    Finset.card_eq_three.mpr ⟨q1, q2, q3, h12, h13, h23, rfl⟩
  have := Finset.card_le_card hsub
  have := (hcount k).1
  omega

/-- Lemma 5.2: in a periodic mutual-check trace with Proposition 4.1 and
    the piece counts, no rook or dragon of either side is moved by a discovered
    check. -/
theorem not_openableMove_rookDragon_of_periodic (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos) (hm : tr.MutualPerpetualCheck kp)
    (h41 : tr.DiscoveredCheckByEachSide kp) (hcount : tr.PieceCountsAtMostTwo) (o : Player)
    (pt : PieceType) (hpt : pt = .rook ∨ pt = .dragon) : ¬ tr.OpenableMoveBy kp o pt := by
  have hm' := hm
  obtain ⟨ht, hs, hk, hsafe, h0, hc, hr, hp, _, _⟩ := hm
  have hkp := tr.kingPos_eq_of_periodic kp ht hs hk hsafe h0 hc hr hp
  rintro ⟨i, src, dst, promote, hturn, hmv, hsrc, hng, _⟩
  let p : Piece := ⟨o, pt⟩
  -- A bishop or horse of `o` behind the source, before the move.
  have hsrcOpen : tr.IsOpenableAt kp i.castSucc src := by
    refine ⟨?_, hng, fun himm => himm.2 i (by rw [hmv]; exact Or.inl rfl)⟩
    change (tr.before i).board.grid src ≠ none
    rw [hsrc]
    exact Option.some_ne_none _
  obtain ⟨B1, Q1, e1, b1, m1, hQ1, hQ1o, hQ1t, hgl1, hray1, hB1, hbm1⟩ :=
    tr.bishopHorse_behind_openable_rookDragon_of_periodic kp ht hs hk hsafe h0 hc hr hp
      i.castSucc src hsrcOpen p hsrc hpt
  -- A bishop or horse of `o` behind the destination, after the move.
  have hdstgrid : (tr.states i.succ).board.grid dst = some p := by
    change (tr.after i).board.grid dst = some p
    rw [tr.boardMove_grid_dst_eq_of_not_glares_of_periodic kp ht hs hk hsafe h0 hc hr hp i src dst
      promote hmv hng]
    exact hsrc
  have hngd : ¬ tr.GlaresAtEnemyKing kp i.succ dst := fun hg =>
    hng (tr.glares_source_of_glares_destination_of_periodic kp ht hs hk hsafe h0 hc hr hp i src
      dst promote hmv hg)
  have hdstOpen : tr.IsOpenableAt kp i.succ dst := by
    refine ⟨?_, hngd, fun himm => himm.2 i (by rw [hmv]; exact Or.inr rfl)⟩
    rw [hdstgrid]
    exact Option.some_ne_none _
  obtain ⟨B2, Q2, e2, b2, m2, hQ2, hQ2o, hQ2t, hgl2, hray2, hB2, hbm2⟩ :=
    tr.bishopHorse_behind_openable_rookDragon_of_periodic kp ht hs hk hsafe h0 hc hr hp
      i.succ dst hdstOpen p hdstgrid hpt
  change OnRay (kp 0 o.opponent) e1 b1 src at hray1
  change OnRay (kp 0 o.opponent) e1 m1 B1 at hB1
  change OnRay (kp 0 o.opponent) e2 b2 dst at hray2
  change OnRay (kp 0 o.opponent) e2 m2 B2 at hB2
  -- The two half-lines differ.
  obtain ⟨d, e, a, b, hsr, hdr, hed, _⟩ :=
    tr.openable_move_rays_of_periodic kp ht hs hk hsafe h0 hc hr hp i src dst promote hmv hng
  rw [hturn] at hsr hdr
  obtain ⟨he1, _⟩ := OnRay.unique hray1 hsr
  obtain ⟨he2, _⟩ := OnRay.unique hray2 hdr
  subst he1
  subst he2
  have hB1s : B1 ≠ src := by
    rintro rfl
    have := (OnRay.unique hB1 hray1).2
    omega
  have hB1d : B1 ≠ dst := by
    rintro rfl
    exact hed (OnRay.unique hB1 hray2).1.symm
  have h12 : B1 ≠ B2 := by
    rintro rfl
    exact hed (OnRay.unique hB1 hB2).1.symm
  have hQ1' : (tr.states i.succ).board.grid B1 = some Q1 := by
    change (tr.after i).board.grid B1 = some Q1
    rw [tr.boardMove_grid_other ht i src dst promote B1 hmv hB1s hB1d]
    exact hQ1
  have hgl1' : tr.GlaresAtEnemyKing kp i.succ B1 :=
    (tr.glaresAtEnemyKing_congr kp ht (hQ1'.trans hQ1.symm) ((hkp _).trans (hkp _).symm)).mpr
      hgl1
  -- These are all the bishops and horses right after the move.
  have hsub : ({B1, B2} : Finset Pos) ⊆ tr.bishopHorseSquares i.succ := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact tr.mem_bishopHorseSquares_of _ _ Q1 hQ1' hQ1t
    · exact tr.mem_bishopHorseSquares_of _ _ Q2 hQ2 hQ2t
  have hallBH : tr.bishopHorseSquares i.succ = {B1, B2} := by
    refine (Finset.eq_of_subset_of_card_le hsub ?_).symm
    rw [Finset.card_pair h12]
    exact (hcount i.succ).1
  -- So the opponent has no non-glaring bishop or horse then, nor in any state.
  let Pbh : Piece → Prop := fun x => x.owner = o.opponent ∧
    (x.pieceType = .bishop ∨ x.pieceType = .horse)
  have hzero : tr.nonGlaringSquaresOf kp Pbh i.succ = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro q hq
    obtain ⟨⟨x, hx, hxP⟩, hngq⟩ := (tr.mem_nonGlaringSquaresOf kp Pbh _ _).mp hq
    have hmem := tr.mem_bishopHorseSquares_of _ _ x hx hxP.2
    rw [hallBH] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl
    · exact hngq hgl1'
    · exact hngq hgl2
  have hzero_all : ∀ k, tr.nonGlaringSquaresOf kp Pbh k = ∅ := by
    intro k
    rw [← Finset.card_eq_zero,
      tr.nonGlaringSquaresOf_card_eq_of_periodic kp ht hs hk hsafe h0 hc hr hp Pbh k,
      ← tr.nonGlaringSquaresOf_card_eq_of_periodic kp ht hs hk hsafe h0 hc hr hp Pbh i.succ,
      hzero, Finset.card_empty]
  -- The opponent's discovered check (Proposition 4.1) moves a rook or a dragon.
  obtain ⟨pt', hopen'⟩ := tr.exists_openableMove kp hm' h41 o.opponent
  have hbh : ¬ (pt' = .bishop ∨ pt' = .horse) := by
    intro hb
    obtain ⟨j, s', _, _, _, _, hsj, hngj, _⟩ := hopen'
    have hmem : s' ∈ tr.nonGlaringSquaresOf kp Pbh j.castSucc :=
      (tr.mem_nonGlaringSquaresOf kp Pbh _ _).mpr ⟨⟨_, hsj, rfl, hb⟩, hngj⟩
    rw [hzero_all] at hmem
    exact absurd hmem (Finset.notMem_empty _)
  have hpt' : pt' = .rook ∨ pt' = .dragon := by
    cases pt' <;> first
      | exact Or.inl rfl
      | exact Or.inr rfl
      | exact absurd hopen' (tr.not_openableMove_king kp hm' _)
      | exact absurd hopen' (tr.not_openableMove_forward_of_periodic kp hm' _ _ (by decide))
      | exact absurd hopen' (tr.not_openableMove_goldType_of_periodic kp hm' _ _ rfl)
      | exact absurd hopen' (tr.not_openableMove_silver_of_periodic kp hm' hcount _)
      | exact absurd (by decide) hbh
  -- An openable rook or dragon of the opponent stands right after `o`'s move.
  obtain ⟨j, s', _, _, _, hmj, hsj, hngj, _⟩ := hopen'
  let Prd : Piece → Prop := fun x => x.owner = o.opponent ∧
    (x.pieceType = .rook ∨ x.pieceType = .dragon)
  have hmem' : s' ∈ tr.openableSquaresOf kp Prd j.castSucc := by
    refine (tr.mem_openableSquaresOf kp Prd _ _).mpr ⟨⟨_, hsj, rfl, hpt'⟩, ?_, hngj,
      fun himm => himm.2 j (by rw [hmj]; exact Or.inl rfl)⟩
    change (tr.before j).board.grid s' ≠ none
    rw [hsj]
    exact Option.some_ne_none _
  have hpos : 0 < (tr.openableSquaresOf kp Prd i.succ).card := by
    rw [tr.openableSquaresOf_card_eq_of_periodic kp ht hs hk hsafe h0 hc hr hp Prd i.succ,
      ← tr.openableSquaresOf_card_eq_of_periodic kp ht hs hk hsafe h0 hc hr hp Prd j.castSucc]
    exact Finset.card_pos.mpr ⟨s', hmem'⟩
  obtain ⟨q3, hq3⟩ := Finset.card_pos.mp hpos
  obtain ⟨⟨x3, hx3, hx3o, hx3t⟩, hq3open⟩ := (tr.mem_openableSquaresOf kp Prd _ _).mp hq3
  obtain ⟨B3, Q3, _, _, _, hQ3, hQ3o, hQ3t, _, _, _, _⟩ :=
    tr.bishopHorse_behind_openable_rookDragon_of_periodic kp ht hs hk hsafe h0 hc hr hp
      i.succ q3 hq3open x3 hx3 hx3t
  -- Three bishop/horse squares: two of `o` and one of the opponent.
  have hown : ∀ {B : Pos} {Q : Piece}, (tr.states i.succ).board.grid B = some Q → Q.owner = o →
      B ≠ B3 := by
    rintro B Q hQ hQo rfl
    rw [hQ3] at hQ
    cases hQ
    rw [hQ3o, hx3o] at hQo
    cases o <;> cases hQo
  exact tr.false_of_three_bishopHorse hcount i.succ B1 B2 B3 h12 (hown hQ1' hQ1o)
    (hown hQ2 hQ2o) (tr.mem_bishopHorseSquares_of _ _ Q1 hQ1' hQ1t)
    (tr.mem_bishopHorseSquares_of _ _ Q2 hQ2 hQ2t) (tr.mem_bishopHorseSquares_of _ _ Q3 hQ3 hQ3t)

end MoveTrace
end MPC
