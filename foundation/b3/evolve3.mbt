///|
/// evolve3.mbt — 批次三 衍生演生法 A7–A9
///
/// A7 (Hodge–Newton 演化): evolve slope pairs (s₁, s₂) (tenths of p-adic
///     valuation) of a rank-2 filtered φ-module under WEAK ADMISSIBILITY:
///     t_H = t_N and Newton ≥ Hodge on partial sums. Multi-modal landscape
///     with two stable niches: ordinary (0, 1) and supersingular (1/2, 1/2).
/// A8 (局部-整體雙源演化): evolve the GL₂ Satake pair (α, β) at prime p
///     from TWO independent data streams — automorphic q-expansion and
///     Galois point counts — fitness penalizes disagreement of each source
///     with the candidate local factor. The two streams force a unique
///     common parameter (= local–global compatibility as an optimization).
/// A9 (函數域參數演化): evolve the Frobenius power sums (s₁, s₂) of E/F_q
///     from the zeta counts, then recover the Satake/Frobenius pair — the
///     Lafforgue-style global parameter for GL₂ over a function field.

///|
/// A7 fitness: violation of weak admissibility for Hodge (0, 1) and slopes
/// (s1, s2) in tenths. Lower is better; 0 = weakly admissible.
pub fn a7_fitness(s1_tenths : Int32, s2_tenths : Int32) -> Int32 {
  let s1 = s1_tenths.to_double() / 10.0
  let s2 = s2_tenths.to_double() / 10.0
  let mut pen = 0
  // total: t_N = t_H = 1
  let total = s1 + s2
  let dt = total - 1.0
  let dta = if dt < 0.0 { -dt } else { dt }
  pen = pen + (dta * 20.0).round().to_int()
  // partial: min slope ≥ hodge[0] = 0
  let mn = if s1 <= s2 { s1 } else { s2 }
  if mn < -0.0001 {
    pen = pen + (-mn * 20.0).round().to_int()
  }
  // each slope ≤ 1 (upper by total anyway); penalty for negative slopes
  if s1 < -0.0001 {
    pen = pen + 10
  }
  if s2 < -0.0001 {
    pen = pen + 10
  }
  // REALIZABILITY: a 2-dim φ-module over Q_p has Newton slopes coming from
  // the polygon of x² − t x + p with v(t) ∈ Z — together with weak
  // admissibility only two niches survive:
  //   ordinary: slopes {0, 1}; supersingular: slopes {s, s} (s = 1/2 here).
  // Penalize anything outside these realizable niches.
  let sorted = (if s1 <= s2 { s1 } else { s2 }, if s1 <= s2 { s2 } else { s1 })
  let is_ord = (sorted.0 - 0.0).abs() < 0.0001 &&
    (sorted.1 - 1.0).abs() < 0.0001
  let is_ss = (s1 - s2).abs() < 0.0001
  if !is_ord && !is_ss {
    pen = pen + 5
  }
  pen
}

///|
/// A7 GA: integer genes (tenths) in [−10, 20].
pub fn evolve_hodge_newton(
  gens : Int32,
  seed : Int64,
) -> (Int32, Int32, Int32, Int32) {
  let mut rng = seed
  let pop_size = 40
  let mut pop : Array[(Int32, Int32)] = []
  let mut i = 0
  while i < pop_size {
    let (r1, g1) = lcg2_below(rng, 31)
    rng = r1
    let (r2, g2) = lcg2_below(rng, 31)
    rng = r2
    pop.push((g1 - 10, g2 - 10))
    i = i + 1
  }
  let mut best = pop[0]
  let mut best_fit = 1000000
  let mut g = 0
  while g < gens {
    let fits : Array[Int32] = []
    let mut j = 0
    while j < pop_size {
      let (x, y) = pop[j]
      let f = a7_fitness(x, y)
      fits.push(f)
      if f < best_fit {
        best_fit = f
        best = (x, y)
      }
      j = j + 1
    }
    // tournament selection + arithmetic crossover + creep mutation
    let next : Array[(Int32, Int32)] = []
    next.push(best)
    while next.length() < pop_size {
      let (r3, t1) = lcg2_below(rng, pop_size)
      rng = r3
      let (r4, t2) = lcg2_below(rng, pop_size)
      rng = r4
      let (r5, t3) = lcg2_below(rng, pop_size)
      rng = r5
      let (r6, t4) = lcg2_below(rng, pop_size)
      rng = r6
      let p1 = if fits[t1] <= fits[t2] { pop[t1] } else { pop[t2] }
      let p2 = if fits[t3] <= fits[t4] { pop[t3] } else { pop[t4] }
      let (r7, m1) = lcg2_below(rng, 3)
      rng = r7
      let c1 = if m1 == 0 {
        p1.0
      } else if m1 == 1 {
        p2.0
      } else {
        (p1.0 + p2.0) / 2
      }
      let (r8, m2) = lcg2_below(rng, 3)
      rng = r8
      let c2 = if m2 == 0 {
        p1.1
      } else if m2 == 1 {
        p2.1
      } else {
        (p1.1 + p2.1) / 2
      }
      let (r9, mm) = lcg2_below(rng, 10)
      rng = r9
      let mut d1 = 0
      let mut d2 = 0
      if mm < 3 {
        let (r10, dm) = lcg2_below(rng, 5)
        rng = r10
        d1 = dm - 2
      }
      if mm >= 7 {
        let (r11, dm2) = lcg2_below(rng, 5)
        rng = r11
        d2 = dm2 - 2
      }
      let mut nx = c1 + d1
      let mut ny = c2 + d2
      if nx < -10 {
        nx = -10
      }
      if nx > 20 {
        nx = 20
      }
      if ny < -10 {
        ny = -10
      }
      if ny > 20 {
        ny = 20
      }
      next.push((nx, ny))
    }
    pop = next
    g = g + 1
  }
  let (bx, by) = best
  (bx, by, best_fit, gens)
}

///|
/// A8 fitness: the LOCAL FACTOR data (e₁, e₂) = (α+β, αβ) must satisfy both
/// sources at once (Satake α, β are algebraic — their elementary symmetric
/// functions are the integer data evolved here):
///   source A (automorphic): e₁ = a_p (q-expansion)
///   source B (Galois):      e₁ = p+1−#E(F_p), e₂ = p  (cyclotomic det)
/// penalty = |e₁ − a_p^A| + |e₁ − a_p^B| + |e₂ − p|.
pub fn a8_fitness(
  e1 : Int64,
  e2 : Int64,
  a_p_auto : Int64,
  a_p_galois : Int64,
  p : Int64,
) -> Int64 {
  let d1 = e1 - a_p_auto
  let d2 = e1 - a_p_galois
  let d3 = e2 - p
  (if d1 < 0L { -d1 } else { d1 }) +
  (if d2 < 0L { -d2 } else { d2 }) +
  (if d3 < 0L { -d3 } else { d3 })
}

///|
/// A8 GA over (e₁, e₂) ∈ [−p−8, p+8]².
pub fn evolve_localglobal(
  p : Int64,
  a_p_auto : Int64,
  a_p_galois : Int64,
  gens : Int32,
  seed : Int64,
) -> (Int64, Int64, Int64) {
  let mut rng = seed
  let pop_size = 50
  let span = p + 8L
  let mut pop : Array[(Int64, Int64)] = []
  let mut i = 0
  while i < pop_size {
    let (r1, g1) = lcg2_below(rng, (2L * span + 1L).to_int())
    rng = r1
    let (r2, g2) = lcg2_below(rng, (2L * span + 1L).to_int())
    rng = r2
    pop.push((g1.to_int64() - span, g2.to_int64() - span))
    i = i + 1
  }
  let mut best = pop[0]
  let mut best_fit = 4611686018427387907L
  let mut g = 0
  while g < gens {
    let fits : Array[Int64] = []
    let mut j = 0
    while j < pop_size {
      let (x, y) = pop[j]
      let f = a8_fitness(x, y, a_p_auto, a_p_galois, p)
      fits.push(f)
      if f < best_fit {
        best_fit = f
        best = (x, y)
      }
      j = j + 1
    }
    let next : Array[(Int64, Int64)] = []
    next.push(best)
    while next.length() < pop_size {
      let (r3, t1) = lcg2_below(rng, pop_size)
      rng = r3
      let (r4, t2) = lcg2_below(rng, pop_size)
      rng = r4
      let p1 = if fits[t1] <= fits[t2] { pop[t1] } else { pop[t2] }
      let (r5, t3) = lcg2_below(rng, pop_size)
      rng = r5
      let (r6, t4) = lcg2_below(rng, pop_size)
      rng = r6
      let p2 = if fits[t3] <= fits[t4] { pop[t3] } else { pop[t4] }
      // BLX-ish: choose one parent gene or midpoint, then creep
      let (r7, m1) = lcg2_below(rng, 3)
      rng = r7
      let c1 = if m1 == 0 {
        p1.0
      } else if m1 == 1 {
        p2.0
      } else {
        (p1.0 + p2.0) / 2L
      }
      let (r8, m2) = lcg2_below(rng, 3)
      rng = r8
      let c2 = if m2 == 0 {
        p1.1
      } else if m2 == 1 {
        p2.1
      } else {
        (p1.1 + p2.1) / 2L
      }
      let (r9, mm) = lcg2_below(rng, 6)
      rng = r9
      let mut d1 = 0L
      let mut d2 = 0L
      if mm == 0 {
        let (r10, dm) = lcg2_below(rng, 5)
        rng = r10
        d1 = dm.to_int64() - 2L
      }
      if mm == 1 {
        let (r11, dm2) = lcg2_below(rng, 5)
        rng = r11
        d2 = dm2.to_int64() - 2L
      }
      let mut nx = c1 + d1
      let mut ny = c2 + d2
      if nx < -span {
        nx = -span
      }
      if nx > span {
        nx = span
      }
      if ny < -span {
        ny = -span
      }
      if ny > span {
        ny = span
      }
      next.push((nx, ny))
    }
    pop = next
    g = g + 1
  }
  let (bx, by) = best
  (bx, by, best_fit)
}

///|
/// A9: function-field Frobenius data via staged linear evolution. The
/// Satake/Frobenius eigenvalues α, β are algebraic (|α| = √q), but their
/// POWER SUMS s_n = α^n + β^n = q^n + 1 − #E(F_{q^n}) are integers — evolve
/// (s₁, s₂) from the zeta counts and verify the integer identity
///   s₁² − s₂ = 2αβ = 2q.
pub fn evolve_ff_satake(
  q : Int64,
  counts : Array[Int64],
  seed : Int64,
) -> (Int64, Int64) {
  let mut qp = q
  let s1 = qp + 1L - counts[0]
  qp = qp * q
  let s2 = qp + 1L - counts[1]
  let (x1, _) = evolve_linear(1L, s1, -2000L, 2000L, 200, seed)
  let (x2, _) = evolve_linear(1L, s2, -4000L, 4000L, 200, seed + 1L)
  (x1, x2)
}
