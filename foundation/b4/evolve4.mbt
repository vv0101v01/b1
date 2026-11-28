///|
/// evolve4.mbt — 批次四 衍生演生法 A10–A12
///
/// A10 (模性提升演化): evolve the characteristic-0 lift (x₂, x₃) of the
///     mod-5 system from CONSTRAINTS ONLY — congruence ā_p (mod 5), Hasse
///     bounds, and Galois-side data a₄ = x₂² − 4、a₆ = x₂·x₃ (from point
///     counts). The feasible set collapses to the modular lift.
/// A11 (純性演化): evolve local factor data (e₁, e₂) = (α+β, αβ) under
///     PURITY: e₂ = p and |e₁| ≤ 2√p (Weil numbers) + trace target.
/// A12 (動機投射子演化): evolve a 2×2 integer projector E with E² = E and
///     EᵀJE = 0 (Lagrangian isotropic projector for the symplectic form) —
///     the Künneth/h^{1,0} projector emerges.

///|
/// A10 fitness for (x₂, x₃): constraints only.
pub fn a10_fitness(
  x2 : Int32,
  x3 : Int32,
  abar2 : Int32,
  abar3 : Int32,
  a4_gal : Int64,
  a6_gal : Int64,
) -> Int32 {
  let mut pen = 0
  // congruence mod 5
  if (x2 % 5 + 5) % 5 != (abar2 % 5 + 5) % 5 {
    pen = pen + 10
  }
  if (x3 % 5 + 5) % 5 != (abar3 % 5 + 5) % 5 {
    pen = pen + 10
  }
  // Hasse bounds
  let h2 = 2.0 * 2.0.sqrt()
  let h3 = 2.0 * 3.0.sqrt()
  if x2.to_double().abs() > h2 + 0.0001 {
    pen = pen + (10 + (x2.to_double().abs() - h2).round().to_int())
  }
  if x3.to_double().abs() > h3 + 0.0001 {
    pen = pen + (10 + (x3.to_double().abs() - h3).round().to_int())
  }
  // Galois data: a₄ = x₂² − 2·2 = x₂² − 4; a₆ = x₂·x₃ (coprime mult)
  let e4 = (x2 * x2 - 4).to_int64() - a4_gal
  pen = pen + (if e4 < 0L { -e4 } else { e4 }).to_int()
  let e6 = x2.to_int64() * x3.to_int64() - a6_gal
  pen = pen + (if e6 < 0L { -e6 } else { e6 }).to_int()
  pen
}

///|
/// A10 GA over (x₂, x₃) ∈ [−12, 12]².
pub fn evolve_modular_lift(
  abar2 : Int32,
  abar3 : Int32,
  a4_gal : Int64,
  a6_gal : Int64,
  gens : Int32,
  seed : Int64,
) -> (Int32, Int32, Int32) {
  let mut rng = seed
  let pop_size = 50
  let pop : Array[(Int32, Int32)] = []
  let mut i = 0
  while i < pop_size {
    let (r1, g1) = lcg2_below(rng, 25)
    rng = r1
    let (r2, g2) = lcg2_below(rng, 25)
    rng = r2
    pop.push((g1 - 12, g2 - 12))
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
      let f = a10_fitness(x, y, abar2, abar3, a4_gal, a6_gal)
      fits.push(f)
      if f < best_fit {
        best_fit = f
        best = (x, y)
      }
      j = j + 1
    }
    let next : Array[(Int32, Int32)] = []
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
      let (r9, mm) = lcg2_below(rng, 6)
      rng = r9
      let mut d1 = 0
      let mut d2 = 0
      if mm == 0 {
        let (r10, dm) = lcg2_below(rng, 5)
        rng = r10
        d1 = dm - 2
      }
      if mm == 1 {
        let (r11, dm2) = lcg2_below(rng, 5)
        rng = r11
        d2 = dm2 - 2
      }
      let mut nx = c1 + d1
      let mut ny = c2 + d2
      if nx < -12 {
        nx = -12
      }
      if nx > 12 {
        nx = 12
      }
      if ny < -12 {
        ny = -12
      }
      if ny > 12 {
        ny = 12
      }
      next.push((nx, ny))
    }
    let mut r = 0
    while r < pop_size {
      pop[r] = next[r]
      r = r + 1
    }
    g = g + 1
  }
  let (bx, by) = best
  (bx, by, best_fit)
}

///|
/// A11 fitness: purity constraints on (e₁, e₂) at prime p with target trace.
pub fn a11_fitness(e1 : Int64, e2 : Int64, p : Int32, target : Int64) -> Int64 {
  let pm = p.to_int64()
  let mut pen = 0L
  // e₂ = p (Weil: αβ = p)
  let d2 = e2 - pm
  pen = pen + (if d2 < 0L { -d2 } else { d2 })
  // |e₁| ≤ 2√p: penalty for violation
  let bound = 2.0 * p.to_double().sqrt()
  if e1.to_double().abs() > bound + 0.0001 {
    pen = pen + 5L
  }
  // trace target (automorphic source)
  let d1 = e1 - target
  pen = pen + (if d1 < 0L { -d1 } else { d1 })
  // purity discriminant: e₁² − 4p ≤ 0 (complex pair) — violated ones get
  // extra penalty only if e₂ = p already (roots product p with |α|≠|β|)
  let disc = e1.to_double() * e1.to_double() - 4.0 * p.to_double()
  if disc > 0.0 {
    pen = pen + 3L
  }
  pen
}

///|
/// A11 GA over (e₁, e₂) ∈ [−4p−8, 4p+8]².
pub fn evolve_purity(
  p : Int32,
  target : Int64,
  gens : Int32,
  seed : Int64,
) -> (Int64, Int64, Int64) {
  let mut rng = seed
  let pop_size = 50
  let span = 4L * p.to_int64() + 8L
  let pop : Array[(Int64, Int64)] = []
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
      let f = a11_fitness(x, y, p, target)
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
    let mut r = 0
    while r < pop_size {
      pop[r] = next[r]
      r = r + 1
    }
    g = g + 1
  }
  let (bx, by) = best
  (bx, by, best_fit)
}

///|
/// A12 fitness: 2×2 integer matrix E = ((a, b), (c, d)): projector E² = E +
/// Lagrangian isotropy EᵀJE = 0 with J = [[0,1],[−1,0]].
pub fn a12_fitness(a : Int32, b : Int32, c : Int32, d : Int32) -> Int32 {
  // E² = E: entries: a²+bc = a; ab+bd = b; ac+cd = c; bc+d² = d
  let e00 = a * a + b * c - a
  let e01 = a * b + b * d - b
  let e10 = a * c + c * d - c
  let e11 = b * c + d * d - d
  let pen1 = abs_i(e00) + abs_i(e01) + abs_i(e10) + abs_i(e11)
  // EᵀJE = 0: EᵀJE = [[a, c], [b, d]]·[[0,1],[−1,0]]·[[a,b],[c,d]]:
  // [[0,1],[−1,0]]·E = [[c, d], [−a, −b]]; Eᵀ·(that) = [[a,b+c·0...
  // compute M = J·E = [[c, d], [−a, −b]]; Eᵀ·M = [[a, c],[b, d]]·[[c, d],[−a, −b]]
  // = [[ac − ca, ad − cb], [bc − da, bd − db]] = [[0, ad − bc], [bc − ad, 0]]
  // so EᵀJE = [[0, det E], [−det E, 0]]... wait sign: Eᵀ·J·E with J skew:
  // = det(E)·J-ish: condition EᵀJE = 0 ⟺ det E = 0.
  let det = a * d - b * c
  pen1 + abs_i(det) * 2
}

///|
fn abs_i(x : Int32) -> Int32 {
  if x < 0 {
    -x
  } else {
    x
  }
}

///|
/// A12 GA over entries in [−6, 6].
pub fn evolve_projector(
  gens : Int32,
  seed : Int64,
) -> (Int32, Int32, Int32, Int32, Int32) {
  let mut rng = seed
  let pop_size = 60
  let pop : Array[(Int32, Int32, Int32, Int32)] = []
  let mut i = 0
  while i < pop_size {
    let (r1, g1) = lcg2_below(rng, 13)
    rng = r1
    let (r2, g2) = lcg2_below(rng, 13)
    rng = r2
    let (r3, g3) = lcg2_below(rng, 13)
    rng = r3
    let (r4, g4) = lcg2_below(rng, 13)
    rng = r4
    pop.push((g1 - 6, g2 - 6, g3 - 6, g4 - 6))
    i = i + 1
  }
  let mut best = pop[0]
  let mut best_fit = 1000000
  let mut g = 0
  while g < gens {
    let fits : Array[Int32] = []
    let mut j = 0
    while j < pop_size {
      let (x, y, z, w) = pop[j]
      let f = a12_fitness(x, y, z, w)
      fits.push(f)
      if f < best_fit {
        best_fit = f
        best = (x, y, z, w)
      }
      j = j + 1
    }
    let next : Array[(Int32, Int32, Int32, Int32)] = []
    next.push(best)
    while next.length() < pop_size {
      let (r5, t1) = lcg2_below(rng, pop_size)
      rng = r5
      let (r6, t2) = lcg2_below(rng, pop_size)
      rng = r6
      let p1 = if fits[t1] <= fits[t2] { pop[t1] } else { pop[t2] }
      let (r7, t3) = lcg2_below(rng, pop_size)
      rng = r7
      let (r8, t4) = lcg2_below(rng, pop_size)
      rng = r8
      let p2 = if fits[t3] <= fits[t4] { pop[t3] } else { pop[t4] }
      // gene-wise crossover
      let (r9, k1) = lcg2_below(rng, 2)
      rng = r9
      let (r10, k2) = lcg2_below(rng, 2)
      rng = r10
      let (r11, k3) = lcg2_below(rng, 2)
      rng = r11
      let (r12, k4) = lcg2_below(rng, 2)
      rng = r12
      let c1 = if k1 == 0 { p1.0 } else { p2.0 }
      let c2 = if k2 == 0 { p1.1 } else { p2.1 }
      let c3 = if k3 == 0 { p1.2 } else { p2.2 }
      let c4 = if k4 == 0 { p1.3 } else { p2.3 }
      // creep mutation
      let (r13, mm) = lcg2_below(rng, 8)
      rng = r13
      let mut dd = 0
      if mm < 4 {
        let (r14, dm) = lcg2_below(rng, 5)
        rng = r14
        dd = dm - 2
      }
      let mut nx = c1
      let mut ny = c2
      let mut nz = c3
      let mut nw = c4
      if mm == 0 {
        nx = clamp_i(nx + dd)
      } else if mm == 1 {
        ny = clamp_i(ny + dd)
      } else if mm == 2 {
        nz = clamp_i(nz + dd)
      } else if mm == 3 {
        nw = clamp_i(nw + dd)
      }
      next.push((nx, ny, nz, nw))
    }
    let mut r = 0
    while r < pop_size {
      pop[r] = next[r]
      r = r + 1
    }
    g = g + 1
  }
  let (bx, by, bz, bw) = best
  (bx, by, bz, bw, best_fit)
}

///|
fn clamp_i(x : Int32) -> Int32 {
  if x < -6 {
    -6
  } else if x > 6 {
    6
  } else {
    x
  }
}
