///|
/// evolve2.mbt — 衍生演生法 II：由計算實驗演化出自守物件
///   A4 (模性 GA): 演化 q-展開係數使其滿足 Hecke 關係＋曲線計數
///       — 收斂點 = 真正的新形式係數（模性定理的演化發現）
///   A5 (Frobenius 矩陣演化): 演化 GL₂(Z/ℓ) 元素逼近
///       tr ≡ a_p (mod ℓ)、det ≡ p (mod ℓ) — 收斂 = Galois 表示生成元
///   A6 (局整相容演化): 由整體 L 資料 {a_{p^m}} 冪和演化 GL₃ Sym² 局部參數
///       — 殘差收斂到 0 ⇒ 局部-整體相容（Satake 由整體資料復原）

///|
/// xorshift64 as a pure function: (state, output).
pub fn lcg2_next(state : Int64) -> (Int64, Int64) {
  let mut x = state
  x = x ^ (x >> 12)
  x = x ^ (x << 25)
  x = x ^ (x >> 27)
  (x, x * 2685821657736338717L)
}

///|
/// Random int in [0, bound).
pub fn lcg2_below(state : Int64, bound : Int32) -> (Int64, Int32) {
  let (s2, v) = lcg2_next(state)
  let mut r = (v % bound.to_int64()).to_int()
  if r < 0 {
    r = r + bound
  }
  (s2, r)
}

///|
/// A4 SMOOTH fitness: Σ |slack| over Hecke relations a_m a_n − Σ d·a_{mn/d²}
/// (+ 2·Σ|a_p − truth_p| over primes when use_curve). Zero iff perfect.
pub fn a4_fitness(
  cand : Array[Int64],
  e : WCurve,
  n_max : Int32,
  use_curve : Bool,
) -> Int32 {
  let mut bad = 0
  let mut m = 1
  while m <= n_max {
    let mut n = 1
    while n <= n_max {
      if m * n <= n_max {
        let lhs = cand[m] * cand[n]
        let mut rhs = 0L
        let mut d = 1
        while d <= m {
          if m % d == 0 && n % d == 0 {
            rhs = rhs + d.to_int64() * cand[m * n / (d * d)]
          }
          d = d + 1
        }
        let slack = lhs - rhs
        bad = bad + (if slack < 0L { -slack } else { slack }).to_int()
      }
      n = n + 1
    }
    m = m + 1
  }
  if use_curve {
    for p in primes_upto(n_max) {
      let truth = (p + 1 - e.count_points(p, 1)).to_int64()
      let diff = cand[p] - truth
      bad = bad + 2 * (if diff < 0L { -diff } else { diff }).to_int()
    }
  }
  bad
}

///|
/// Hecke repair operator: project a candidate onto the Hecke-eigenvalue
/// manifold. Given the prime genes a_p, derive composites by
/// a_{p^j} = a_p·a_{p^{j−1}} − p·a_{p^{j−2}} (weight 2; at p = 11 | N:
/// a_{11^j} = a_{11}^j) and a_{mn} = a_m·a_n for coprime m, n.
pub fn hecke_repair(cand : Array[Int64], n_max : Int32) -> Unit {
  // prime powers
  for p in primes_upto(n_max) {
    let mut pj = p * p
    while pj <= n_max {
      if p == 11 {
        cand[pj] = cand[pj / p] * cand[p]
      } else {
        cand[pj] = cand[p] * cand[pj / p] - p.to_int64() * cand[pj / (p * p)]
      }
      pj = pj * p
    }
  }
  // coprime composites
  let mut n = 2
  while n <= n_max {
    let mut u = 2
    while u * u <= n {
      if n % u == 0 {
        let v = n / u
        if gcd_int(u, v) == 1 {
          cand[n] = cand[u] * cand[v]
          u = n
        }
      }
      u = u + 1
    }
    n = n + 1
  }
}

///|
/// Run A4 GA: evolve coefficients of the X₀(11) newform.
/// Returns (best fitness, best candidate, generations used).
pub fn evolve_modularity(
  n_max : Int32,
  gens : Int32,
) -> (Int32, Array[Int64], Int32) {
  let e = x011_curve()
  let mut rng = 20261124L
  let pop_size = 60
  let pop : Array[Array[Int64]] = []
  let mut i = 0
  while i < pop_size {
    let cand : Array[Int64] = []
    cand.push(0L)
    cand.push(1L)
    let mut n = 2
    while n <= n_max {
      let (s2, v) = lcg2_below(rng, 5)
      rng = s2
      cand.push((v - 2).to_int64())
      n = n + 1
    }
    hecke_repair(cand, n_max)
    pop.push(cand)
    i = i + 1
  }
  let mut g = 0
  while g < gens {
    let fits : Array[Int32] = []
    let mut j = 0
    while j < pop_size {
      let f = a4_fitness(pop[j], e, n_max, g > gens / 3)
      fits.push(f)
      j = j + 1
    }
    let next : Array[Array[Int64]] = []
    let mut bi = 0
    let mut k = 0
    while k < pop_size {
      if fits[k] < fits[bi] {
        bi = k
      }
      k = k + 1
    }
    next.push(pop[bi])
    while next.length() < pop_size {
      let (s2, t1) = lcg2_below(rng, pop_size)
      let (s3, t2) = lcg2_below(s2, pop_size)
      rng = s3
      let pa = if fits[t1] < fits[t2] { pop[t1] } else { pop[t2] }
      let (s4, u1) = lcg2_below(rng, pop_size)
      let (s5, u2) = lcg2_below(s4, pop_size)
      rng = s5
      let pb = if fits[u1] < fits[u2] { pop[u1] } else { pop[u2] }
      let child : Array[Int64] = []
      child.push(0L)
      child.push(1L)
      let mut n = 2
      while n <= n_max {
        let (s6, pick) = lcg2_below(rng, 2)
        rng = s6
        let mut v = if pick == 0 { pa[n] } else { pb[n] }
        let (s7, mutp) = lcg2_below(rng, 3)
        let (s8, delta) = lcg2_below(s7, 3)
        rng = s8
        if mutp == 0 {
          v = v + (delta - 1).to_int64()
        }
        child.push(v)
        n = n + 1
      }
      hecke_repair(child, n_max)
      next.push(child)
    }
    let mut r = 0
    while r < pop_size {
      pop[r] = next[r]
      r = r + 1
    }
    g = g + 1
  }
  // final re-score with FULL criteria (curve + Hecke) — the staged search may
  // have locked in a Hecke-consistent but wrong-prime solution in phase 1
  let mut fb = 999999
  let mut bb = pop[0]
  let mut q = 0
  while q < pop_size {
    let f = a4_fitness(pop[q], e, n_max, true)
    if f < fb {
      fb = f
      bb = pop[q]
    }
    q = q + 1
  }
  (fb, bb, gens)
}

///|
/// A5 fitness: count of unmet constraints on (tr, det) mod ℓ.
pub fn a5_fitness(m : Mat2, a_p : Int32, p : Int32, ell : Int32) -> Int32 {
  let mut bad = 0
  if m.trace_mod(ell) != (a_p % ell + ell) % ell {
    bad = bad + 1
  }
  if m.det_mod(ell) != (p % ell + ell) % ell {
    bad = bad + 1
  }
  bad
}

///|
/// Run A5 GA. Returns (best fitness, best matrix, gens).
pub fn evolve_frobenius_matrix(
  a_p : Int32,
  p : Int32,
  ell : Int32,
  gens : Int32,
) -> (Int32, Mat2, Int32) {
  let mut rng = 424242L
  let pop_size = 20
  let pop : Array[Mat2] = []
  let mut i = 0
  while i < pop_size {
    let (s1, a) = lcg2_below(rng, ell)
    let (s2, b) = lcg2_below(s1, ell)
    let (s3, c) = lcg2_below(s2, ell)
    let (s4, d) = lcg2_below(s3, ell)
    rng = s4
    pop.push(Mat2(a, b, c, d))
    i = i + 1
  }
  let mut best_fit = 999
  let mut best = pop[0]
  let mut g = 0
  while g < gens {
    let fits : Array[Int32] = []
    let mut j = 0
    while j < pop_size {
      let f = a5_fitness(pop[j], a_p, p, ell)
      fits.push(f)
      if f < best_fit {
        best_fit = f
        best = pop[j]
      }
      j = j + 1
    }
    if best_fit == 0 {
      return (0, best, g)
    }
    let next : Array[Mat2] = []
    let mut bi = 0
    let mut k = 0
    while k < pop_size {
      if fits[k] < fits[bi] {
        bi = k
      }
      k = k + 1
    }
    next.push(pop[bi])
    while next.length() < pop_size {
      let (s1, t1) = lcg2_below(rng, pop_size)
      let (s2, t2) = lcg2_below(s1, pop_size)
      rng = s2
      let pa = if fits[t1] < fits[t2] { pop[t1] } else { pop[t2] }
      let (s3, u1) = lcg2_below(rng, pop_size)
      let (s4, u2) = lcg2_below(s3, pop_size)
      rng = s4
      let pb = if fits[u1] < fits[u2] { pop[u1] } else { pop[u2] }
      let (s5, p0) = lcg2_below(rng, 2)
      let (s6, p1) = lcg2_below(s5, 2)
      let (s7, p2) = lcg2_below(s6, 2)
      let (s8, p3) = lcg2_below(s7, 2)
      let (s9, idx) = lcg2_below(s8, 4)
      let (s10, add) = lcg2_below(s9, ell)
      rng = s10
      let entries : Array[Int32] = []
      entries.push(if p0 == 0 { pa.0 } else { pb.0 })
      entries.push(if p1 == 0 { pa.1 } else { pb.1 })
      entries.push(if p2 == 0 { pa.2 } else { pb.2 })
      entries.push(if p3 == 0 { pa.3 } else { pb.3 })
      entries[idx] = (entries[idx] + add) % ell
      next.push(Mat2(entries[0], entries[1], entries[2], entries[3]))
    }
    let mut r = 0
    while r < pop_size {
      pop[r] = next[r]
      r = r + 1
    }
    g = g + 1
  }
  (best_fit, best, gens)
}

///|
/// Clamp to keep Newton-identity intermediates within Int64 range.
pub fn clamp64(x : Int64, lo : Int64, hi : Int64) -> Int64 {
  if x < lo {
    lo
  } else if x > hi {
    hi
  } else {
    x
  }
}

///|
/// One-dimensional evolutionary search: evolve x toward |a·x − target| = 0
/// with tournament + elitism + heavy-tailed mutation. Returns (best_x, err).
pub fn evolve_linear(
  a_coeff : Int64,
  target : Int64,
  lo : Int64,
  hi : Int64,
  gens : Int32,
  seed : Int64,
) -> (Int64, Int64) {
  let mut rng = seed
  let pop_size = 50
  let pop : Array[Int64] = []
  let mut i = 0
  while i < pop_size {
    let (s1, a) = lcg2_below(rng, 20000)
    rng = s1
    let span = ((hi - lo) / 20000L).to_int()
    pop.push(lo + a.to_int64() * span.to_int64())
    i = i + 1
  }
  let mut best_x = pop[0]
  let mut best_err = 4611686018427387907L
  let mut g = 0
  while g < gens {
    let fits : Array[Int64] = []
    let mut j = 0
    while j < pop_size {
      let d = a_coeff * pop[j] - target
      let e = if d < 0L { -d } else { d }
      fits.push(e)
      if e < best_err {
        best_err = e
        best_x = pop[j]
      }
      j = j + 1
    }
    if best_err == 0L {
      return (best_x, 0L)
    }
    let next : Array[Int64] = []
    let mut bi = 0
    let mut k = 0
    while k < pop_size {
      if fits[k] < fits[bi] {
        bi = k
      }
      k = k + 1
    }
    next.push(pop[bi])
    while next.length() < pop_size {
      let (s1, t1) = lcg2_below(rng, pop_size)
      let (s2, t2) = lcg2_below(s1, pop_size)
      rng = s2
      let pa = if fits[t1] < fits[t2] { pop[t1] } else { pop[t2] }
      let (s3, u1) = lcg2_below(rng, pop_size)
      let (s4, u2) = lcg2_below(s3, pop_size)
      rng = s4
      let pb = if fits[u1] < fits[u2] { pop[u1] } else { pop[u2] }
      let (s5, pick) = lcg2_below(rng, 2)
      rng = s5
      let mut c = if pick == 0 { pa } else { pb }
      let (s6, m0) = lcg2_below(rng, 2)
      let (s7, kk) = lcg2_below(s6, 13)
      let (s8, dd) = lcg2_below(s7, 20)
      rng = s8
      if m0 == 0 {
        c = c + (dd - 10).to_int64() * pow64(10L, kk)
        c = clamp64(c, lo, hi)
      }
      next.push(c)
    }
    let mut r = 0
    while r < pop_size {
      pop[r] = next[r]
      r = r + 1
    }
    g = g + 1
  }
  (best_x, best_err)
}

///|
/// Run A6 as a genuine STAGED evolutionary algorithm following the triangular
/// Newton structure of the Sym² Satake data:
///   stage 1: evolve e1 (t1 = e1);
///   stage 2: evolve e2 (t2 = e1² − 2e2);
///   stage 3: evolve e3 (t3 = e1t2 − e2t1 + 3e3).
/// Returns (best fitness, e1, e2, e3, gens).
pub fn evolve_sym2_data(
  targets : Array[Int64],
  gens : Int32,
) -> (Int64, Int64, Int64, Int64, Int32) {
  let g3 = gens / 3
  // stage 1: t1 = 1·e1 = targets[0]
  let (e1, err1) = evolve_linear(
    1L,
    targets[0],
    -1000000L,
    1000000L,
    g3,
    1122334455L,
  )
  if err1 != 0L {
    return (err1, e1, 0L, 0L, gens)
  }
  // stage 2: t2 = e1² − 2e2 = targets[1] ⇒ 2·e2 = e1² − targets[1]
  let (e2, err2) = evolve_linear(
    -2L,
    targets[1] - e1 * e1,
    -100000000L,
    100000000L,
    g3,
    2233445566L,
  )
  if err2 != 0L {
    return (err2, e1, e2, 0L, gens)
  }
  // stage 3: t3 = e1·t2 − e2·t1 + 3·e3 = targets[2]
  let t1 = e1
  let t2 = e1 * e1 - 2 * e2
  let const3 = e1 * t2 - e2 * t1
  let (e3, err3) = evolve_linear(
    3L,
    targets[2] - const3,
    -1000000000000L,
    1000000000000L,
    gens,
    3344556677L,
  )
  let total = if err3 == 0L { 0L } else { err3 }
  (total, e1, e2, e3, gens)
}
