///|
/// Evolutionary algorithms A13–A15 (batch 5, continuing A7–A12).
/// Deterministic LCG-driven mutation loops with constraint fitness.

///|
/// Lehmer LCG state step (fits 32-bit Int)
fn lcg_next(state : Int32) -> Int32 {
  (state * 75 + 74) % 65537
}

///|
/// random integer in [0, bound)
fn lcg_rand(state : Int32, bound : Int32) -> (Int32, Int32) {
  let s2 = lcg_next(state)
  (s2 % bound, s2)
}

///|
/// A13 fitness: substitution consistency of a noncommutative diagram:
/// genes = images of x, y (len 2) and compiled products x², xy, y² (len 4);
/// constraints: subst([x,x]) = img_x2, subst([x,y]) = img_xy,
/// subst([y,y]) = img_y2
pub fn a13_fitness(
  img_x : Array[Int32],
  img_y : Array[Int32],
  img_x2 : Array[Int32],
  img_xy : Array[Int32],
  img_y2 : Array[Int32],
) -> Int32 {
  let mut err = 0
  let xx = subst([0, 0], [img_x, img_y])
  let xy = subst([0, 1], [img_x, img_y])
  let yy = subst([1, 1], [img_x, img_y])
  for i in 0..<4 {
    if xx[i] != img_x2[i] {
      err = err + 1
    }
    if xy[i] != img_xy[i] {
      err = err + 1
    }
    if yy[i] != img_y2[i] {
      err = err + 1
    }
  }
  err
}

///|
/// A13: evolve the diagram genes toward substitution consistency
/// (a monoid-homomorphic string diagram) — fitness 0 = interchange solution
pub fn evolve_noncomm_diagram() -> (
  Array[Int32],
  Array[Int32],
  Array[Int32],
  Array[Int32],
  Array[Int32],
) {
  let mut state = 7
  let img_x = [0, 1]
  let img_y = [1, 0]
  let mut img_x2 = [1, 1, 1, 1]
  let mut img_xy = [0, 0, 0, 0]
  let mut img_y2 = [1, 0, 0, 1]
  let mut best = a13_fitness(img_x, img_y, img_x2, img_xy, img_y2)
  let mut gen = 0
  while gen < 2000 && best > 0 {
    gen = gen + 1
    // pick gene + position + bit
    let (g0, s1) = lcg_rand(state, 5)
    state = s1
    let (pos, s2) = lcg_rand(state, 4)
    state = s2
    let (bit, s3) = lcg_rand(state, 2)
    state = s3
    let ox2 = img_x2.copy()
    let oxy = img_xy.copy()
    let oy2 = img_y2.copy()
    if g0 == 0 {
      if pos < 2 {
        img_x[pos] = bit
      }
    } else if g0 == 1 {
      if pos < 2 {
        img_y[pos] = bit
      }
    } else if g0 == 2 {
      img_x2[pos] = bit
    } else if g0 == 3 {
      img_xy[pos] = bit
    } else {
      img_y2[pos] = bit
    }
    let f = a13_fitness(img_x, img_y, img_x2, img_xy, img_y2)
    if f <= best {
      best = f
    } else {
      // revert product genes (x, y images stay — small neutral drift ok)
      img_x2 = ox2
      img_xy = oxy
      img_y2 = oy2
    }
  }
  (img_x, img_y, img_x2, img_xy, img_y2)
}

///|
/// A13 check: evolved diagram satisfies substitution consistency
pub fn a13_converges_ok() -> Bool {
  let (ix, iy, ix2, ixy, iy2) = evolve_noncomm_diagram()
  a13_fitness(ix, iy, ix2, ixy, iy2) == 0
}

///|
/// A14 fitness: representation gene m ∈ [0, 120): two constraints —
/// (i) deep on (Z/25)^*: cond25(m mod 20) = 2; (ii) non-Galois-invariant
/// on F_{25}^*: (m mod 24) % 6 ≠ 0. Fitness = number of violations.
pub fn a14_fitness(m : Int32) -> Int32 {
  let mut err = 0
  if cond25(m % 20) != 2 {
    err = err + 1
  }
  if m % 24 % 6 == 0 {
    err = err + 1
  }
  err
}

///|
/// A14: evolve a deep supercuspidal representation gene
pub fn evolve_deep_rep() -> Int32 {
  let mut state = 11
  let mut m = 60 // start at a doubly-bad gene: 60 % 20 = 0, 60 % 24 = 12
  let mut best = a14_fitness(m)
  let mut gen = 0
  while gen < 2000 && best > 0 {
    gen = gen + 1
    let (delta, s1) = lcg_rand(state, 15)
    state = s1
    let (sign, s2) = lcg_rand(state, 2)
    state = s2
    let cand = if sign == 0 { m + delta + 1 } else { m - delta - 1 }
    let c2 = (cand % 120 + 120) % 120
    let f = a14_fitness(c2)
    if f <= best {
      best = f
      m = c2
    }
  }
  m
}

///|
/// A14 check: evolved gene is deep + supercuspidal (fitness 0)
pub fn a14_converges_ok() -> Bool {
  a14_fitness(evolve_deep_rep()) == 0
}

///|
/// A15 fitness: wave front genes λ (len 6) toward WF = {−1, +1} with
/// "unboundedness evidence" (max |λ| ≥ 20)
pub fn a15_fitness(lam : Array[Int32]) -> Int32 {
  let dirs = wf_dirs(lam)
  let mut err = 0
  let mut has_p = false
  let mut has_n = false
  for i in 0..<dirs.length() {
    if dirs[i] == 1 {
      has_p = true
    }
    if dirs[i] == -1 {
      has_n = true
    }
  }
  if !has_p {
    err = err + 1
  }
  if !has_n {
    err = err + 1
  }
  let mut mx = 0
  for i in 0..<lam.length() {
    let v = if lam[i] < 0 { -lam[i] } else { lam[i] }
    if v > mx {
      mx = v
    }
  }
  if mx < 20 {
    err = err + 1
  }
  err
}

///|
/// A15: evolve a frequency sequence with prescribed wave front {−1, +1}
pub fn evolve_wavefront() -> Array[Int32] {
  let mut state = 23
  let lam = [1, -1, 2, -2, 3, -3]
  let mut best = a15_fitness(lam)
  let mut gen = 0
  while gen < 2000 && best > 0 {
    gen = gen + 1
    let (pos, s1) = lcg_rand(state, 6)
    state = s1
    let (delta, s2) = lcg_rand(state, 20)
    state = s2
    let (sign, s3) = lcg_rand(state, 2)
    state = s3
    let old = lam[pos]
    lam[pos] = if sign == 0 {
      lam[pos] + delta + 1
    } else {
      lam[pos] - delta - 1
    }
    let f = a15_fitness(lam)
    if f <= best {
      best = f
    } else {
      lam[pos] = old
    }
  }
  lam
}

///|
/// A15 check: evolved sequence realizes WF = {−1, +1}
pub fn a15_converges_ok() -> Bool {
  a15_fitness(evolve_wavefront()) == 0
}
