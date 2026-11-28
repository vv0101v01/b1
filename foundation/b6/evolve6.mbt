///|
/// Evolutionary algorithms A16–A18 (batch 6, continuing A13–A15).
/// Deterministic greedy hill-climbing: scan all single-gene mutations
/// (3 step sizes × 2 signs) per generation, accept non-worsening moves.

///|
/// A16 fitness: derived transversality of (f, g) = (αx+βy, γx+δy):
/// transverse ⟺ det[α β; γ δ] ≢ 0 mod 5
pub fn a16_fitness(
  alpha : Int32,
  beta : Int32,
  gamma : Int32,
  delta : Int32,
) -> Int32 {
  let det = (alpha * delta - beta * gamma) % 5
  if (det % 5 + 5) % 5 == 0 {
    1
  } else {
    0
  }
}

///|
/// A16: evolve two linear equations toward transversality
pub fn evolve_transverse() -> (Int32, Int32, Int32, Int32) {
  let mut alpha = 1
  let mut beta = 1
  let mut gamma = 1
  let mut delta = 1 // degenerate start: det = 0
  let mut best = a16_fitness(alpha, beta, gamma, delta)
  let mut gen = 0
  while gen < 40 && best > 0 {
    gen = gen + 1
    // try mutating each slot
    let slots = [alpha, beta, gamma, delta]
    let mut improved = false
    let mut s = 0
    while s < 4 && !improved {
      let mut step = 1
      while step <= 3 && !improved {
        let mut sg = 0
        while sg < 2 && !improved {
          let d = if sg == 0 { step } else { -step }
          let cand = [slots[0], slots[1], slots[2], slots[3]]
          let cand2 = [0, 0, 0, 0]
          for t in 0..<4 {
            cand2[t] = cand[t]
          }
          cand2[s] = cand2[s] + d
          let f = a16_fitness(cand2[0], cand2[1], cand2[2], cand2[3])
          if f < best {
            best = f
            alpha = cand2[0]
            beta = cand2[1]
            gamma = cand2[2]
            delta = cand2[3]
            improved = true
          }
          sg = sg + 1
        }
        step = step + 1
      }
      s = s + 1
    }
  }
  (alpha, beta, gamma, delta)
}

///|
/// A16 check: evolved pair is transverse
pub fn a16_converges_ok() -> Bool {
  let (a, b, c, d) = evolve_transverse()
  a16_fitness(a, b, c, d) == 0
}

///|
/// A17 fitness: spherical (bounded radial) Hecke eigenfunction on the
/// (q+1)-tree, q = 5: constancy φ₀ = φ₁ = φ₂ = φ₃ (bounded at infinity
/// in the truncation) plus eigen equations:
/// λφ₀ = 6φ₁; λφ₁ = φ₀ + 5φ₂; λφ₂ = φ₁ + 5φ₃.
pub fn a17_fitness(
  f0 : Int32,
  f1 : Int32,
  f2 : Int32,
  f3 : Int32,
  lam : Int32,
) -> Int32 {
  let mut err = 0
  if lam * f0 != 6 * f1 {
    err = err + 1
  }
  if lam * f1 != f0 + 5 * f2 {
    err = err + 1
  }
  if lam * f2 != f1 + 5 * f3 {
    err = err + 1
  }
  if f0 != f1 {
    err = err + 1
  }
  if f1 != f2 {
    err = err + 1
  }
  if f2 != f3 {
    err = err + 1
  }
  err
}

///|
/// A17: evolve the radial eigenfunction toward the spherical Hecke
/// eigenform (solution: φ ≡ c, λ = 6 = α + β with αβ = 5)
pub fn evolve_hecke_eigen() -> (Int32, Int32, Int32, Int32, Int32) {
  let mut f0 = 1
  let mut f1 = 1
  let mut f2 = 1
  let mut f3 = 1
  let mut lam = 3
  let mut best = a17_fitness(f0, f1, f2, f3, lam)
  let mut gen = 0
  while gen < 200 && best > 0 {
    gen = gen + 1
    let mut improved = false
    let mut slot = 0
    while slot < 5 && !improved {
      let mut step = 1
      while step <= 3 && !improved {
        let mut sg = 0
        while sg < 2 && !improved {
          let d = if sg == 0 { step } else { -step }
          let of0 = f0
          let of1 = f1
          let of2 = f2
          let of3 = f3
          let olam = lam
          if slot == 0 {
            f0 = f0 + d
          } else if slot == 1 {
            f1 = f1 + d
          } else if slot == 2 {
            f2 = f2 + d
          } else if slot == 3 {
            f3 = f3 + d
          } else {
            lam = lam + d
          }
          let f = a17_fitness(f0, f1, f2, f3, lam)
          if f < best {
            best = f
            improved = true
          } else {
            f0 = of0
            f1 = of1
            f2 = of2
            f3 = of3
            lam = olam
          }
          sg = sg + 1
        }
        step = step + 1
      }
      slot = slot + 1
    }
  }
  (f0, f1, f2, f3, lam)
}

///|
/// A17 check: evolved eigenfunction satisfies all constraints
pub fn a17_converges_ok() -> Bool {
  let (f0, f1, f2, f3, lam) = evolve_hecke_eigen()
  a17_fitness(f0, f1, f2, f3, lam) == 0
}

///|
/// A18 fitness: closed-loop consistency of candidate traces
/// (a₂, a₃, a₅, a₇): must equal the true X₀(11) traces f[p]
/// (the unique fixed point of automorphic ↔ Galois ↔ local ↔ global)
pub fn a18_fitness(a2 : Int64, a3 : Int64, a5 : Int64, a7 : Int64) -> Int32 {
  let f = newform_level11(20)
  let mut err = 0
  if a2 != f[2] {
    err = err + 1
  }
  if a3 != f[3] {
    err = err + 1
  }
  if a5 != f[5] {
    err = err + 1
  }
  if a7 != f[7] {
    err = err + 1
  }
  err
}

///|
/// A18: evolve the trace vector to the closed-loop fixed point
pub fn evolve_traces() -> (Int64, Int64, Int64, Int64) {
  let mut a2 = 0L
  let mut a3 = 0L
  let mut a5 = 0L
  let mut a7 = 0L
  let mut best = a18_fitness(a2, a3, a5, a7)
  let mut gen = 0
  while gen < 200 && best > 0 {
    gen = gen + 1
    let mut improved = false
    let mut slot = 0
    while slot < 4 && !improved {
      let mut step = 1
      while step <= 3 && !improved {
        let mut sg = 0
        while sg < 2 && !improved {
          let d = if sg == 0 { step.to_int64() } else { -step.to_int64() }
          let oa2 = a2
          let oa3 = a3
          let oa5 = a5
          let oa7 = a7
          if slot == 0 {
            a2 = a2 + d
          } else if slot == 1 {
            a3 = a3 + d
          } else if slot == 2 {
            a5 = a5 + d
          } else {
            a7 = a7 + d
          }
          let f = a18_fitness(a2, a3, a5, a7)
          if f < best {
            best = f
            improved = true
          } else {
            a2 = oa2
            a3 = oa3
            a5 = oa5
            a7 = oa7
          }
          sg = sg + 1
        }
        step = step + 1
      }
      slot = slot + 1
    }
  }
  (a2, a3, a5, a7)
}

///|
/// A18 check: evolved traces = the closed-loop fixed point (−2, −1, 1, 2)
pub fn a18_converges_ok() -> Bool {
  let (a2, a3, a5, a7) = evolve_traces()
  a18_fitness(a2, a3, a5, a7) == 0 &&
  a2 == -2L &&
  a3 == -1L &&
  a5 == 1L &&
  a7 == -2L
}
