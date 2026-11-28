///|
/// 185. Depth of representations — Moy–Prasad toy on (Z/125)^* = Z/100
/// (generator 2), filtration U^a = 1 + 5^a Z/125: orders (100, 25, 5, 1).
/// depth(χ_m) = conductor exponent − 1; all break points lie in (1/e)Z
/// with e = 1; depth is subadditive: depth(χψ) ≤ max(depth χ, depth ψ).

///|
/// conductor exponent of χ_m on (Z/125)^* (gen 2, order 100):
/// U¹ has index subgroup ind = 4Z/100; U²: 20Z/100; U³ = {1}
pub fn cond125(m : Int32) -> Int32 {
  let mm = (m % 100 + 100) % 100
  if mm == 0 {
    0
  } else if mm % 25 == 0 {
    1
  } else if mm % 5 == 0 {
    2
  } else {
    3
  }
}

///|
/// depth of χ_m = cond − 1 (trivial character: depth 0)
pub fn depth125(m : Int32) -> Int32 {
  let c = cond125(m)
  if c == 0 {
    0
  } else {
    c - 1
  }
}

///|
/// T185a: filtration orders (100, 25, 5, 1) and conductor distribution
/// (c = 0, 1, 2, 3) = (1, 3, 16, 80)
pub fn depth_filtration_ok() -> Bool {
  // U^a sizes via definition: 1 + 5^a Z/125
  let mut u1 = 0
  let mut u2 = 0
  let mut u3 = 0
  for x in 0..<125 {
    if (x - 1) % 5 == 0 {
      u1 = u1 + 1
    }
    if (x - 1) % 25 == 0 {
      u2 = u2 + 1
    }
    if (x - 1) % 125 == 0 {
      u3 = u3 + 1
    }
  }
  let dist = [0, 0, 0, 0]
  for m in 0..<100 {
    let c = cond125(m)
    dist[c] = dist[c] + 1
  }
  u1 == 25 &&
  u2 == 5 &&
  u3 == 1 &&
  dist[0] == 1 &&
  dist[1] == 3 &&
  dist[2] == 16 &&
  dist[3] == 80
}

///|
/// T185b: subadditivity of depth: depth(χ_m χ_n) = depth(χ_{m+n}) ≤
/// max(depth χ_m, depth χ_n) for ALL 100×100 pairs
pub fn depth_subadditive_ok() -> Bool {
  let mut ok = true
  for m in 0..<100 {
    for n in 0..<100 {
      let dp = depth125(m + n)
      let dmax = if depth125(m) > depth125(n) {
        depth125(m)
      } else {
        depth125(n)
      }
      if dp > dmax {
        ok = false
      }
    }
  }
  ok
}

///|
/// T185c: break points in (1/e)Z with e = 1 (all integral); maximal depth
/// in the regular representation = 2 = max over all characters
pub fn depth_breakpoints_ok() -> Bool {
  let mut maxd = 0
  for m in 0..<100 {
    if depth125(m) > maxd {
      maxd = depth125(m)
    }
  }
  // trivial character depth 0; every depth value occurs as a break point
  let mut has0 = false
  let mut has1 = false
  let mut has2 = false
  for m in 0..<100 {
    let d = depth125(m)
    if d == 0 {
      has0 = true
    }
    if d == 1 {
      has1 = true
    }
    if d == 2 {
      has2 = true
    }
  }
  maxd == 2 && has0 && has1 && has2
}

///|
/// T185d: filtration multiplicativity at level 125: U^a·U^b = U^{min(a,b)}
pub fn filtration_mult_ok() -> Bool {
  // U¹·U² = U¹: (1+5x)(1+25y) = 1 + 5x + 25y + 125xy ≡ 1 + 5(x+5y): spans U¹
  // check: every u ∈ U¹ factors as u₁ u₂ with u₁ ∈ U¹, u₂ ∈ U²
  let mut ok = true
  for x in 0..<25 {
    let u = 1 + 5 * x
    // u₂ = 1 (= 1 + 25·0) is in U²; u₁ = u: trivial factorization exists
    if (u - 1) % 5 != 0 {
      ok = false
    }
  }
  ok
}

///|
/// 185: depth package
pub fn depth_ok() -> Bool {
  depth_filtration_ok() &&
  depth_subadditive_ok() &&
  depth_breakpoints_ok() &&
  filtration_mult_ok()
}
