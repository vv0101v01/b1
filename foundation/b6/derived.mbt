///|
/// 191. Derived algebraic geometry and derived stacks — computational model.
/// Derived intersections via Koszul homology over the artinian ring
/// R = F₅[x,y]/(x⁴, y⁴) (16-dim); derived stack = action groupoid [X/G]
/// with orbifold Euler characteristic |X|/|G|.

///|
/// rank of an integer matrix over F_p (Gaussian elimination)
pub fn rank_p(m : Array[Array[Int32]], p : Int32) -> Int32 {
  let rows = m.length()
  if rows == 0 {
    return 0
  }
  let cols = m[0].length()
  let mat : Array[Array[Int32]] = []
  for i in 0..<rows {
    let row : Array[Int32] = []
    for j in 0..<cols {
      row.push((m[i][j] % p + p) % p)
    }
    mat.push(row)
  }
  let mut rank = 0
  let mut col = 0
  let mut row = 0
  while row < rows && col < cols {
    let mut pivot = -1
    for i in row..<rows {
      if pivot < 0 && mat[i][col] != 0 {
        pivot = i
      }
    }
    if pivot < 0 {
      col = col + 1
    } else {
      let tmp = mat[row]
      mat[row] = mat[pivot]
      mat[pivot] = tmp
      let mut inv = 1
      for t in 1..<p {
        if t * mat[row][col] % p == 1 {
          inv = t
        }
      }
      for j in col..<cols {
        mat[row][j] = mat[row][j] * inv % p
      }
      for i in 0..<rows {
        if i != row && mat[i][col] != 0 {
          let f = mat[i][col]
          for j in col..<cols {
            mat[i][j] = ((mat[i][j] - f * mat[row][j]) % p + p) % p
          }
        }
      }
      rank = rank + 1
      row = row + 1
      col = col + 1
    }
  }
  rank
}

///|
/// R = F₅[x,y]/(x⁴,y⁴): elements = 16 coeff vectors indexed i*4+j ↦ x^i y^j
pub fn ring_mul(a : Array[Int32], b : Array[Int32]) -> Array[Int32] {
  let out : Array[Int32] = []
  for _k in 0..<16 {
    out.push(0)
  }
  for i in 0..<4 {
    for j in 0..<4 {
      for k2 in 0..<4 {
        for l in 0..<4 {
          if i + k2 < 4 && j + l < 4 {
            let idx = (i + k2) * 4 + (j + l)
            out[idx] = (out[idx] + a[i * 4 + j] * b[k2 * 4 + l]) % 5
          }
        }
      }
    }
  }
  out
}

///|
/// monomial x^i y^j as ring element
pub fn mono(i : Int32, j : Int32) -> Array[Int32] {
  let out : Array[Int32] = []
  for _k in 0..<16 {
    out.push(0)
  }
  out[i * 4 + j] = 1
  out
}

///|
/// Koszul homology dims (H₂, H₁, H₀) of (f, g) on R:
/// 0 → R →[(-g,f)] R² →[(f,g)] R → 0 over F₅
pub fn koszul_dims(f : Array[Int32], g : Array[Int32]) -> (Int32, Int32, Int32) {
  // d2 : R → R² : a ↦ (−g·a, f·a): matrix 32×16
  let d2 : Array[Array[Int32]] = []
  for col in 0..<16 {
    let a = mono(col / 4, col % 4)
    let ga = ring_mul(g, a)
    let fa = ring_mul(f, a)
    let colv : Array[Int32] = []
    for k in 0..<16 {
      colv.push((-ga[k] % 5 + 5) % 5)
    }
    for k in 0..<16 {
      colv.push(fa[k])
    }
    d2.push(colv)
  }
  // transpose to 32 rows × 16 cols
  let d2t : Array[Array[Int32]] = []
  for r in 0..<32 {
    let row : Array[Int32] = []
    for c in 0..<16 {
      row.push(d2[c][r])
    }
    d2t.push(row)
  }
  // d1 : R² → R : (u, v) ↦ f·u + g·v: matrix 16×32
  let d1t : Array[Array[Int32]] = []
  for col in 0..<32 {
    let a = mono(col % 16 / 4, col % 16 % 4)
    let prod = if col < 16 { ring_mul(f, a) } else { ring_mul(g, a) }
    d1t.push(prod)
  }
  let d1 : Array[Array[Int32]] = []
  for r in 0..<16 {
    let row : Array[Int32] = []
    for c in 0..<32 {
      row.push(d1t[c][r])
    }
    d1.push(row)
  }
  let r2 = rank_p(d2t, 5) // rank of d2
  let r1 = rank_p(d1, 5) // rank of d1
  let h2 = 16 - r2
  let h0 = 16 - r1
  let h1 = 32 - r2 - r1
  (h2, h1, h0)
}

///|
/// T191a: Koszul identity for (f, g) = (x, 1): H = (0, 0, 0) (unit ideal)
/// and (f, g) = (x, y): H = (1, 2, 1) — the artinian "fat point" makes the
/// transverse intersection derived: H₂ = ann(x)∩ann(y) = (x³y³).
pub fn koszul_examples_ok() -> Bool {
  let x = mono(1, 0)
  let y = mono(0, 1)
  let unit = mono(0, 0)
  let h_unit = koszul_dims(x, unit)
  let h_xy = koszul_dims(x, y)
  h_unit == (0, 0, 0) && h_xy == (1, 2, 1)
}

///|
/// T191b: excess intersection (f, g) = (x, x): H = (4, 8, 4) — doubling
/// the equation doubles the derived data; Euler identity H₂ − H₁ + H₀ = 0
/// holds for every pair (complex Euler char = 16 − 32 + 16 = 0).
pub fn koszul_excess_ok() -> Bool {
  let x = mono(1, 0)
  let h_xx = koszul_dims(x, x)
  let mut chi_ok = true
  let pairs = [
    [mono(1, 0), mono(0, 1)],
    [mono(1, 0), mono(1, 0)],
    [mono(1, 0), mono(2, 0)],
    [mono(1, 1), mono(0, 1)],
  ]
  for i in 0..<4 {
    let h = koszul_dims(pairs[i][0], pairs[i][1])
    if h.0 - h.1 + h.2 != 0 {
      chi_ok = false
    }
  }
  h_xx == (4, 8, 4) && chi_ok
}

///|
/// T191c: derived stack [X/G]: X = F₅², G = Z/2 acting by −1:
/// Burnside #orbits = (|X| + |Fix|)/2 = 13; orbifold Euler
/// Σ 1/|stab| = |X|/|G| = 25/2 (checked as 2·Σ = 25).
pub fn action_groupoid_ok() -> Bool {
  // fixed points of −id on F₅²: (x, y) = (−x, −y) ⇒ 2x = 0 ⇒ x = 0 (char 5)
  let mut fix = 0
  for x in 0..<5 {
    for y in 0..<5 {
      if 2 * x % 5 == 0 && 2 * y % 5 == 0 {
        fix = fix + 1
      }
    }
  }
  let orbits = (25 + fix) / 2
  // orbifold Euler char: Σ_{orbits} 1/|stab| = (25 − fix)/2 + fix·(1/2)
  // = 25/2 = |X|/|G|: 2·χ = 25 exactly
  let free_orbits = (25 - fix) / 2
  let twice_chi = 2 * free_orbits + fix
  fix == 1 && orbits == 13 && twice_chi == 25
}

///|
/// 191: derived AG package
pub fn derived_ok() -> Bool {
  koszul_examples_ok() && koszul_excess_ok() && action_groupoid_ok()
}
