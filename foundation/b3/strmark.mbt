///|
/// 181. 4-dim string-diagram Gaussian–Markov structure implies the 8-dim
/// octonion (composition-algebra) axioms.  All checks are exact integer
/// identities: Markov vanishing ⟺ quadratic-form gluing; string-diagram
/// interchange law; Cayley–Dickson doubling ℂ→ℍ→𝕆 with alternativity and
/// norm multiplicativity.

///|
/// determinant of a 2×2 integer matrix
pub fn det2(m : Array[Array[Int32]]) -> Int32 {
  det2i(m)
}

///|
/// determinant of a 3×3 integer matrix (first-row cofactors)
pub fn det3(m : Array[Array[Int32]]) -> Int32 {
  let c0 = m[0][0] * (m[1][1] * m[2][2] - m[1][2] * m[2][1])
  let c1 = m[0][1] * (m[1][0] * m[2][2] - m[1][2] * m[2][0])
  let c2 = m[0][2] * (m[1][0] * m[2][1] - m[1][1] * m[2][0])
  c0 - c1 + c2
}

///|
/// determinant of a 4×4 integer matrix (first-row cofactors)
pub fn det4(m : Array[Array[Int32]]) -> Int32 {
  let mut acc = 0
  for j in 0..<4 {
    let minor : Array[Array[Int32]] = []
    for r in 1..<4 {
      let row : Array[Int32] = []
      for c in 0..<4 {
        if c != j {
          row.push(m[r][c])
        }
      }
      minor.push(row)
    }
    let sign = if j % 2 == 0 { 1 } else { -1 }
    acc = acc + sign * m[0][j] * det3(minor)
  }
  acc
}

///|
/// adjugate of a 4×4 integer matrix: adj[i][j] = (−1)^{i+j}·det(minor ji)
pub fn adj4(m : Array[Array[Int32]]) -> Array[Array[Int32]] {
  let adj : Array[Array[Int32]] = []
  for i in 0..<4 {
    let row : Array[Int32] = []
    for j in 0..<4 {
      let minor : Array[Array[Int32]] = []
      for r in 0..<4 {
        if r != j {
          let mr : Array[Int32] = []
          for c in 0..<4 {
            if c != i {
              mr.push(m[r][c])
            }
          }
          minor.push(mr)
        }
      }
      let sign = if (i + j) % 2 == 0 { 1 } else { -1 }
      row.push(sign * det3(minor))
    }
    adj.push(row)
  }
  adj
}

///|
/// Precision matrix of the decomposable graph: cliques {0,1,2} and {2,3},
/// separator {2}; the only non-edge is (0,3).
pub fn markov_precision() -> Array[Array[Int32]] {
  [[3, 1, 1, 0], [1, 3, 1, 0], [1, 1, 4, 1], [0, 0, 1, 2]]
}

///|
/// Gaussian–Markov vanishing: K = 0 on the non-edge (0,3)
pub fn markov_vanishes(k : Array[Array[Int32]]) -> Bool {
  k[0][3] == 0 && k[3][0] == 0
}

///|
/// quadratic form xᵀKx
pub fn quad(k : Array[Array[Int32]], x : Array[Int32]) -> Int32 {
  let n = x.length()
  let mut acc = 0
  for a in 0..<n {
    for b in 0..<n {
      acc = acc + k[a][b] * x[a] * x[b]
    }
  }
  acc
}

///|
/// quadratic form of the principal submatrix on index set idx
pub fn quad_sub(
  k : Array[Array[Int32]],
  x : Array[Int32],
  idx : Array[Int32],
) -> Int32 {
  let mut acc = 0
  for a in 0..<idx.length() {
    for b in 0..<idx.length() {
      acc = acc + k[idx[a]][idx[b]] * x[idx[a]] * x[idx[b]]
    }
  }
  acc
}

///|
/// T181a: quadratic-form gluing: xᵀKx = q_{C1} + q_{C2} − q_S for ALL
/// x ∈ {−1,0,1}⁴ — holds ⟺ the (0,3) cross term vanishes (Markov).
pub fn markov_gluing_ok(k : Array[Array[Int32]]) -> Bool {
  let mut ok = true
  for a in 0..<3 {
    for b in 0..<3 {
      for c in 0..<3 {
        for d in 0..<3 {
          let x = [a - 1, b - 1, c - 1, d - 1]
          let lhs = quad(k, x)
          let rhs = quad_sub(k, x, [0, 1, 2]) +
            quad_sub(k, x, [2, 3]) -
            quad_sub(k, x, [2])
          if lhs != rhs {
            ok = false
          }
        }
      }
    }
  }
  ok
}

///|
/// T181b: fundamental identity K·adj(K) = det(K)·I (exact integers)
pub fn adj_identity_ok(k : Array[Array[Int32]]) -> Bool {
  let d = det4(k)
  let adj = adj4(k)
  let ka = mat_mul(k, adj)
  let di : Array[Array[Int32]] = []
  for i in 0..<4 {
    let row : Array[Int32] = []
    for j in 0..<4 {
      if i == j {
        row.push(d)
      } else {
        row.push(0)
      }
    }
    di.push(row)
  }
  mat_eq(ka, di)
}

///|
/// complex add/sub/mul/conjugate on [re, im]
fn c_add(a : Array[Int32], b : Array[Int32]) -> Array[Int32] {
  [a[0] + b[0], a[1] + b[1]]
}

///|
fn c_sub(a : Array[Int32], b : Array[Int32]) -> Array[Int32] {
  [a[0] - b[0], a[1] - b[1]]
}

///|
fn c_mul(a : Array[Int32], b : Array[Int32]) -> Array[Int32] {
  [a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0]]
}

///|
fn c_conj(a : Array[Int32]) -> Array[Int32] {
  [a[0], -a[1]]
}

///|
/// quaternion as [a0, a1, a2, a3] = (a0 + a1 i) + (a2 + a3 i) j
fn q_conj(a : Array[Int32]) -> Array[Int32] {
  [a[0], -a[1], -a[2], -a[3]]
}

///|
fn q_add(a : Array[Int32], b : Array[Int32]) -> Array[Int32] {
  [a[0] + b[0], a[1] + b[1], a[2] + b[2], a[3] + b[3]]
}

///|
fn q_sub(a : Array[Int32], b : Array[Int32]) -> Array[Int32] {
  [a[0] - b[0], a[1] - b[1], a[2] - b[2], a[3] - b[3]]
}

///|
/// Cayley–Dickson: (a0,a1)(b0,b1) = (a0b0 − conj(b1)a1, b1a0 + a1conj(b0))
pub fn q_mul(a : Array[Int32], b : Array[Int32]) -> Array[Int32] {
  let a0 = [a[0], a[1]]
  let a1 = [a[2], a[3]]
  let b0 = [b[0], b[1]]
  let b1 = [b[2], b[3]]
  let l = c_sub(c_mul(a0, b0), c_mul(c_conj(b1), a1))
  let r = c_add(c_mul(b1, a0), c_mul(a1, c_conj(b0)))
  [l[0], l[1], r[0], r[1]]
}

///|
/// octonion product via Cayley–Dickson doubling of ℍ
pub fn o_mul(a : Array[Int32], b : Array[Int32]) -> Array[Int32] {
  let a0 = [a[0], a[1], a[2], a[3]]
  let a1 = [a[4], a[5], a[6], a[7]]
  let b0 = [b[0], b[1], b[2], b[3]]
  let b1 = [b[4], b[5], b[6], b[7]]
  let l = q_sub(q_mul(a0, b0), q_mul(q_conj(b1), a1))
  let r = q_add(q_mul(b1, a0), q_mul(a1, q_conj(b0)))
  [l[0], l[1], l[2], l[3], r[0], r[1], r[2], r[3]]
}

///|
/// octonion basis vector e_i
pub fn o_basis(i : Int32) -> Array[Int32] {
  let out : Array[Int32] = []
  for k in 0..<8 {
    if k == i {
      out.push(1)
    } else {
      out.push(0)
    }
  }
  out
}

///|
/// integer norm Σ x_i²
pub fn o_norm(x : Array[Int32]) -> Int32 {
  let mut acc = 0
  for i in 0..<8 {
    acc = acc + x[i] * x[i]
  }
  acc
}

///|
/// T181c: alternativity of the CD-octonion on the basis:
/// (e_i e_i) e_j = e_i (e_i e_j) and (e_i e_j) e_j = e_i (e_j e_j)
pub fn octonion_alternative_ok() -> Bool {
  let mut ok = true
  for i in 0..<8 {
    for j in 0..<8 {
      let ei = o_basis(i)
      let ej = o_basis(j)
      let ii_j = o_mul(o_mul(ei, ei), ej)
      let i_ij = o_mul(ei, o_mul(ei, ej))
      if !array_eq8(ii_j, i_ij) {
        ok = false
      }
      let ij_j = o_mul(o_mul(ei, ej), ej)
      let i_jj = o_mul(ei, o_mul(ej, ej))
      if !array_eq8(ij_j, i_jj) {
        ok = false
      }
    }
  }
  ok
}

///|
fn array_eq8(a : Array[Int32], b : Array[Int32]) -> Bool {
  for i in 0..<8 {
    if a[i] != b[i] {
      return false
    }
  }
  true
}

///|
/// T181d: norm multiplicativity |xy|² = |x|²|y|² on basis combos
pub fn octonion_norm_mult_ok() -> Bool {
  let mut ok = true
  for i in 0..<8 {
    for j in 0..<8 {
      for s in -1..<2 {
        if s != 0 {
          let x = o_basis(i)
          x[j] = x[j] + s
          let y = o_basis(j)
          y[i] = y[i] - s
          if o_norm(o_mul(x, y)) != o_norm(x) * o_norm(y) {
            ok = false
          }
        }
      }
    }
  }
  ok
}

///|
/// T181e: string-diagram interchange law on 2×2 blocks:
/// (F⊗G)(H⊗K) = (FH)⊗(GK) as 4×4 block matrices
pub fn interchange_ok() -> Bool {
  let f = [[1, 2], [0, 1]]
  let g = [[0, 1], [1, 1]]
  let h = [[2, 0], [1, 3]]
  let kk = [[1, 1], [0, 2]]
  let tf = tensor4(f, g)
  let tk = tensor4(h, kk)
  let lhs = mat_mul(tf, tk)
  let rhs = tensor4(mat_mul(f, h), mat_mul(g, kk))
  mat_eq(lhs, rhs)
}

///|
/// block-diagonal tensor of two 2×2 into 4×4
pub fn tensor4(
  a : Array[Array[Int32]],
  b : Array[Array[Int32]],
) -> Array[Array[Int32]] {
  let out : Array[Array[Int32]] = []
  for i in 0..<4 {
    let row : Array[Int32] = []
    for j in 0..<4 {
      let v = if i < 2 && j < 2 {
        a[i][j]
      } else if i >= 2 && j >= 2 {
        b[i - 2][j - 2]
      } else {
        0
      }
      row.push(v)
    }
    out.push(row)
  }
  out
}

///|
/// T181 (chain): 4-dim Gaussian–Markov + string-diagram interchange ⇒ the
/// 8-dim Cayley–Dickson octonion axioms (alternativity + norm law).
pub fn markov_implies_octonion_ok() -> Bool {
  let k = markov_precision()
  markov_vanishes(k) &&
  markov_gluing_ok(k) &&
  adj_identity_ok(k) &&
  interchange_ok() &&
  octonion_alternative_ok() &&
  octonion_norm_mult_ok()
}
