///|
/// inter_coh.mbt — 58. 相交上同調 (intersection cohomology)
///
/// IC of a singular space X: the intermediate extension of the constant sheaf
/// from the smooth locus; for curves IC = constant (IH = H); for quotient
/// singularities X = Y/G: IH(X) = H(Y)^G. Decomposition theorem: for a
/// resolution π: Ỹ → Y: H(Ỹ) = IH(Y) ⊕ (vanishing cycles) — the failure is
/// measured by the singular strata (e.g. dual-graph cycles of a nodal curve).
///
/// Concrete: simplicial homology over F_p (chain complex + ranks); graph
/// cycle spaces; group-invariant parts; Poincaré duality checks.
///
/// Theorem engine:
///   T58a (同調演算法): b(S¹) = (1,1)、b(S²) = (1,0,1)、b(D²) = (1,0,0)
///   T58b (商奇點): H(Y/G) = H(Y)^G：S²/± = RP²：H²(S²)^{Z/2} = 0 (p odd)
///       與 H²(RP²; F_p) = 0 一致；E/± = P¹：H¹ 不變量 = 0 ✓
///   T58c (對偶圖): 節點曲線的 b₁(Γ) = E − V + 1（圈空間維數）
///   T58d (分解定理玩具): 正規化 P¹ → 節點三次曲線：多出的 H¹ = b₁(Γ) = 1

///|
/// Rank of a matrix over F_p (Gaussian elimination; rows × cols).
pub fn rank_mod(
  m : Array[Array[Int32]],
  rows : Int32,
  cols : Int32,
  p : Int32,
) -> Int32 {
  let a : Array[Array[Int32]] = []
  let mut i = 0
  while i < rows {
    let row : Array[Int32] = []
    let mut j = 0
    while j < cols {
      row.push((m[i][j] % p + p) % p)
      j = j + 1
    }
    a.push(row)
    i = i + 1
  }
  let mut rank = 0
  let mut col = 0
  let mut rr = 0
  while col < cols && rr < rows {
    let mut piv = rr
    while piv < rows && a[piv][col] == 0 {
      piv = piv + 1
    }
    if piv < rows {
      let tmp = a[rr]
      a[rr] = a[piv]
      a[piv] = tmp
      let inv = mod_inverse(a[rr][col].to_int64(), p.to_int64()).to_int()
      let mut j = col
      while j < cols {
        a[rr][j] = a[rr][j] * inv % p
        j = j + 1
      }
      let mut i2 = 0
      while i2 < rows {
        if i2 != rr && a[i2][col] != 0 {
          let f = a[i2][col]
          let mut j2 = col
          while j2 < cols {
            a[i2][j2] = ((a[i2][j2] - f * a[rr][j2]) % p + p) % p
            j2 = j2 + 1
          }
        }
        i2 = i2 + 1
      }
      rank = rank + 1
      rr = rr + 1
    } else {
      col = col + 1
    }
    // note: when pivot found we still advance col below
    if piv < rows {
      col = col + 1
    }
  }
  rank
}

///|
/// Simplicial homology Betti numbers over F_p from a full simplex list
/// (each simplex = sorted vertex array; the list must include all faces).
/// Returns (b₀, b₁, b₂) for a complex of dimension ≤ 2.
pub fn betti_simplicial(
  simplices : Array[Array[Int32]],
  p : Int32,
) -> (Int32, Int32, Int32) {
  // classify by dimension
  let v0 : Array[Array[Int32]] = []
  let e1 : Array[Array[Int32]] = []
  let f2 : Array[Array[Int32]] = []
  for s in simplices {
    if s.length() == 1 {
      v0.push(s)
    } else if s.length() == 2 {
      e1.push(s)
    } else if s.length() == 3 {
      f2.push(s)
    }
  }
  let nv = v0.length()
  let ne = e1.length()
  let nf = f2.length()
  // d1: vertices × edges
  let d1 : Array[Array[Int32]] = []
  let mut i1 = 0
  while i1 < nv {
    let row : Array[Int32] = []
    let mut j1 = 0
    while j1 < ne {
      row.push(0)
      j1 = j1 + 1
    }
    d1.push(row)
    i1 = i1 + 1
  }
  let mut j = 0
  while j < ne {
    let a = e1[j][0]
    let b = e1[j][1]
    let ia = find_vertex(v0, nv, a)
    let ib = find_vertex(v0, nv, b)
    if ia >= 0 {
      d1[ia][j] = (d1[ia][j] + 1) % p
    }
    if ib >= 0 {
      d1[ib][j] = (d1[ib][j] + p - 1) % p
    }
    j = j + 1
  }
  // d2: edges × faces
  let d2 : Array[Array[Int32]] = []
  let mut i2 = 0
  while i2 < ne {
    let row : Array[Int32] = []
    let mut j2 = 0
    while j2 < nf {
      row.push(0)
      j2 = j2 + 1
    }
    d2.push(row)
    i2 = i2 + 1
  }
  let mut k = 0
  while k < nf {
    let (x, y, z) = (f2[k][0], f2[k][1], f2[k][2])
    let iyz = find_edge(e1, ne, y, z)
    let ixz = find_edge(e1, ne, x, z)
    let ixy = find_edge(e1, ne, x, y)
    if iyz >= 0 {
      d2[iyz][k] = (d2[iyz][k] + 1) % p
    }
    if ixz >= 0 {
      d2[ixz][k] = (d2[ixz][k] + p - 1) % p
    }
    if ixy >= 0 {
      d2[ixy][k] = (d2[ixy][k] + 1) % p
    }
    k = k + 1
  }
  let r1 = rank_mod(d1, nv, ne, p)
  let r2 = rank_mod(d2, ne, nf, p)
  let b0 = nv - r1
  let b1 = ne - r1 - r2
  let b2 = nf - r2
  (b0, b1, b2)
}

///|
/// Index of vertex w in the vertex list (−1 if absent).
fn find_vertex(v0 : Array[Array[Int32]], nv : Int32, w : Int32) -> Int32 {
  let mut i = 0
  let mut r = -1
  while i < nv {
    if v0[i][0] == w {
      r = i
    }
    i = i + 1
  }
  r
}

///|
/// Index of edge {u, w} in the edge list (−1 if absent).
fn find_edge(
  e1 : Array[Array[Int32]],
  ne : Int32,
  u : Int32,
  w : Int32,
) -> Int32 {
  let mut i = 0
  let mut r = -1
  while i < ne {
    if (e1[i][0] == u && e1[i][1] == w) || (e1[i][0] == w && e1[i][1] == u) {
      r = i
    }
    i = i + 1
  }
  r
}

///|
/// S¹ as triangle boundary: V {0,1,2}, E {01,12,02}.
pub fn circle_simplices() -> Array[Array[Int32]] {
  [[0], [1], [2], [0, 1], [1, 2], [0, 2]]
}

///|
/// S² as tetrahedron boundary.
pub fn sphere_simplices() -> Array[Array[Int32]] {
  [
    [0],
    [1],
    [2],
    [3],
    [0, 1],
    [0, 2],
    [0, 3],
    [1, 2],
    [1, 3],
    [2, 3],
    [0, 1, 2],
    [0, 1, 3],
    [0, 2, 3],
    [1, 2, 3],
  ]
}

///|
/// Filled triangle (disk).
pub fn disk_simplices() -> Array[Array[Int32]] {
  [[0], [1], [2], [0, 1], [1, 2], [0, 2], [0, 1, 2]]
}

///|
/// Graph cycle-space dimension: b₁(Γ) = E − V + c (c = #components).
pub fn graph_cycle_dim(
  edges : Array[(Int32, Int32)],
  n_verts : Int32,
  n_components : Int32,
) -> Int32 {
  edges.length() - n_verts + n_components
}

///|
/// Group invariants of cohomology with a Z/2 action given by eigenvalues
/// (±1) on each graded piece (over F_p, p odd): invariants dim per piece.
pub fn z2_invariants_dims(
  eigenvalues : Array[Int32],
  p : Int32,
) -> Array[Int32] {
  let res : Array[Int32] = []
  for e in eigenvalues {
    // acts by e (mod p): invariants = full dim if e = 1, else 0 (p odd)
    res.push(if (e % p + p) % p == 1 { 1 } else { 0 })
  }
  res
}

///|
/// RP² chain complex over F_p (p odd): d₂ = 2 (attachment degree), d₁ = 0:
/// H = (1, 0, 0).
pub fn rp2_betti(p : Int32) -> (Int32, Int32, Int32) {
  // H₀ = F_p; H₁ = ker d₁ / im d₂ = F_p / 2F_p = 0 (p odd); H₂ = ker d₂ = 0
  let h1 = if 2 % p == 0 { 1 } else { 0 }
  let h2 = if 2 % p == 0 { 1 } else { 0 }
  (1, h1, h2)
}

///|
/// Poincaré duality on S²: b₀ = b₂ ✓ verified via betti.
pub fn poincare_duality_betti(b : (Int32, Int32, Int32)) -> Bool {
  b.0 == b.2
}
