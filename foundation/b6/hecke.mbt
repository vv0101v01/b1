///|
/// 197. Hecke action on shtuka moduli — Bruhat–Tits tree of GL₂ over a
/// local field with q = 5: the (q+1)-regular tree ball of radius 2
/// (37 vertices, 36 edges = shtuka modifications).  Hecke relation
/// A² = (q+1)·I + E₂ on the interior; spherical eigenvalue q+1 = α + β
/// with αβ = q (Satake); radial Hecke operators commute.

///|
/// tree ball radius 2, q = 5: vertex 0 = root, 1..6 = level 1,
/// 7..36 = level 2 (children of 1..6 in groups of 5)
pub fn tree_adjacency() -> Array[Array[Int32]] {
  let n = 37
  let a : Array[Array[Int32]] = []
  for _i in 0..<n {
    let row : Array[Int32] = []
    for _j in 0..<n {
      row.push(0)
    }
    a.push(row)
  }
  // root-level1
  for i in 1..<7 {
    a[0][i] = 1
    a[i][0] = 1
  }
  // level1-level2: vertex 7+m has parent 1 + m/5
  for m in 0..<30 {
    let v = 7 + m
    let parent = 1 + m / 5
    a[v][parent] = 1
    a[parent][v] = 1
  }
  a
}

///|
fn mat_sq(a : Array[Array[Int32]]) -> Array[Array[Int32]] {
  let n = a.length()
  let out : Array[Array[Int32]] = []
  for i in 0..<n {
    let row : Array[Int32] = []
    for j in 0..<n {
      let mut acc = 0
      for k in 0..<n {
        acc = acc + a[i][k] * a[k][j]
      }
      row.push(acc)
    }
    out.push(row)
  }
  out
}

///|
/// T197a: Hecke relation on interior rows (root + level 1):
/// A² = (q+1)·I + E₂ where E₂ = distance-2 adjacency (0-1 valued)
pub fn hecke_relation_ok() -> Bool {
  let a = tree_adjacency()
  let a2 = mat_sq(a)
  let q1 = 6
  let mut ok = true
  for i in 0..<7 {
    for j in 0..<37 {
      let e2 = a2[i][j] - (if i == j { q1 } else { 0 })
      if e2 != 0 && e2 != 1 {
        ok = false
      }
      // distance-2 support check vs tree structure
      let d2 = tree_dist(i, j) == 2
      if (e2 == 1) != d2 {
        ok = false
      }
    }
  }
  ok
}

///|
/// distance in the ball graph (BFS-free closed form by construction)
fn tree_dist(i : Int32, j : Int32) -> Int32 {
  if i == j {
    return 0
  }
  let li = if i == 0 { 0 } else if i < 7 { 1 } else { 2 }
  let lj = if j == 0 { 0 } else if j < 7 { 1 } else { 2 }
  let pi = if li == 2 { 1 + (i - 7) / 5 } else { i }
  let pj = if lj == 2 { 1 + (j - 7) / 5 } else { j }
  if li == 0 && lj == 1 {
    1
  } else if li == 1 && lj == 0 {
    1
  } else if li == 0 && lj == 2 {
    2
  } else if li == 2 && lj == 0 {
    2
  } else if li == 1 && lj == 1 {
    2 // distinct level-1 vertices meet at root
  } else if li == 1 && lj == 2 {
    if pj == i {
      1 // j is a child of i
    } else {
      3 // through root
    }
  } else if li == 2 && lj == 1 {
    if pi == j {
      1 // i is a child of j
    } else {
      3
    }
  } else if pi == pj {
    2 // siblings
  } else {
    4 // cousin via root
  }
}

///|
/// T197b: shtuka modifications = edges of the tree: 6 + 30 = 36 edges;
/// the constant function is spherical: A·1 = (q+1)·1 at interior vertices
pub fn shtuka_count_ok() -> Bool {
  let a = tree_adjacency()
  let mut edges = 0
  for i in 0..<37 {
    for j in (i + 1)..<37 {
      if a[i][j] == 1 {
        edges = edges + 1
      }
    }
  }
  let _unused_i = 0
  // spherical check at interior
  let mut sph = true
  for i in 0..<7 {
    let mut deg = 0
    for j in 0..<37 {
      deg = deg + a[i][j]
    }
    if deg != 6 {
      sph = false
    }
  }
  edges == 36 && sph
}

///|
/// T197c: Satake: spherical eigenvalue λ = q + 1 = α + β with αβ = q
/// (α = q, β = 1): exact integer check; radial Hecke operators e₁, e₂
/// commute (matrix check on the ball)
pub fn satake_ok() -> Bool {
  let q = 5
  let lambda = q + 1
  let alpha = q
  let beta = 1
  let satake = alpha + beta == lambda && alpha * beta == q
  // commutativity of radial operators: e₁ = A, e₂ = E₂: A·E₂ = E₂·A
  let a = tree_adjacency()
  let a2 = mat_sq(a)
  let e2 : Array[Array[Int32]] = []
  for i in 0..<37 {
    let row : Array[Int32] = []
    for j in 0..<37 {
      let v = a2[i][j] - (if i == j { 6 } else { 0 })
      row.push(v)
    }
    e2.push(row)
  }
  let lhs = mat_mul(a, e2)
  let rhs = mat_mul(e2, a)
  let mut comm = true
  for i in 0..<37 {
    for j in 0..<37 {
      if lhs[i][j] != rhs[i][j] {
        comm = false
      }
    }
  }
  satake && comm
}

///|
/// 197: Hecke package
pub fn hecke_ok() -> Bool {
  hecke_relation_ok() && shtuka_count_ok() && satake_ok()
}
