///|
/// synth.mbt — 批次八·模組 8：綜合高階範疇論（有限單純集模型）
///
/// 以「半單純集」（只記錄面映射）作為有限單純集的模型：
///   B8SS.dims[d][s] = 第 s 個 d-單形的 (d+1) 個面（下標指向 dims[d-1]）。
/// 可計算的內容：
///   1. 範疇的神經 N(C)：N_n = 可複合 n 元組；面映射由合成／刪除給出；
///      並以窮舉驗證單純恆等式 d_i d_j = d_{j-1} d_i（i < j）。
///   2. 內角（inner horn）Λ^n_i 的填充：準範疇（quasi-category）判定；
///      每一組可複合對 (g, f) 給出唯一填充 ⇒ 填充數 = 合成運算的自由度。
///   3. Δ² 的所有子半單純集之枚舉，以及其中「內角可填充」者之計數。
///   4. 退化結構的鏈數對照（N_n 的成長率）。

///|
/// 半單純集。
pub(all) struct B8SS {
  dims : Array[Array[Array[Int32]]]
}

///|
/// 由面資料建構。
pub fn b8ss_make(dims : Array[Array[Array[Int32]]]) -> B8SS {
  { dims, }
}

///|
/// 範疇的神經（維度 0…3）。面孔的約定：d_0 為「刪去最後一個箭頭」。
pub fn b8ss_nerve(c : B8Cat) -> B8SS {
  // 維度 0：物件
  let d0 : Array[Array[Int32]] = []
  for _ in 0..<c.nob {
    let e : Array[Int32] = []
    d0.push(e)
  }
  // 維度 1：態射 m，d_0(m) = dom m，d_1(m) = cod m
  let d1 : Array[Array[Int32]] = []
  for m in 0..<c.nmor {
    d1.push([c.cod[m], c.dom[m]])
  }
  // 維度 2：可複合對 (f, g)（cod f = dom g），面 d_0 = g、d_1 = g∘f、d_2 = f
  let d2 : Array[Array[Int32]] = []
  let pairIdx : Array[Array[Int32]] = []
  for f in 0..<c.nmor {
    for g in 0..<c.nmor {
      if c.cod[f] == c.dom[g] {
        d2.push([g, c.cmp[g * c.nmor + f], f])
        pairIdx.push([f, g])
      }
    }
  }
  // 維度 3：三元組 (f, g, h) 可合成，面為對應的 2-單形下標
  let d3 : Array[Array[Int32]] = []
  for f in 0..<c.nmor {
    for g in 0..<c.nmor {
      for h in 0..<c.nmor {
        if c.cod[f] == c.dom[g] && c.cod[g] == c.dom[h] {
          // d_0 = (g,h)、d_1 = (g∘f, h)、d_2 = (f, h∘g)、d_3 = (f, g)
          let a = b8ss_pair_pos(pairIdx, g, h)
          let b = b8ss_pair_pos(pairIdx, c.cmp[g * c.nmor + f], h)
          let cc = b8ss_pair_pos(pairIdx, f, c.cmp[h * c.nmor + g])
          let dd = b8ss_pair_pos(pairIdx, f, g)
          d3.push([a, b, cc, dd])
        }
      }
    }
  }
  let dims : Array[Array[Array[Int32]]] = [d0, d1, d2, d3]
  b8ss_make(dims)
}

///|
/// 在 2-單形清單中尋找 (f, g) 的位置。
fn b8ss_pair_pos(idx : Array[Array[Int32]], f : Int32, g : Int32) -> Int32 {
  let mut pos = -1
  for i in 0..<idx.length() {
    if idx[i][0] == f && idx[i][1] == g {
      pos = i
    }
  }
  pos
}

///|
/// 驗證單純恆等式（維度 ≤ 3）：d_i d_j = d_{j-1} d_i（i < j）。
pub fn b8ss_identities(s : B8SS) -> Bool {
  let mut ok = true
  for d in 1..<s.dims.length() {
    for simplex in s.dims[d] {
      let k = simplex.length()
      for i in 0..<(k - 1) {
        for j in 0..<(k - 1) {
          if i < j {
            // d_i d_j = d_{j-1} d_i
            let fi = s.dims[d - 1][simplex[j]]
            let lhs = fi[i]
            let fj = s.dims[d - 1][simplex[i]]
            let rhs = fj[j - 1]
            if lhs != rhs {
              ok = false
            }
          }
        }
      }
    }
  }
  ok
}

///|
/// 內角 Λ^n_i 的填充：是否存在 n-單形 t 使 d_j t = x_j（j ≠ i），
/// 其中 (x_j) 為 (n−1)-單形之相容族。回傳 (是否存在, 相容族數, 填充數)。
pub fn b8ss_inner_horn(s : B8SS, n : Int32, i : Int32) -> (Bool, Int32, Int32) {
  if n < 2 || i <= 0 || i >= n {
    return (false, 0, 0)
  }
  let faces = s.dims[n - 1]
  let nf = faces.length()
  // 相容族：下標元組（長度 n+1，第 i 位任意）
  let horns : Array[Array[Int32]] = []
  let total : Int32 = b8_pow_int(nf, n + 1)
  for code in 0..<total {
    let t : Array[Int32] = []
    let mut c = code
    for _ in 0..<(n + 1) {
      t.push(c % nf)
      c = c / nf
    }
    let mut ok = true
    for j in 0..<(n + 1) {
      for k in 0..<(n + 1) {
        if j != i && k != i && j < k {
          // d_j x_k = d_{k-1} x_j
          let l = faces[t[k]][j]
          let r = faces[t[j]][k - 1]
          if l != r {
            ok = false
          }
        }
      }
    }
    if ok {
      horns.push(t)
    }
  }
  let mut filled = 0
  let mut allfilled = true
  for h in horns {
    let mut found = false
    for t in s.dims[n] {
      let mut eq = true
      for j in 0..<(n + 1) {
        if j != i && t[j] != h[j] {
          eq = false
        }
      }
      if eq {
        found = true
      }
    }
    if found {
      filled = filled + 1
    } else {
      allfilled = false
    }
  }
  (allfilled && horns.length() > 0, horns.length(), filled)
}

///|
/// 是否為準範疇（維度 2、3 的內角全部可填充）。
pub fn b8ss_is_quasicat(s : B8SS) -> Bool {
  let (a, _, _) = b8ss_inner_horn(s, 2, 1)
  let (b, _, _) = b8ss_inner_horn(s, 3, 1)
  let (c, _, _) = b8ss_inner_horn(s, 3, 2)
  a && b && c
}

///|
/// 是否為 Kan 複形（含外角；維度 2 檢驗）。
pub fn b8ss_is_kan2(s : B8SS) -> Bool {
  let (a, _, _) = b8ss_inner_horn(s, 2, 1)
  // 外角：Λ²_0 與 Λ²_2
  let (b, _, _) = b8ss_outer_horn(s, 2, 0)
  let (c, _, _) = b8ss_outer_horn(s, 2, 2)
  a && b && c
}

///|
/// 外角 Λ^n_0 或 Λ^n_n 的填充。
pub fn b8ss_outer_horn(s : B8SS, n : Int32, i : Int32) -> (Bool, Int32, Int32) {
  let faces = s.dims[n - 1]
  let nf = faces.length()
  let horns : Array[Array[Int32]] = []
  let total : Int32 = b8_pow_int(nf, n + 1)
  for code in 0..<total {
    let t : Array[Int32] = []
    let mut c = code
    for _ in 0..<(n + 1) {
      t.push(c % nf)
      c = c / nf
    }
    let mut ok = true
    for j in 0..<(n + 1) {
      for k in 0..<(n + 1) {
        if j != i && k != i && j < k {
          let l = faces[t[k]][j]
          let r = faces[t[j]][k - 1]
          if l != r {
            ok = false
          }
        }
      }
    }
    if ok {
      horns.push(t)
    }
  }
  let mut filled = 0
  let mut allfilled = true
  for h in horns {
    let mut found = false
    for t in s.dims[n] {
      let mut eq = true
      for j in 0..<(n + 1) {
        if j != i && t[j] != h[j] {
          eq = false
        }
      }
      if eq {
        found = true
      }
    }
    if found {
      filled = filled + 1
    } else {
      allfilled = false
    }
  }
  (allfilled && horns.length() > 0, horns.length(), filled)
}

///|
/// Δ² 的半單純子集：7 個胞腔（3 頂點 0,1,2；3 邊 01,12,02；1 三角形）以位元遮罩表示。
/// 若面封閉則建構半單純集，否則回傳 None。
pub fn b8ss_subset_of_delta2(mask : Int32) -> B8SS? {
  let has = fn(b : Int32) -> Bool { ((mask >> b) & 1) == 1 }
  // 面封閉檢查
  if has(3) && !(has(0) && has(1)) {
    return None
  }
  if has(4) && !(has(1) && has(2)) {
    return None
  }
  if has(5) && !(has(0) && has(2)) {
    return None
  }
  if has(6) && !(has(3) && has(4) && has(5)) {
    return None
  }
  // 頂點清單與位置
  let vtx : Array[Array[Int32]] = []
  let vpos : Array[Int32] = [-1, -1, -1]
  for v in 0..<3 {
    if has(v) {
      vpos[v] = vtx.length()
      let e : Array[Int32] = []
      vtx.push(e)
    }
  }
  // 邊清單：面 d_0 = 終點、d_1 = 起點
  let edges : Array[Array[Int32]] = []
  let epos : Array[Int32] = [-1, -1, -1]
  // 邊 3 = (0,1)、4 = (1,2)、5 = (0,2)
  if has(3) {
    epos[0] = edges.length()
    edges.push([vpos[1], vpos[0]])
  }
  if has(4) {
    epos[1] = edges.length()
    edges.push([vpos[2], vpos[1]])
  }
  if has(5) {
    epos[2] = edges.length()
    edges.push([vpos[2], vpos[0]])
  }
  let tris : Array[Array[Int32]] = []
  if has(6) {
    // 三角形 (0,1,2)：d_0 = (1,2)、d_1 = (0,2)、d_2 = (0,1)
    tris.push([epos[1], epos[2], epos[0]])
  }
  let d3 : Array[Array[Int32]] = []
  let dims : Array[Array[Array[Int32]]] = [vtx, edges, tris, d3]
  Some(b8ss_make(dims))
}

///|
/// 統計 Δ² 的所有子半單純集中，內角可填充（Λ²_1 有填充）者之數。
pub fn b8ss_count_quasi_subsets() -> (Int32, Int32) {
  let mut total = 0
  let mut quasi = 0
  for mask in 0..<128 {
    match b8ss_subset_of_delta2(mask) {
      Some(s) => {
        total = total + 1
        let (ok, _, _) = b8ss_inner_horn(s, 2, 1)
        if ok {
          quasi = quasi + 1
        }
      }
      None => ()
    }
  }
  (total, quasi)
}
