///|
/// der11.mbt — 批次十一·模組 3：導出範疇、單純形層、(∞,1)-幾何態射、反常層、ℓ-進層
///
/// 導出範疇：以 Čech 複形的上同調具體實現 Ext^n（模 p 高斯消去）。
/// 單純形層：以「有序（允許退化）Čech 複形」實現單純形對象，並與交替複形比對。
/// (∞,1)-幾何態射：在截斷複形（預層鏈）上核對伴隨恆等式。
/// 反常層：以中中間偏差公式 ^p H^n = H^n(U) + H^{n−1}(Z) 計算交集上同調。
/// ℓ-進層：核對貝蒂數與 ℓ 無關（ℓ = 5, 7）。

// ───────────────────────── 導出範疇 ─────────────────────────

///|
/// Ext^n(ℤ/p, ℤ/p) 的維數表（= H^n(X; ℤ/p)）。
pub fn b11_ext_dims(cv : B9Cover, pmax : Int32, pm : Int32) -> Array[Int32] {
  let out : Array[Int32] = []
  for n in 0..<=pmax {
    out.push(b9_cech_h(cv, n, pm))
  }
  out
}

///|
/// 空間的連通分量數：以「所有既開又閉的子集」分離點。
pub fn b11_connected_components(t : B9Top) -> Int32 {
  let par : Array[Int32] = []
  for p in 0..<t.npt {
    par.push(p)
  }
  for p in 0..<t.npt {
    for q in 0..<t.npt {
      if p < q {
        let mut sep = false
        for i in 0..<t.opens.length() {
          // 開集 i 是否為閉（補集也是開集）
          let comp : Array[Bool] = []
          for r in 0..<t.npt {
            comp.push(!t.opens[i][r])
          }
          if b9_top_find(t, comp) >= 0 && t.opens[i][p] != t.opens[i][q] {
            sep = true
          }
        }
        if !sep {
          let mut r1 = p
          while par[r1] != r1 {
            r1 = par[r1]
          }
          let mut r2 = q
          while par[r2] != r2 {
            r2 = par[r2]
          }
          if r1 != r2 {
            par[r2] = r1
          }
        }
      }
    }
  }
  let mut c = 0
  for p in 0..<t.npt {
    if par[p] == p {
      c = c + 1
    }
  }
  c
}

///|
/// Ext^0 = Hom 的檢驗：dim H^0(X; ℤ/p) 應等於空間的連通分量數。
pub fn b11_ext0_check(cv : B9Cover, pm : Int32) -> (Int32, Int32) {
  (b9_cech_h(cv, 0, pm), b11_connected_components(cv.site.top))
}

// ───────────────────────── 單純形層 ─────────────────────────

///|
/// 元組的交集點集（點位元表）。
fn b11_tuple_pts_bool(
  s : B9Site,
  cv : B9Cover,
  tup : Array[Int32],
) -> Array[Bool] {
  let acc : Array[Bool] = []
  for _ in 0..<s.top.npt {
    acc.push(true)
  }
  for i in tup {
    let o = s.top.opens[s.opens[s.cat.dom[cv.fam[i]]]]
    for p in 0..<s.top.npt {
      if !o[p] {
        acc[p] = false
      }
    }
  }
  acc
}

///|
/// 點 p 在開集（點集）內的分量代表（同分量取最小點）；不在其中回 -1。
fn b11_open_comp_of(s : B9Site, pts : Array[Bool], p : Int32) -> Int32 {
  if !pts[p] {
    return -1
  }
  // 以特殊化預序在 pts 內合併
  let par : Array[Int32] = []
  for q in 0..<s.top.npt {
    par.push(q)
  }
  for a in 0..<s.top.npt {
    for b in 0..<s.top.npt {
      if pts[a] && pts[b] && a != b {
        let mut spec = true
        for w in 0..<s.cat.nob {
          let ow = s.top.opens[s.opens[w]]
          if ow[b] && !ow[a] {
            spec = false
          }
        }
        if spec {
          let mut r1 = a
          while par[r1] != r1 {
            r1 = par[r1]
          }
          let mut r2 = b
          while par[r2] != r2 {
            r2 = par[r2]
          }
          if r1 != r2 {
            par[r2] = r1
          }
        }
      }
    }
  }
  let mut root = p
  while par[root] != root {
    root = par[root]
  }
  // 分量內最小點
  let mut m = root
  for q in 0..<s.top.npt {
    let mut r = q
    while par[r] != r {
      r = par[r]
    }
    if r == root && q < m {
      m = q
    }
  }
  m
}

///|
/// 有序 Čech 複形的第 n 階基（以分量為基）：每個 (元組, 交集的分量代表)。
fn b11_ordered_basis(
  s : B9Site,
  cv : B9Cover,
  n : Int32,
) -> Array[Array[Int32]] {
  let k = cv.fam.length()
  let total = b8_pow_int(k, n + 1)
  let out : Array[Array[Int32]] = []
  for code in 0..<total {
    let tup : Array[Int32] = []
    let mut c = code
    for _ in 0..<(n + 1) {
      tup.push(c % k)
      c = c / k
    }
    let pts = b11_tuple_pts_bool(s, cv, tup)
    // 拜訪所有分量代表（代表 = 某點 p 且其分量代表為自身）
    for p in 0..<s.top.npt {
      if pts[p] && b11_open_comp_of(s, pts, p) == p {
        let e : Array[Int32] = []
        for t in tup {
          e.push(t)
        }
        e.push(p)
        out.push(e)
      }
    }
  }
  out
}

///|
/// 去面：從元組刪去第 k 位。
fn b11_drop(tup : Array[Int32], k : Int32) -> Array[Int32] {
  let out : Array[Int32] = []
  for i in 0..<tup.length() {
    if i != k {
      out.push(tup[i])
    }
  }
  out
}

///|
/// 在基表中尋找 (元組, 點) 的索引；不存在回 -1。
fn b11_basis_find(
  basis : Array[Array[Int32]],
  tup : Array[Int32],
  p : Int32,
) -> Int32 {
  let l = tup.length()
  for c in 0..<basis.length() {
    let f = basis[c]
    if f.length() != l + 1 {
      continue
    }
    let mut same = true
    for i in 0..<l {
      if f[i] != tup[i] {
        same = false
      }
    }
    if f[l] != p {
      same = false
    }
    if same {
      return c
    }
  }
  -1
}

///|
/// 有序 Čech 上同調維數 H^n（含退化單形，模 p 高斯消去）。
/// 第 n 階基元素 = (長度 n+1 的索引元組, 交集中的點)。
pub fn b11_ordered_cech_h(cv : B9Cover, n : Int32, pm : Int32) -> Int32 {
  let s = cv.site
  let bn = b11_ordered_basis(s, cv, n)
  let bn1 = b11_ordered_basis(s, cv, n + 1)
  // d_n : C^n → C^{n+1}
  let rows : Array[Array[Int32]] = []
  for b in 0..<bn1.length() {
    let row : Array[Int32] = []
    for _ in 0..<bn.length() {
      row.push(0)
    }
    let e = bn1[b]
    let tup : Array[Int32] = []
    for i in 0..<(n + 2) {
      tup.push(e[i])
    }
    let p = e[n + 2]
    for k in 0..<=(n + 1) {
      let t2 = b11_drop(tup, k)
      let c = b11_basis_find(bn, t2, p)
      if c >= 0 {
        let sign = if k % 2 == 0 { 1 } else { pm - 1 }
        row[c] = (row[c] + sign) % pm
      }
    }
    rows.push(row)
  }
  let rank_n = b9_rank_mod(rows, bn.length(), pm)
  let mut rank_prev = 0
  if n > 0 {
    let bm = b11_ordered_basis(s, cv, n - 1)
    let rows2 : Array[Array[Int32]] = []
    for b in 0..<bn.length() {
      let row : Array[Int32] = []
      for _ in 0..<bm.length() {
        row.push(0)
      }
      let e = bn[b]
      let tup : Array[Int32] = []
      for i in 0..<(n + 1) {
        tup.push(e[i])
      }
      let p = e[n + 1]
      for k in 0..<=n {
        let t2 = b11_drop(tup, k)
        let c = b11_basis_find(bm, t2, p)
        if c >= 0 {
          let sign = if k % 2 == 0 { 1 } else { pm - 1 }
          row[c] = (row[c] + sign) % pm
        }
      }
      rows2.push(row)
    }
    rank_prev = b9_rank_mod(rows2, bm.length(), pm)
  }
  bn.length() - rank_n - rank_prev
}

///|
/// 退化映射 s_k：在第 k 位插入一個複本。
pub fn b11_degen(tup : Array[Int32], k : Int32) -> Array[Int32] {
  let out : Array[Int32] = []
  for i in 0..<tup.length() {
    if i == k {
      out.push(tup[k])
    }
    out.push(tup[i])
  }
  out
}

///|
/// 退化恆等式 s_i∘s_j = s_{j+1}∘s_i（i ≤ j）在全部 2-單形上逐對核對。
pub fn b11_degeneracy_ok(cv : B9Cover) -> Bool {
  let k = cv.fam.length()
  for a in 0..<k {
    for b in 0..<k {
      let t : Array[Int32] = [a, b]
      for i in 0..<=2 {
        for j in 0..<=2 {
          if i <= j {
            let lhs = b11_degen(b11_degen(t, j), i)
            let rhs = b11_degen(b11_degen(t, i), j + 1)
            if lhs.length() != rhs.length() {
              return false
            }
            for x in 0..<lhs.length() {
              if lhs[x] != rhs[x] {
                return false
              }
            }
          }
        }
      }
    }
  }
  true
}

///|
/// 神經的 π₀：Čech 群oid 的連通分量數（成員以非空交集相連）。
pub fn b11_groupoid_pi0(cv : B9Cover) -> Int32 {
  let k = cv.fam.length()
  let par : Array[Int32] = []
  for i in 0..<k {
    par.push(i)
  }
  for i in 0..<k {
    for j in 0..<k {
      if i < j && b9_cover_inter(cv, (1 << i) | (1 << j)) >= 0 {
        let mut r1 = i
        while par[r1] != r1 {
          r1 = par[r1]
        }
        let mut r2 = j
        while par[r2] != r2 {
          r2 = par[r2]
        }
        if r1 != r2 {
          par[r2] = r1
        }
      }
    }
  }
  let mut c = 0
  for i in 0..<k {
    if par[i] == i {
      c = c + 1
    }
  }
  c
}

// ───────────────────────── (∞,1)-幾何態射 ─────────────────────────

///|
/// (∞,1)-幾何態射的截斷檢定：在 2 項複形上核對伴隨
/// ∏_n |Hom(f_!A^n, B^n)| = ∏_n |Hom(A^n, f^*B^n)|。
pub fn b11_inf_adjunction(
  u : B8Fun,
  left : Array[B8PS],
  right : Array[B8PS],
) -> Bool {
  let mut lhs = 1
  let mut rhs = 1
  for n in 0..<left.length() {
    if n < right.length() {
      lhs = lhs * b8_nat_count(b8_lan(u, left[n]), right[n])
      rhs = rhs * b8_nat_count(left[n], b8_pull(u, right[n]))
    }
  }
  lhs == rhs
}

// ───────────────────────── 反常層 ─────────────────────────

///|
/// 子空間拓撲：以點集給出開集限制。
pub fn b11_subspace(t : B9Top, pts : Array[Bool]) -> B9Top {
  let idx : Array[Int32] = []
  let n : Int32 = b9_pop(pts)
  let out : Array[Array[Bool]] = []
  for i in 0..<t.opens.length() {
    let o : Array[Bool] = []
    for p in 0..<t.npt {
      if pts[p] {
        o.push(t.opens[i][p])
      }
    }
    out.push(o)
  }
  let _ = idx
  b9_top(n, out)
}

///|
/// 反常層（中中間偏差）：^p H^n = H^n(U) + H^{n−1}(Z)，U = X∖Z 為開、Z 為閉。
/// 回傳 (H^*(X), ^p H^*(X))。
pub fn b11_perverse_dims(
  s : B9Site,
  cv : B9Cover,
  z : Array[Bool],
  pmax : Int32,
  pm : Int32,
) -> (Array[Int32], Array[Int32]) {
  let t = s.top
  let hx = b11_ext_dims(cv, pmax, pm)
  // U = 補集
  let u_pts : Array[Bool] = []
  for p in 0..<t.npt {
    u_pts.push(!z[p])
  }
  let tu = b11_subspace(t, u_pts)
  let tz = b11_subspace(t, z)
  let hu = b11_site_dims(tu, pmax, pm)
  let hz = b11_site_dims(tz, pmax, pm)
  let per : Array[Int32] = []
  for n in 0..<=pmax {
    let mut v = hu[n]
    if n > 0 {
      v = v + hz[n - 1]
    }
    per.push(v)
  }
  (hx, per)
}

///|
/// 對一個有限空間（以其站）計算 H^*(; ℤ/p) 的維數表。
pub fn b11_site_dims(t : B9Top, pmax : Int32, pm : Int32) -> Array[Int32] {
  let s = b9_site(t)
  if s.cat.nob == 0 {
    let out : Array[Int32] = []
    for _ in 0..<=pmax {
      out.push(0)
    }
    return out
  }
  let top = s.cat.nob - 1
  let fam : Array[Int32] = []
  for v in 0..<s.cat.nob {
    if v != top && b9_site_inter(s, v, top) == v {
      fam.push(b9_site_incl(s, v, top))
    }
  }
  // 若未覆蓋則補 top
  let acc : Array[Bool] = []
  for _ in 0..<t.npt {
    acc.push(false)
  }
  for m in fam {
    let o = s.top.opens[s.opens[s.cat.dom[m]]]
    for p in 0..<t.npt {
      if o[p] {
        acc[p] = true
      }
    }
  }
  let base = s.top.opens[s.opens[top]]
  let mut cov = true
  for p in 0..<t.npt {
    if base[p] && !acc[p] {
      cov = false
    }
  }
  if !cov || fam.length() == 0 {
    fam.push(b9_site_incl(s, top, top))
  }
  let cv2 : B9Cover = { site: s, v: top, fam, }
  b11_ext_dims(cv2, pmax, pm)
}

// ───────────────────────── ℓ-進層 ─────────────────────────

///|
/// ℓ-進係數的貝蒂數獨立性：以兩個不同素數 ℓ₁, ℓ₂ 計算上同調維數並比對。
pub fn b11_ell_betti(
  cv : B9Cover,
  pmax : Int32,
  l1 : Int32,
  l2 : Int32,
) -> (Array[Int32], Array[Int32], Bool) {
  let a = b11_ext_dims(cv, pmax, l1)
  let b = b11_ext_dims(cv, pmax, l2)
  let mut eq = true
  for i in 0..<a.length() {
    if a[i] != b[i] {
      eq = false
    }
  }
  (a, b, eq)
}
