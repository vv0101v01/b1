///|
/// cohom9.mbt — 批次九·模組 7：層上同調（sheaf cohomology）
///
/// 係數取常數層 F_p（p 質數）：A(V) = F_p^{π0(V)}，限制映射由連通分量誘導。
/// 對覆蓋族 {U_i} 的 Čech 複形
///     C^p = ⊕_{|I| = p+1} A(U_I),   (d x)_{I∖{j}} = (−1)^j x_I|_{U_I},
/// 在 F_p 上以高斯消去算秩，得 dim H^p = dim ker d^p − rank d^{p−1}。
///
/// 另一支：群上同調 H^n(G; F_p) 以非齊次標準複形計算：
///     (∂f)(g_1..g_{n+1}) = f(g_2..) + Σ_{i=1}^{n} (−1)^i f(.., g_i g_{i+1}, ..) + (−1)^{n+1} f(.., g_n)

// ───────────────────────── mod p 線性代數 ─────────────────────────

///|
/// 模 p 逆元。
pub fn b9_modinv(a : Int32, p : Int32) -> Int32 {
  // 費馬小定理：a^(p−2) ≡ a⁻¹ (mod p)，p 為質數且 a ≢ 0
  let mut r = 1
  for _ in 0..<(p - 2) {
    r = r * a % p
  }
  r
}

///|
/// 矩陣（列優先）模 p 的秩。
pub fn b9_rank_mod(rows : Array[Array[Int32]], nm : Int32, p : Int32) -> Int32 {
  let nr = rows.length()
  if nr == 0 || nm == 0 {
    return 0
  }
  let m : Array[Array[Int32]] = []
  for i in 0..<nr {
    let row : Array[Int32] = []
    for j in 0..<nm {
      row.push((rows[i][j] % p + p) % p)
    }
    m.push(row)
  }
  let mut rank = 0
  let mut col = 0
  while col < nm && rank < nr {
    let mut piv = -1
    for i in rank..<nr {
      if m[i][col] != 0 && piv < 0 {
        piv = i
      }
    }
    if piv < 0 {
      col = col + 1
    } else {
      let tmp = m[rank]
      m[rank] = m[piv]
      m[piv] = tmp
      let inv = b9_modinv(m[rank][col], p)
      for j in 0..<nm {
        m[rank][j] = m[rank][j] * inv % p
      }
      for i in 0..<nr {
        if i != rank && m[i][col] != 0 {
          let f = m[i][col]
          for j in 0..<nm {
            m[i][j] = ((m[i][j] - f * m[rank][j]) % p + p) % p
          }
        }
      }
      rank = rank + 1
      col = col + 1
    }
  }
  rank
}

// ───────────────────────── 常數層與連通分量 ─────────────────────────

///|
/// 站物件上的連通分量編號：p ~ q 若 p ∈ cl(q) 或 q ∈ cl(p)（專化關係的生成等價）。
pub fn b9_components(s : B9Site, obj : Int32) -> Array[Int32] {
  let npt = s.top.npt
  let u = s.top.opens[s.opens[obj]]
  let par : Array[Int32] = []
  for p in 0..<npt {
    par.push(p)
  }
  // p ⤳ q ：q 的每個鄰域都含 p ⟺ 所有含 q 的開集都含 p
  for p in 0..<npt {
    for q in 0..<npt {
      if u[p] && u[q] {
        let mut spec = true
        for w in 0..<s.cat.nob {
          let ow = s.top.opens[s.opens[w]]
          if ow[q] && !ow[p] {
            spec = false
          }
        }
        if spec {
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
  let out : Array[Int32] = []
  for _ in 0..<npt {
    out.push(-1)
  }
  let mut cnt = 0
  for p in 0..<npt {
    let mut r = p
    while par[r] != r {
      r = par[r]
    }
    if u[p] {
      if out[r] < 0 {
        out[r] = cnt
        cnt = cnt + 1
      }
      out[p] = out[r]
    }
  }
  out
}

///|
/// 站物件的連通分量個數。
pub fn b9_comp_count(s : B9Site, obj : Int32) -> Int32 {
  let ids = b9_components(s, obj)
  let mut c = 0
  let seen : Array[Bool] = []
  for _ in 0..<s.top.npt {
    seen.push(false)
  }
  for p in 0..<s.top.npt {
    if ids[p] >= 0 && !seen[ids[p]] {
      seen[ids[p]] = true
      c = c + 1
    }
  }
  c
}

// ───────────────────────── Čech 複形 ─────────────────────────

///|
/// 覆蓋：站物件 v 的一族態射（各成員的定義域構成覆蓋）。
pub(all) struct B9Cover {
  site : B9Site
  v : Int32
  fam : Array[Int32]
}

///|
/// 子集 I（位元遮罩）對應的交集物件；空交集回 -1（其 A 為 0 維）。
pub fn b9_cover_inter(cv : B9Cover, mask : Int32) -> Int32 {
  let s = cv.site
  let mut cur = -1
  for i in 0..<cv.fam.length() {
    if ((mask >> i) & 1) == 1 {
      let d = s.cat.dom[cv.fam[i]]
      if cur < 0 {
        cur = d
      } else {
        cur = b9_site_inter(s, cur, d)
        if cur < 0 {
          return -1
        }
      }
    }
  }
  cur
}

///|
/// 全部大小為 k 的子集遮罩。
pub fn b9_subsets(cv : B9Cover, k : Int32) -> Array[Int32] {
  let out : Array[Int32] = []
  let n = cv.fam.length()
  let total = 1 << n
  for mask in 0..<total {
    let mut c = 0
    for i in 0..<n {
      if ((mask >> i) & 1) == 1 {
        c = c + 1
      }
    }
    if c == k {
      out.push(mask)
    }
  }
  out
}

///|
/// C^p 的維度。
pub fn b9_cech_dim(cv : B9Cover, p : Int32) -> Int32 {
  let mut d = 0
  for mask in b9_subsets(cv, p + 1) {
    let obj = b9_cover_inter(cv, mask)
    if obj >= 0 {
      d = d + b9_comp_count(cv.site, obj)
    }
  }
  d
}

///|
/// d^p : C^p → C^{p+1} 的矩陣（列 = C^{p+1} 的基，行 = C^p 的基），係數在 F_p。
pub fn b9_cech_diff(
  cv : B9Cover,
  p : Int32,
  pm : Int32,
) -> (Array[Array[Int32]], Int32, Int32) {
  let s = cv.site
  let src = b9_subsets(cv, p + 1)
  let dst = b9_subsets(cv, p + 2)
  // 索引：每個子集的起始偏移
  let src_off : Array[Int32] = []
  let mut acc = 0
  for mask in src {
    src_off.push(acc)
    let obj = b9_cover_inter(cv, mask)
    if obj >= 0 {
      acc = acc + b9_comp_count(s, obj)
    }
  }
  let dst_off : Array[Int32] = []
  let mut acc2 = 0
  for mask in dst {
    dst_off.push(acc2)
    let obj = b9_cover_inter(cv, mask)
    if obj >= 0 {
      acc2 = acc2 + b9_comp_count(s, obj)
    }
  }
  let rows : Array[Array[Int32]] = []
  for _ in 0..<acc2 {
    let row : Array[Int32] = []
    for _ in 0..<acc {
      row.push(0)
    }
    rows.push(row)
  }
  // 列 = |J| = p+2 的子集（C^{p+1} 的基），行 = |I| = p+1 的子集（C^p 的基）
  // (d x)_J = Σ_{i ∈ J} (−1)^{pos(i)} x_{J∖{i}}|_{U_J}
  for t in 0..<dst.length() {
    let big = dst[t]
    let obj_big = b9_cover_inter(cv, big)
    if obj_big >= 0 {
      let nb = b9_comp_count(s, obj_big)
      let cbig = b9_components(s, obj_big)
      for j in 0..<cv.fam.length() {
        if ((big >> j) & 1) == 1 {
          let small = big ^ (1 << j)
          let mut pos = -1
          for u in 0..<src.length() {
            if src[u] == small {
              pos = u
            }
          }
          if pos >= 0 {
            let obj_small = b9_cover_inter(cv, small)
            if obj_small >= 0 {
              // 位置編號：J 中小於 j 的元素個數
              let mut idxj = 0
              for q in 0..<j {
                if ((big >> q) & 1) == 1 {
                  idxj = idxj + 1
                }
              }
              let sign = if idxj % 2 == 0 { 1 } else { pm - 1 }
              let csmall = b9_components(s, obj_small)
              let row = rows[dst_off[t] + 0]
              let _ = row
              for c in 0..<nb {
                let mut target = -1
                for q in 0..<s.top.npt {
                  if cbig[q] == c {
                    target = csmall[q]
                  }
                }
                if target >= 0 {
                  let rr = dst_off[t] + c
                  let cc = src_off[pos] + target
                  let rw = rows[rr]
                  rw[cc] = (rw[cc] + sign) % pm
                }
              }
            }
          }
        }
      }
    }
  }
  (rows, acc2, acc)
}

///|
/// Čech 上同調維度 dim H^p（p = 0, 1, 2）。
pub fn b9_cech_h(cv : B9Cover, p : Int32, pm : Int32) -> Int32 {
  let (d_p, nrows_p, ncols_p) = b9_cech_diff(cv, p, pm)
  let rank_p = b9_rank_mod(d_p, ncols_p, pm)
  let mut rank_prev = 0
  if p > 0 {
    let (d_prev, _a, ncols_prev) = b9_cech_diff(cv, p - 1, pm)
    rank_prev = b9_rank_mod(d_prev, ncols_prev, pm)
  }
  let _ = nrows_p
  let cyc = ncols_p - rank_p
  cyc - rank_prev
}

///|
/// Čech 歐拉特徵 Σ(−1)^p dim H^p。
pub fn b9_cech_euler(cv : B9Cover, maxp : Int32, pm : Int32) -> Int32 {
  let mut e = 0
  for p in 0..<(maxp + 1) {
    let h = b9_cech_h(cv, p, pm)
    if p % 2 == 0 {
      e = e + h
    } else {
      e = e - h
    }
  }
  e
}

// ───────────────────────── 群上同調 ─────────────────────────

///|
/// 非齊次標準複形的 d^n : C^n → C^{n+1}（係數為平凡作用的 F_p）。
/// C^n 的基 = G^n 的元組（字典序編號）。
pub fn b9_bar_diff(
  g : B9Group,
  n : Int32,
  pm : Int32,
) -> (Array[Array[Int32]], Int32, Int32) {
  let k = g.k
  let dimsrc = b8_pow_int(k, n)
  let dimdst = b8_pow_int(k, n + 1)
  let rows : Array[Array[Int32]] = []
  for _ in 0..<dimdst {
    let row : Array[Int32] = []
    for _ in 0..<dimsrc {
      row.push(0)
    }
    rows.push(row)
  }
  // 列 = C^{n+1} 的基（長度 n+1 的元組），行 = C^n 的基（長度 n 的元組）
  for fcode in 0..<dimdst {
    let full : Array[Int32] = []
    let mut rem = fcode
    for _ in 0..<(n + 1) {
      full.push(rem % k)
      rem = rem / k
    }
    let row = rows[fcode]
    // 項 0：f(g_2..g_{n+1})
    let t0 : Array[Int32] = []
    for i in 1..<(n + 1) {
      t0.push(full[i])
    }
    let c0 = b9_tuple_code(t0, k)
    row[c0] = (row[c0] + 1) % pm
    // 項 i（1 ≤ i ≤ n）：f(.., g_i g_{i+1}, ..)，符號 (−1)^i
    for i in 1..<(n + 1) {
      let t : Array[Int32] = []
      for idx in 0..<(n + 1) {
        if idx == i - 1 {
          t.push(g.mul[full[i - 1] * k + full[i]])
        } else if idx == i {
          let _ = 0
        } else {
          t.push(full[idx])
        }
      }
      let ci = b9_tuple_code(t, k)
      let sign = if i % 2 == 0 { 1 } else { pm - 1 }
      row[ci] = (row[ci] + sign) % pm
    }
    // 末項 (−1)^{n+1} f(g_1..g_n)
    let tn : Array[Int32] = []
    for i in 0..<n {
      tn.push(full[i])
    }
    let cn = b9_tuple_code(tn, k)
    let sign2 = if (n + 1) % 2 == 0 { 1 } else { pm - 1 }
    row[cn] = (row[cn] + sign2) % pm
  }
  (rows, dimdst, dimsrc)
}

///|
/// 元組 → 編碼（digits[0] 為最低位）。
pub fn b9_tuple_code(t : Array[Int32], k : Int32) -> Int32 {
  let mut c = 0
  let mut pw = 1
  for i in 0..<t.length() {
    c = c + t[i] * pw
    pw = pw * k
  }
  c
}

///|
/// H^n(G; F_p) 的維度。
pub fn b9_group_h(g : B9Group, n : Int32, pm : Int32) -> Int32 {
  let (d_n, _a, ncols) = b9_bar_diff(g, n, pm)
  let rank_n = b9_rank_mod(d_n, ncols, pm)
  let mut rank_prev = 0
  if n > 0 {
    let (d_p, _b, ncols_p) = b9_bar_diff(g, n - 1, pm)
    rank_prev = b9_rank_mod(d_p, ncols_p, pm)
  }
  ncols - rank_n - rank_prev
}

///|
/// |Hom(G, F_p)|：群同態個數（用於 H^1 的獨立核對）。
pub fn b9_hom_to_fp(g : B9Group, pm : Int32) -> Int32 {
  let cur : Array[Int32] = []
  for _ in 0..<g.k {
    cur.push(0)
  }
  let mut cnt = 0
  let mut done = false
  while !done {
    let mut ok = cur[0] == 0
    for a in 0..<g.k {
      for b in 0..<g.k {
        if cur[g.mul[a * g.k + b]] != (cur[a] + cur[b]) % pm {
          ok = false
        }
      }
    }
    if ok {
      cnt = cnt + 1
    }
    let mut t = 0
    let mut carry = true
    while carry && t < g.k {
      cur[t] = cur[t] + 1
      if cur[t] >= pm {
        cur[t] = 0
        t = t + 1
      } else {
        carry = false
      }
    }
    if carry {
      done = true
    }
  }
  cnt
}
