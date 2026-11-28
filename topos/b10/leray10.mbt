///|
/// leray10.mbt — 批次十·模組 1：高階直像層與勒雷譜序列
///
/// 對幾何態射 f : Y → pt（常數層係數 F_p）：
///   f_*F = Γ(Y, F)                      （第 0 直像 = 整體截面）
///   R^q f_* = H^q(Y, F)                 （高階直像 = 上同調，逐維度相等）
/// 並以 **Künneth 雙複形** 給出勒雷譜序列退化的精確實例：
///   E_2^{p,q} = H^p(C_1) ⊗ H^q(C_2)  ⇒  H^n(Tot) ，
/// 因係數在域 F_p 上，雙複形退化，故 dim H^n(Tot) = Σ_{p+q=n} dim E_2^{p,q}。
/// （Čech 上同調與導出函子上同調一致屬框架假設。）

// ───────────────────────── 直像 ─────────────────────────

///|
/// 常數層 F_p 在物件 U 上的截面數 = p^{π₀(U)}。
pub fn b10_sections_dim(s : B9Site, obj : Int32, pm : Int32) -> Int32 {
  b8_pow_int(pm, b9_comp_count(s, obj))
}

///|
/// f : Y → pt 的第 0 直像：單物件範疇上的預層，值 = 整體截面數。
pub fn b10_direct_image_pt(cv : B9Cover, pm : Int32) -> B8PS {
  let pt = b8_cat_disc(1)
  b8_ps_make(pt, [b10_sections_dim(cv.site, cv.v, pm)], [])
}

///|
/// 高階直像 R^q f_*(pt) 的維數 = H^q(Y, F_p)（以覆蓋族的 Čech 上同調計算）。
pub fn b10_higher_direct(cv : B9Cover, q : Int32, pm : Int32) -> Int32 {
  b9_cech_h(cv, q, pm)
}

///|
/// 高階直像的維數表 [dim R^0 f_*, dim R^1 f_*, …]。
pub fn b10_higher_direct_dims(
  cv : B9Cover,
  pmax : Int32,
  pm : Int32,
) -> Array[Int32] {
  let out : Array[Int32] = []
  for q in 0..<=pmax {
    out.push(b10_higher_direct(cv, q, pm))
  }
  out
}

///|
/// 纖維無環：H^q(f^{-1}(pt), F) = 0 對所有 q > 0。
pub fn b10_fiber_acyclic(cv : B9Cover, pmax : Int32, pm : Int32) -> Bool {
  for q in 1..<=pmax {
    if b10_higher_direct(cv, q, pm) != 0 {
      return false
    }
  }
  true
}

// ───────────────────────── 歐拉－龐加萊 ─────────────────────────

///|
/// Čech 複形的歐拉－龐加萊恆等式：Σ(−1)^p dim C^p = Σ(−1)^p dim H^p。
/// 回傳 (左側, 右側) 供比對。
pub fn b10_euler_poincare(
  cv : B9Cover,
  pmax : Int32,
  pm : Int32,
) -> (Int32, Int32) {
  let mut lhs = 0
  let mut rhs = 0
  for p in 0..<=pmax {
    let d = b9_cech_dim(cv, p)
    let h = b9_cech_h(cv, p, pm)
    if p % 2 == 0 {
      lhs = lhs + d
      rhs = rhs + h
    } else {
      lhs = lhs - d
      rhs = rhs - h
    }
  }
  (lhs, rhs)
}

// ───────────────────────── 覆蓋無關性 ─────────────────────────

///|
/// 由覆蓋族建構覆蓋。
pub fn b10_cover(s : B9Site, v : Int32, fam : Array[Int32]) -> B9Cover {
  { site: s, v, fam, }
}

///|
/// 兩個覆蓋給出相同的上同調維數（勒雷收斂的維度形式：E_∞ 與覆蓋選擇無關）。
/// 回傳 (覆蓋一, 覆蓋二) 的維數表。
pub fn b10_cover_independence(
  s : B9Site,
  v : Int32,
  fam1 : Array[Int32],
  fam2 : Array[Int32],
  pmax : Int32,
  pm : Int32,
) -> (Array[Int32], Array[Int32]) {
  let c1 = b10_cover(s, v, fam1)
  let c2 = b10_cover(s, v, fam2)
  (b10_higher_direct_dims(c1, pmax, pm), b10_higher_direct_dims(c2, pmax, pm))
}

// ───────────────────────── Künneth 雙複形 ─────────────────────────

///|
/// 某度數的微分矩陣（列 = 目標基，行 = 來源基）。
fn b10_diff_at(
  cv : B9Cover,
  p : Int32,
  pm : Int32,
) -> (Array[Array[Int32]], Int32) {
  if cv.fam.length() < p + 1 {
    return ([], 0)
  }
  let r = b9_cech_diff(cv, p, pm)
  (r.0, r.2)
}

///|
/// Künneth 雙複形：以兩個 Čech 複形的張量積構造 Tot^n = ⊕_{p+q=n} C₁^p ⊗ C₂^q，
/// 微分 d(x⊗y) = dx⊗y + (−1)^p x⊗dy，在 F_p 係數下計算
///   (a) Tot 的上同調維數表；(b) Künneth 預測值 Σ_{p+q=n} dim H^p(C₁)·dim H^q(C₂)。
pub fn b10_kunneth(
  cv1 : B9Cover,
  cv2 : B9Cover,
  pmax1 : Int32,
  pmax2 : Int32,
  pm : Int32,
) -> (Array[Int32], Array[Int32]) {
  // 各度數的維數與微分
  let dim1 : Array[Int32] = []
  let dim2 : Array[Int32] = []
  let d1 : Array[Array[Array[Int32]]] = []
  let d2 : Array[Array[Array[Int32]]] = []
  for p in 0..<=pmax1 {
    dim1.push(b9_cech_dim(cv1, p))
    let r = b10_diff_at(cv1, p, pm)
    d1.push(r.0)
  }
  for q in 0..<=pmax2 {
    dim2.push(b9_cech_dim(cv2, q))
    let r = b10_diff_at(cv2, q, pm)
    d2.push(r.0)
  }
  let deg = pmax1 + pmax2 + 1
  // 每個度數的區塊佈局：(p, offset)
  let blocks : Array[Array[(Int32, Int32)]] = []
  let totdim : Array[Int32] = []
  for n in 0..<deg {
    let bs : Array[(Int32, Int32)] = []
    let mut off = 0
    for p in 0..<=pmax1 {
      let q = n - p
      if q >= 0 && q <= pmax2 {
        bs.push((p, off))
        off = off + dim1[p] * dim2[q]
      }
    }
    blocks.push(bs)
    totdim.push(off)
  }
  // 總微分矩陣 T[n] : Tot^n → Tot^{n+1}
  let diffs : Array[Array[Array[Int32]]] = []
  for n in 0..<(deg - 1) {
    let rows : Array[Array[Int32]] = []
    for _ in 0..<totdim[n + 1] {
      let row : Array[Int32] = []
      for _ in 0..<totdim[n] {
        row.push(0)
      }
      rows.push(row)
    }
    for (p, offc) in blocks[n] {
      let q = n - p
      // 水平：d₁ ⊗ id，作用到 Tot^{n+1} 的 (p+1, q) 區塊
      if p + 1 <= pmax1 && d1[p].length() > 0 {
        let target_off = b10_block_off(blocks[n + 1], p + 1)
        if target_off >= 0 {
          for i2 in 0..<dim1[p + 1] {
            for i1 in 0..<dim1[p] {
              let coef = d1[p][i2][i1]
              if coef != 0 {
                for j in 0..<dim2[q] {
                  let src = offc + i1 * dim2[q] + j
                  let dst = target_off + i2 * dim2[q] + j
                  rows[dst][src] = coef
                }
              }
            }
          }
        }
      }
      // 垂直：(−1)^p id ⊗ d₂，作用到 Tot^{n+1} 的 (p, q+1) 區塊
      if q + 1 <= pmax2 && d2[q].length() > 0 {
        let target_off = b10_block_off(blocks[n + 1], p)
        if target_off >= 0 {
          let sign = if p % 2 == 0 { 1 } else { pm - 1 }
          for j2 in 0..<dim2[q + 1] {
            for j1 in 0..<dim2[q] {
              let coef = d2[q][j2][j1]
              if coef != 0 {
                for i in 0..<dim1[p] {
                  let src = offc + i * dim2[q] + j1
                  let dst = target_off + i * dim2[q + 1] + j2
                  rows[dst][src] = (rows[dst][src] + sign * coef) % pm
                }
              }
            }
          }
        }
      }
    }
    diffs.push(rows)
  }
  // Tot 的上同調維數
  let total_h : Array[Int32] = []
  for n in 0..<deg {
    let rk_up = if n < deg - 1 {
      b9_rank_mod(diffs[n], totdim[n], pm)
    } else {
      0
    }
    let rk_down = if n == 0 {
      0
    } else {
      b9_rank_mod(diffs[n - 1], totdim[n - 1], pm)
    }
    total_h.push(totdim[n] - rk_up - rk_down)
  }
  // Künneth 預測
  let pred : Array[Int32] = []
  for n in 0..<deg {
    let mut s = 0
    for p in 0..<=pmax1 {
      let q = n - p
      if q >= 0 && q <= pmax2 {
        s = s + b9_cech_h(cv1, p, pm) * b9_cech_h(cv2, q, pm)
      }
    }
    pred.push(s)
  }
  (total_h, pred)
}

///|
/// 在區塊佈局中查度數 p 的起始偏移；不存在回 -1。
fn b10_block_off(bs : Array[(Int32, Int32)], p : Int32) -> Int32 {
  for (pp, off) in bs {
    if pp == p {
      return off
    }
  }
  -1
}

///|
/// 譜序列退化檢定：Tot 的維數表與 Künneth 預測逐度數相等。
pub fn b10_kunneth_ok(
  cv1 : B9Cover,
  cv2 : B9Cover,
  pmax1 : Int32,
  pmax2 : Int32,
  pm : Int32,
) -> Bool {
  let (a, b) = b10_kunneth(cv1, cv2, pmax1, pmax2, pm)
  let mut ok = a.length() == b.length()
  for i in 0..<a.length() {
    if a[i] != b[i] {
      ok = false
    }
  }
  ok
}
