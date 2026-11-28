///|
/// stalk9.mbt — 批次九·模組 3：柄（stalk）、芽（germ）、點與「足夠多點」
///
/// 點 p ∈ X 給出鄰域濾過系統 { U ∋ p }（向下包含），柄為餘極限
///     F_p = colim_{U ∋ p} F(U).
/// 有限模型中：元素 = 對 (U, x), p ∈ U；等價 (U,x) ~ (V,y) ⟺ F(U∩V)(x) = F(U∩V)(y)
/// （U∩V 仍含 p 且非空，故為合法鄰域）。以併查集求商。
///
/// 芽：F(U) → F_p，x ↦ [(U,x)]。
/// 點 = 幾何態射 Set → Sh(X)：x* = 柄函子（左正伴隨），x_* = 摩天樓層（右伴隨）。
/// 「足夠多點」= 柄函子聯合忠實：層的態射相同 ⟺ 在所有柄上相同 ⟺ 截面由芽決定。

// ───────────────────────── 柄 ─────────────────────────

///|
/// 柄的類編號：回傳 (柄的元素個數, 以 obj*mx+x 索引的類編號表（-1 表示該物件不含 p）)。
pub fn b9_stalk(f : B8PS, s : B9Site, p : Int32) -> (Int32, Array[Int32]) {
  let n = s.cat.nob
  let mx = f.mx
  let total = n * mx
  let par : Array[Int32] = []
  let has : Array[Bool] = []
  for i in 0..<total {
    par.push(i)
    let obj = i / mx
    let x = i % mx
    has.push(x < f.sz[obj] && s.top.opens[s.opens[obj]][p])
  }
  for i in 0..<total {
    if has[i] {
      let u = i / mx
      let x = i % mx
      for j in 0..<total {
        if has[j] {
          let v = j / mx
          let y = j % mx
          let w = b9_site_inter(s, u, v)
          if w >= 0 {
            let m1 = b9_site_incl(s, w, u)
            let m2 = b9_site_incl(s, w, v)
            if f.res[m1 * mx + x] == f.res[m2 * mx + y] {
              // 併查集合併
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
      }
    }
  }
  let cls : Array[Int32] = []
  for _ in 0..<total {
    cls.push(-1)
  }
  let mut cnt = 0
  for i in 0..<total {
    if has[i] {
      let mut r = i
      while par[r] != r {
        r = par[r]
      }
      if cls[r] < 0 {
        cls[r] = cnt
        cnt = cnt + 1
      }
      cls[i] = cls[r]
    }
  }
  (cnt, cls)
}

///|
/// 柄的元素個數。
pub fn b9_stalk_count(f : B8PS, s : B9Site, p : Int32) -> Int32 {
  let (k, _) = b9_stalk(f, s, p)
  k
}

///|
/// 全部點的柄大小。
pub fn b9_stalk_all(f : B8PS, s : B9Site) -> Array[Int32] {
  let out : Array[Int32] = []
  for p in 0..<s.top.npt {
    out.push(b9_stalk_count(f, s, p))
  }
  out
}

///|
/// 截面由芽決定（分離性）：對層 F 的任一開集 U 上兩個相異截面，存在 p ∈ U 使芽不同。
pub fn b9_points_separate_sections(s : B9Site, f : B8PS) -> Bool {
  let mx = f.mx
  for u in 0..<s.cat.nob {
    for x in 0..<f.sz[u] {
      for y in 0..<f.sz[u] {
        if x != y {
          let mut sep = false
          for p in 0..<s.top.npt {
            if s.top.opens[s.opens[u]][p] {
              let (_k, cls) = b9_stalk(f, s, p)
              if cls[u * mx + x] != cls[u * mx + y] {
                sep = true
              }
            }
          }
          if !sep {
            return false
          }
        }
      }
    }
  }
  true
}

// ───────────────────────── 點的幾何態射 ─────────────────────────

///|
/// 摩天樓層 x_*(S)：含 p 的開集取 S，其餘取單點；限制映射相應為恆等或唯一映射。
pub fn b9_skyscraper(s : B9Site, p : Int32, n : Int32) -> B8PS {
  let sz : Array[Int32] = []
  for u in 0..<s.cat.nob {
    if s.top.opens[s.opens[u]][p] {
      sz.push(n)
    } else {
      sz.push(1)
    }
  }
  let mx = if n < 1 { 1 } else { n }
  let res : Array[Int32] = []
  for _ in 0..<(s.cat.nmor * mx) {
    res.push(0)
  }
  for m in 0..<s.cat.nmor {
    let d = s.cat.dom[m]
    let c = s.cat.cod[m]
    let hp = s.top.opens[s.opens[c]][p]
    for j in 0..<mx {
      if hp && s.top.opens[s.opens[d]][p] {
        res[m * mx + j] = if j < n { j } else { 0 }
      } else {
        res[m * mx + j] = 0
      }
    }
  }
  b8_ps_make(s.cat, sz, res)
}

///|
/// 點伴隨的計數核對：對層 F 與集合 S（|S| = n），
///     |Hom_Set(F_p, S)| = n^{|F_p|} = |Nat(F, x_*S)|。
pub fn b9_point_adjunction(
  s : B9Site,
  f : B8PS,
  p : Int32,
  n : Int32,
) -> (Int32, Int32) {
  let k = b9_stalk_count(f, s, p)
  let lhs = b8_pow_int(n, k)
  let rhs = b8_nat_count(f, b9_skyscraper(s, p, n))
  (lhs, rhs)
}

///|
/// 空間的點是否被柄區分（T0 判準的可計算版本）：不同點在某个預層上給出不同柄大小。
pub fn b9_points_distinguished(s : B9Site) -> Bool {
  let mut ok = true
  for p in 0..<s.top.npt {
    for q in 0..<s.top.npt {
      if p != q {
        // 存在可表預層使柄大小不同 ⟺ 存在開集含 p 不含 q 或反之
        let mut sep = false
        for u in 0..<s.cat.nob {
          let ap = s.top.opens[s.opens[u]][p]
          let aq = s.top.opens[s.opens[u]][q]
          if ap != aq {
            sep = true
          }
        }
        if !sep {
          ok = false
        }
      }
    }
  }
  ok
}

///|
/// 層化後的截面數與「相容芽族」數的比較：
/// a(F)(U) 的元素個數應等於「在所有 p ∈ U 上給定芽、且局部相容」的族個數。
/// 在有限空間上，局部相容等價於：存在某個細覆蓋上的相容族（由構造 a 給出），
/// 這裡改以「芽組成的族若來自共同細化則相同」計數 —— 直接核對 a(F)(U) = |F⁺⁺(U)| 與柄的關係：
/// 若 x ≠ y 在 a(F)(U) 中，則存在 p 使兩者芽不同（a(F) 為層）。
pub fn b9_sheafify_pointwise(s : B9Site, g : B9Groth, f : B8PS) -> Bool {
  let a = b9_sheafify(g, f)
  b9_points_separate_sections(s, a)
}
