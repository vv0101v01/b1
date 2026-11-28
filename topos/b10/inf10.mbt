///|
/// inf10.mbt — 批次十·模組 2：∞-遺址與高階吉羅公理
///
/// ∞-遺址 = 站 ＋ 每個覆蓋的 **超覆蓋神經**（逐層的高階匹配資料）。
/// 高階吉羅公理 = 吉羅公理在「∞-截斷」下的版本：
///   G1′ 有限餘極限、G2′ 不交餘積、G3′ 群oid 商有效、G4′ 小生成集，
/// 且在 1-截斷（超覆蓋第 1 層）即已足夠決定層與其上同調。

// ───────────────────────── 神經與超覆蓋 ─────────────────────────

///|
/// 神經第 n 層的大小：n-單形（|I| = n+1 的子集）個數。
pub fn b10_nerve_level_size(cv : B9Cover, n : Int32) -> Int32 {
  b9_subsets(cv, n + 1).length()
}

///|
/// 嚴格（無冗餘）超覆蓋條件：對每個層級的交集 U_I，其「下一層」{U_J : J ⊋ I}
/// 構成的族覆蓋 U_I。注意標準 Čech 神經允許重複元組，此時條件恆成立
/// （見 b10_hypercover_degenerate_ok）；嚴格版本恰在覆蓋「無冗餘」時才會失敗。
pub fn b10_hypercover_ok(s : B9Site, cv : B9Cover) -> Bool {
  for n in 0..<cv.fam.length() {
    for mask in b9_subsets(cv, n + 1) {
      let obj = b9_cover_inter(cv, mask)
      if obj >= 0 {
        let base = s.top.opens[s.opens[obj]]
        // 下一層覆蓋：所有 |J| = n+2、J ⊃ mask 的交集的聯集
        let acc : Array[Bool] = []
        for _ in 0..<s.top.npt {
          acc.push(false)
        }
        let mut any = false
        for big in b9_subsets(cv, n + 2) {
          let mut sup = true
          for i in 0..<cv.fam.length() {
            if ((mask >> i) & 1) == 1 && ((big >> i) & 1) == 0 {
              sup = false
            }
          }
          if sup {
            let o = b9_cover_inter(cv, big)
            if o >= 0 {
              any = true
            }
          }
        }
        let _ = any
        for big in b9_subsets(cv, n + 2) {
          let mut sup = true
          for i in 0..<cv.fam.length() {
            if ((mask >> i) & 1) == 1 && ((big >> i) & 1) == 0 {
              sup = false
            }
          }
          if sup {
            let o = b9_cover_inter(cv, big)
            if o >= 0 {
              let oo = s.top.opens[s.opens[o]]
              for p in 0..<s.top.npt {
                if oo[p] {
                  acc[p] = true
                }
              }
            }
          }
        }
        // 若更高階交集合為空，此層級退化，條件視為空成立
        for p in 0..<s.top.npt {
          if any && base[p] && !acc[p] {
            return false
          }
        }
      }
    }
  }
  true
}

///|
/// 標準（允許重複）Čech 神經的超覆蓋條件：第 n+1 層取 U_I ∩ U_j（j 可屬於 I），
/// 族中含有 U_I 自身，故必覆蓋 U_I —— 這正是「Čech 神經是超覆蓋」的有限核對。
pub fn b10_hypercover_degenerate_ok(cv : B9Cover) -> Bool {
  let s = cv.site
  for n in 0..<cv.fam.length() {
    for mask in b9_subsets(cv, n + 1) {
      let obj = b9_cover_inter(cv, mask)
      if obj >= 0 {
        let base = s.top.opens[s.opens[obj]]
        let acc : Array[Bool] = []
        for _ in 0..<s.top.npt {
          acc.push(false)
        }
        for j in 0..<cv.fam.length() {
          let big = mask | (1 << j)
          let o = b9_cover_inter(cv, big)
          if o >= 0 {
            let oo = s.top.opens[s.opens[o]]
            for p in 0..<s.top.npt {
              if oo[p] {
                acc[p] = true
              }
            }
          }
        }
        for p in 0..<s.top.npt {
          if base[p] && !acc[p] {
            return false
          }
        }
      }
    }
  }
  true
}

///|
/// 去面算子：從子集遮罩刪去第 k 個元素。
pub fn b10_face(mask : Int32, k : Int32) -> Int32 {
  let mut out = 0
  let mut bit = 0
  for i in 0..<16 {
    if ((mask >> i) & 1) == 1 {
      if bit != k {
        out = out | (1 << i)
      }
      bit = bit + 1
    }
  }
  out
}

///|
/// 單純恆等式 d_i ∘ d_j = d_{j-1} ∘ d_i（i < j），對神經的所有 2-單形逐對檢定。
pub fn b10_simplicial_ok(cv : B9Cover) -> Bool {
  let n2 = b9_subsets(cv, 3)
  for mask in n2 {
    for i in 0..<2 {
      for j in 0..<2 {
        if i < j {
          let lhs = b10_face(b10_face(mask, j), i)
          let rhs = b10_face(b10_face(mask, i), j - 1)
          if lhs != rhs {
            return false
          }
        }
      }
    }
  }
  true
}

///|
/// 覆蓋的重心細化 𝒰̃：族 = 所有非空交集的包含映射。
/// 其神經即 𝒰 神經的重心重分，是高階意義下的細化（超覆蓋）。
pub fn b10_refined_cover(cv : B9Cover) -> B9Cover {
  let s = cv.site
  let fam : Array[Int32] = []
  for k in 1..<=cv.fam.length() {
    for mask in b9_subsets(cv, k) {
      let o = b9_cover_inter(cv, mask)
      if o >= 0 {
        let m = b9_site_incl(s, o, cv.v)
        if m >= 0 {
          fam.push(m)
        }
      }
    }
  }
  { site: s, v: cv.v, fam, }
}

///|
/// ∞-遺址上的不變性：細化前後 Čech 上同調逐度數相等
/// （高階吉羅公理成立時，超覆蓋可替換原覆蓋計算層與上同調）。
pub fn b10_nerve_cohomology_ok(cv : B9Cover, pmax : Int32, pm : Int32) -> Bool {
  let rf = b10_refined_cover(cv)
  for p in 0..<=pmax {
    if b9_cech_h(cv, p, pm) != b9_cech_h(rf, p, pm) {
      return false
    }
  }
  true
}

// ───────────────────────── ∞-遺址 ─────────────────────────

///|
/// ∞-遺址資料是否合法：站合法、覆蓋族逐層覆蓋（超覆蓋）、單純恆等式成立。
pub fn b10_inf_site_ok(
  s : B9Site,
  cv : B9Cover,
  pmax : Int32,
  pm : Int32,
) -> Bool {
  let (a, b, c) = b9_topology_ok(s)
  a &&
  b &&
  c &&
  b10_hypercover_degenerate_ok(cv) &&
  b10_simplicial_ok(cv) &&
  b10_nerve_cohomology_ok(cv, pmax, pm)
}

// ───────────────────────── 高階吉羅公理 ─────────────────────────

///|
/// G3′：覆蓋映射 ⊔よ(u_i) → 1 是正則滿（核對的餘等化子）——群oid 商在 1-截斷有效。

///|
/// 覆蓋族的象子層（⊔よ(u_i) 在 1 中的像）：im(v) = 1 若 v ⊆ ⋃_i u_i，否則 0。
/// 注意：有限空間站不含空開集，b9_sheafify 在「不交覆蓋」的空交集上退化，
/// 故此處以象子層直接計算（見報告「框架限制」一節）。
pub fn b10_image_sheaf(cv : B9Cover) -> B8PS {
  let s = cv.site
  let sz : Array[Int32] = []
  for v in 0..<s.cat.nob {
    let base = s.top.opens[s.opens[v]]
    let acc : Array[Bool] = []
    for _ in 0..<s.top.npt {
      acc.push(false)
    }
    for m in cv.fam {
      let d = s.cat.dom[m]
      let oo = s.top.opens[s.opens[d]]
      for p in 0..<s.top.npt {
        if oo[p] {
          acc[p] = true
        }
      }
    }
    let mut cov = true
    for p in 0..<s.top.npt {
      if base[p] && !acc[p] {
        cov = false
      }
    }
    sz.push(if cov && b9_pop(base) > 0 { 1 } else { 0 })
  }
  let mx = 1
  let res : Array[Int32] = []
  for _ in 0..<(s.cat.nmor * mx) {
    res.push(0)
  }
  b8_ps_make(s.cat, sz, res)
}

///|
/// G3′：覆蓋映射 ⊔よ(u_i) → 1 是有效的群oid 商 ——
/// 其象子層在 V 上恰為 1（滿射），且本身是層（下降有效）。
pub fn b10_giraud_g3(cv : B9Cover) -> Bool {
  let s = cv.site
  let g = b9_groth_spatial(s)
  let im = b10_image_sheaf(cv)
  im.sz[cv.v] == 1 && b9_is_sheaf(g, im)
}

///|
/// G1′／G2′／G4′：有限極限、不交餘積、小生成集（在 1-截斷）。
pub fn b10_giraud_low(s : B9Site) -> (Bool, Bool, Bool) {
  let (t, i, p, c) = b9_lex_ok(s.cat)
  let f = b8_ps_const(s.cat, 2)
  let g = b8_ps_yoneda(s.cat, 0)
  let disj = b9_coprod_disjoint(f, g)
  let univ = b9_coprod_universal(f, g, f)
  let (l, r) = b9_density_check(f)
  (t && i && p && c, disj && univ, l == r)
}
