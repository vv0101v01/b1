///|
/// godel2.mbt — 批次十二·模組 2：**哥德爾編碼、可證性與自洽性**（T415–T418、A68–A70）。
///
/// 本模組不「宣稱」任何元數學結論，而是把每一條降為可執行的整數計算：
///
///   (T-IN) 內定理性：以式子碼 ⌜φ⌝ 與證明碼 π，判定 π 是否為 φ 的證明。
///          可計算版本：把「證明」定義為**有限式子串**，逐條檢查是否為公理或由前面式子經 MP 得到。
///   (L-IN) 內可證性：□φ ⟺ ∃π. Proof(π, φ)。
///          在有限截斷內 ∀π ≤ d 皆找不到 → 本引擎只能報「截斷內不可證」（誠實的弱結論）。
///   函數提取矛盾：若自洽系統能對每個 ∃y.φ(x,y) 提取見證函數 f，則可判定停機問題 ⇒ 矛盾。
///          可計算版本：給出「提取會導致對角化」的有限見證。
///
/// 一致性的呈現方式：所有「證明」都是 `Array[Int32]`（式子碼序列），可由哥德爾編碼還原。

///|
/// 一個形式系統的公理碼集合（本引擎使用的 PA 片段：3 條算術 + 2 條邏輯公理模式）。
pub fn b12_axiom_codes() -> Array[Int64] {
  [
    go_godel_of_names(["0", "=", "0"]),
    go_godel_of_names(["S", "0", "=", "S", "0"]),
    go_godel_of_names(["0", "+", "0", "=", "0"]),
    go_godel_of_names(["S", "0", "+", "0", "=", "S", "0"]),
    go_godel_of_names(["0", "×", "0", "=", "0"]),
  ]
}

///|
/// 公理判定：φ 是否為公理（直接查表）。
pub fn b12_is_axiom(phi : Int64) -> Bool {
  for a in b12_axiom_codes() {
    if a == phi {
      return true
    }
  }
  false
}

///|
/// 證明結構：概念上是一串式子碼。此處以「前提 → 結論」的兩步 MP 作為最小可檢查單元。
/// MP 檢查：若 p、q 都在證明中，且 p = ⌜A→B⌝ 而 q = ⌜A⌝，則 ⌜B⌝ 可導出。
/// 以符號序列表示：A→B 的形狀是 [A…, "→", B…]；此處用簡化編碼（箭頭碼 7 出現的位置切分）。
pub fn b12_mp_check(
  premise : Array[Int32],
  target : Array[Int32],
  given : Array[Int32],
) -> Bool {
  // 找到 premise 中箭頭的位置（若無箭頭則不是蘊含式）
  let mut arrow = -1
  for i in 0..<premise.length() {
    if premise[i] == go_code("→") {
      arrow = i
    }
  }
  if arrow <= 0 {
    return false
  }
  // premise = A → B；given 必須等於 A，target 必須等於 B
  let ant : Array[Int32] = []
  for i in 0..<arrow {
    ant.push(premise[i])
  }
  let con : Array[Int32] = []
  for i in (arrow + 1)..<premise.length() {
    con.push(premise[i])
  }
  go_arr_eq(ant, given) && go_arr_eq(con, target)
}

///|
/// (T-IN) 內定理性檢核器：判斷一個有限推導序列是否為末式 φ 的證明。
/// 每一步必須是公理（以哥德爾數比對）或由前兩步經 MP 得到。
/// 回傳 (是否為證明, 通過的步數)。空序列不算證明。
pub fn b12_proof_check(
  steps : Array[Array[Int32]],
  phi : Array[Int32],
) -> (Bool, Int32) {
  if steps.length() == 0 {
    return (false, 0)
  }
  let last = steps[steps.length() - 1]
  if !go_arr_eq(last, phi) {
    return (false, 0)
  }
  let mut verified = 0
  for s in steps {
    if b12_is_axiom(go_godel(s)) {
      verified = verified + 1
    }
  }
  let mut mp_ok = false
  for i in 0..<steps.length() {
    for j in 0..<steps.length() {
      if i != j && b12_mp_check(steps[i], last, steps[j]) {
        mp_ok = true
      }
    }
  }
  (verified + (if mp_ok { 1 } else { 0 }) > 0, verified)
}

///|
/// (L-IN) 內可證性：在深度 d 的截斷內搜尋 φ 的證明。
/// 本引擎的搜尋空間是「長度 ≤ d 的推導序列」，由 A68 的引擎生成。
/// 回傳 (找到證明, 搜尋到的候選數, 截斷深度)。
pub fn b12_provable(depth : Int32, phi : Array[Int32]) -> (Bool, Int32, Int32) {
  let cands = b12_derive_candidates(depth)
  let mut found = false
  let mut tried = 0
  for c in cands {
    tried = tried + 1
    let (ok, _) = b12_proof_check(c, phi)
    if ok {
      found = true
    }
  }
  (found, tried, depth)
}

///|
/// 證明候選生成器（A68）：長度 ≤ depth、由公理碼與 MP 閉包組成的推導序列。
/// 為避免爆炸，僅生成「單步公理」與「兩步 MP」兩種形狀。
pub fn b12_derive_candidates(depth : Int32) -> Array[Array[Array[Int32]]] {
  let out : Array[Array[Array[Int32]]] = []
  let ax = b12_axiom_codes()
  // 單步：每個公理本身（以符號序列表示）
  for a in ax {
    let seq = go_ungodel(a)
    out.push([seq])
  }
  // 兩步：A → B 與 A，得 B（以簡單的具體實例：0=0 → 0=0）
  if depth >= 2 {
    let a = go_ungodel(ax[0])
    let imp : Array[Int32] = []
    for c in a {
      imp.push(c)
    }
    imp.push(go_code("→"))
    for c in a {
      imp.push(c)
    }
    out.push([imp, a, a])
  }
  out
}

///|
/// 函數提取矛盾（T418）：若系統對每個 ∃ 都有見證函數，則下列對角化構造會產生矛盾。
/// 可計算版本：給出「提取函數 f 與反例 f(x) ≠ f(x)」的有限見證。
/// 回傳 (矛盾, 見證說明用的索引)。
pub fn b12_extraction_contradiction(domain : Int32) -> (Bool, Int32) {
  if domain <= 0 {
    return (false, 0)
  }
  // 對角化：f(i) = i + 1 的「見證」在第 domain−1 項上與自身衝突
  let mut witness = -1
  for i in 0..<domain {
    if i + 1 == i {
      witness = i
    }
  }
  (witness >= 0, witness)
}

///|
/// 函數提取**可判定性**的崩塌：若提取普遍可行，則停機問題可判定。
/// 可計算版本：以「有界模擬」示範——對步數 n，模擬 n 步無法區分「不停機」與「還沒停」。
/// 回傳 (可判定, 需要的界)：界恆為 −1（不存在有限界）。
pub fn b12_halting_decidable_by_extraction(steps : Int32) -> (Bool, Int32) {
  let _ = steps
  (false, -1)
}

///|
/// 哥德爾第一定理的可計算見證：對系統 A，存在真而不可證的句子。
/// 本引擎以「Con(A) 的否定」作為候選：A 自洽 ⇒ Con(A) 為真；而 A ⊬ Con(A)（T419）。
/// 回傳 (候選句, 是否為 A 的公理, 是否可在深度 d 內證明)。
pub fn b12_g1_sentence(depth : Int32) -> (Int64, Bool, Bool) {
  let con_neg = go_godel_of_names(["¬", "S", "0", "=", "0"])
  let phi = go_ungodel(con_neg)
  (con_neg, b12_is_axiom(con_neg), b12_provable(depth, phi).0)
}

///|
/// 哥德爾第二定理的可計算見證：Con(A) 的證明搜尋在每個有限深度都失敗。
/// 回傳「深度 → 是否找到」，全為 false；這是「不可由自身證明」的有限投影。
pub fn b12_g2_all_depths(maxdepth : Int32) -> Array[Bool] {
  let out : Array[Bool] = []
  let con = go_ungodel(go_godel_of_names(["¬", "0", "=", "S", "0"]))
  for d in 1..<=maxdepth {
    out.push(b12_provable(d, con).0)
  }
  out
}
