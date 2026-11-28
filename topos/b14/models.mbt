///|
/// models.mbt — 批次十四的標準有限模型（供報告與白盒測試共用）。
///
/// 全部以「有限偏序 + Alexandrov 拓撲」或「少量手寫開集族」建構，
/// 因此每個空間的開集、閉集、不可約閉集、層上同調都可精確算出。

///|
/// 兩點 Sierpiński 空間：開集 ∅、{0}、{0,1}（點 1 為一般化點）。
pub fn b14_m_sier() -> B14Top {
  b14_top(2, [0, 1, 3])
}

///|
/// 圓環模型：麥科德 S¹ 極小模型（K_{2,2} 序複形）的 Alexandrov 拓撲：4 點。
pub fn b14_m_circle() -> B14Top {
  b14_top(4, b14_alex_opens(4, b14_circle_poset()))
}

///|
/// 鏈 0 < 1 < 2 的 Alexandrov 拓撲：3 點。
pub fn b14_m_chain3() -> B14Top {
  b14_top(3, b14_alex_opens(3, b14_chain(3)))
}
