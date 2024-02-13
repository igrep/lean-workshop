-- section は variable のスペースを切るための機能らしい
section useful
  variable (α β γ : Type)
  variable (g : β → γ) (f : α → β) (h : α → α)
  variable (x : α)

  def compose := g (f x)
  def doTwice := h (h x)
  def doThrice := h (h (h x))

  #check g
end useful

-- これはダメ
-- #check g

namespace useful
  variable (α β γ : Type)
  variable (g : β → γ) (f : α → β) (h : α → α)
  variable (x : α)

  def compose := g (f x)
  def doTwice := h (h x)
  def doThrice := h (h (h x))
end useful

-- これは、sectionで定義したcompose
#check compose
-- これは、もちろんusefulで定義したcompose
#check useful.compose

-- これはダメ。variable はあくまでprivateなものらしい
-- #check useful.g
