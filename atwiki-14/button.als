enum Type {Normal, Over, Press}
sig Button {
  type: Type,
  width: Int,
  height: Int
}

{
  width >= 0 && height >= 0
}

pred show {}
//run show

// マウスがボタン上にあるのかを述語としてまとめている
pred on_button(x: Int, y: Int, b: Button) {
  x >= 0 && x < b.width
  y >= 0 && y < b.height
}


pred mouse_move(x: Int, y: Int, b: Button, b': Button) {
  // ボタン上にカーソルがないときは、ボタンはNormal状態
  !on_button[x, y, b] => b'.type = Normal
  // ボタン上にカーソルが来たら、Press状態であれば、Pressのまま
  // Press状態でなければOverにする
  on_button[x, y, b] => {
		b.type = Press => b'.type = b.type
		b.type != Press => b'.type = Over
	}
  b'.width = b.width
  b'.height = b.height
}

run mouse_move

// mouse_moveと同様に書く
pred mouse_pressL (x : Int, y : Int, b : Button, b' : Button) {
on_button[x, y, b] => b'.type = Press
! on_button[x, y, b] => b'.type = Normal

b'.width = b.width
b'.height = b.height
}

// mouse_moveと同様に書く
pred mouse_releaseL (x : Int, y : Int, b : Button, b' : Button) {
	on_button[x, y, b] => b'.type = Over
	! on_button[x, y, b] => b'.type = Normal

	b'.width = b.width
	b'.height = b.height
}
