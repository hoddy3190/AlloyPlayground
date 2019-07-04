
sig Name, Addr {}
sig Book {
    addr: Name -> lone Addr
}


pred show(b: Book) {
    #b.addr > 1
    #Name.(b.addr) = 2  // すべてのNameの要素が使っているアドレス要素の合計が2であること
                                 // すべてのNameの要素が使っている関係addrの合計数が2ではないことに注意
}


run show for 3 but 1 Book  // Book以外のシグネチャは高々3つのオブジェクトに限定し、Bookは1つのオブジェクトに限定する
